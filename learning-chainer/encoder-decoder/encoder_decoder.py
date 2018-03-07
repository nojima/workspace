import numpy as np
from chainer import Chain, links as L, Variable, functions as F
from chainer import optimizers, Variable, serializers
import chainer
from typing import List, Tuple, Dict
import pickle
from logging import getLogger, StreamHandler, DEBUG
import multiprocessing
import collections
import glob


logger = getLogger(__name__)
handler = StreamHandler()
handler.setLevel(DEBUG)
logger.setLevel(DEBUG)
logger.addHandler(handler)
logger.propagate = False


EOS = 0
UNK = 1


class Vocabulary:
    def __init__(self):
        self._word2id = {}  # type: Dict[str, int]
        self._id2word = {}  # type: Dict[int, str]
        self.intern("<EOS>")
        self.intern("<UNK>")

    def intern(self, word: str) -> int:
        if word not in self._word2id:
            id = len(self._word2id)
            self._word2id[word] = id
            self._id2word[id] = word
        return self._word2id[word]

    def to_word(self, id: int) -> str:
        return self._id2word[id]

    def to_id(self, word: str) -> int:
        return self._word2id[word]

    @property
    def size(self):
        return len(self._word2id)


class DataSet:
    @staticmethod
    def load(filename: str, ja_vocab: Vocabulary, en_vocab: Vocabulary) -> "DataSet":
        ja_sentences = []
        en_sentences = []

        with open(filename, "rb") as f:
            for translation in pickle.load(f):
                ja = translation["ja"]
                ja_words = [ja_vocab.intern(w) for w in ja]
                ja_sentences.append(np.array(ja_words, dtype=np.int32))

                en = translation["en"]
                en_words = [en_vocab.intern(w) for w in en]
                en_sentences.append(np.array(en_words, dtype=np.int32))

        return DataSet(ja_sentences, ja_vocab, en_sentences, en_vocab)

    def __init__(self,
                 ja_sentences: List[np.ndarray], ja_vocab: Vocabulary,
                 en_sentences: List[np.ndarray], en_vocab: Vocabulary) -> None:
        self._ja_sentences = ja_sentences
        self._ja_vocabulary = ja_vocab
        self._en_sentences = en_sentences
        self._en_vocabulary = en_vocab

    @property
    def n_sentences(self) -> int:
        return len(self._ja_sentences)

    @property
    def ja_vocabulary(self) -> Vocabulary:
        return self._ja_vocabulary

    @property
    def ja_sentences(self) -> List[np.ndarray]:
        return self._ja_sentences

    @property
    def en_vocabulary(self) -> Vocabulary:
        return self._en_vocabulary

    @property
    def en_sentences(self) -> List[np.ndarray]:
        return self._en_sentences

    def split(self, ratio: float):
        n = int(self.n_sentences * ratio)
        np.random.seed(12345)
        shuffled = np.random.permutation(self.n_sentences)
        return (DataSet([self.ja_sentences[i] for i in shuffled[:n]],
                        self.ja_vocabulary,
                        [self.en_sentences[i] for i in shuffled[:n]],
                        self.en_vocabulary),
                DataSet([self.ja_sentences[i] for i in shuffled[n:]],
                        self.ja_vocabulary,
                        [self.en_sentences[i] for i in shuffled[n:]],
                        self.en_vocabulary))


class EncoderDecoder(Chain):
    def __init__(self, input_dimension: int, output_dimension: int, hidden_dimension: int, attention: bool = False):
        super().__init__()
        with super().init_scope():
            self._embed_input = L.EmbedID(input_dimension, hidden_dimension)
            self._embed_output = L.EmbedID(output_dimension, hidden_dimension)

            self._encoder = L.NStepLSTM(
                n_layers=1,
                in_size=hidden_dimension,
                out_size=hidden_dimension,
                dropout=0.1)
            self._decoder = L.NStepLSTM(
                n_layers=1,
                in_size=hidden_dimension,
                out_size=hidden_dimension,
                dropout=0.1)

            # Embed の逆を行う行列を表す良い名前がほしい。
            self._extract_output = L.Linear(hidden_dimension, output_dimension)

            self._use_attention = attention
            if attention:
                self._attention_layer = L.Linear(2 * hidden_dimension, hidden_dimension)
            else:
                self._attention_layer = None

        self._hyper_params = (input_dimension, output_dimension, hidden_dimension, attention)

    @property
    def hyper_params(self) -> tuple:
        return self._hyper_params

    def __call__(self, xs: List[Variable], ys: List[Variable]) -> Variable:
        batch_size = len(xs)
        xs = [x[::-1] for x in xs]

        eos = np.array([EOS], dtype=np.int32)
        ys_in = [F.concat((eos, y), axis=0) for y in ys]
        ys_out = [F.concat((y, eos), axis=0) for y in ys]

        embedded_xs = [self._embed_input(x) for x in xs]
        embedded_ys = [self._embed_output(y) for y in ys_in]

        hidden_states, cell_states, attentions = self._encoder(None, None, embedded_xs)
        _, _, embedded_outputs = self._decoder(hidden_states, cell_states, embedded_ys)

        loss = 0
        for embedded_output, y, attention in zip(embedded_outputs, ys_out, attentions):
            if self._use_attention:
                output = self._calculate_attention_layer_output(embedded_output, attention)
            else:
                output = self._extract_output(embedded_output)
            loss += F.softmax_cross_entropy(output, y)
        loss /= batch_size

        return loss

    def _calculate_attention_layer_output(self, embedded_output: Variable, attention: Variable) -> Variable:
        inner_prod = F.matmul(embedded_output, attention, transb=True)
        weights = F.softmax(inner_prod)
        contexts = F.matmul(weights, attention)
        concatenated = F.concat((contexts, embedded_output))
        new_embedded_output = F.tanh(self._attention_layer(concatenated))
        return self._extract_output(new_embedded_output)

    def _translate_one_word(self, wid: int, hidden_states, cell_states, attentions):
        y = np.array([wid], dtype=np.int32)
        embedded_y = self._embed_output(y)
        hidden_states, cell_states, embedded_outputs = \
            self._decoder(hidden_states, cell_states, [embedded_y])

        if self._use_attention:
            output = self._calculate_attention_layer_output(embedded_outputs[0], attentions[0])
        else:
            output = self._extract_output(embedded_outputs[0])

        output = F.softmax(output)

        return output[0], hidden_states, cell_states

    def translate(self, sentence: np.ndarray, max_length: int = 30) -> List[int]:
        with chainer.no_backprop_mode(), chainer.using_config('train', False):
            sentence = sentence[::-1]

            embedded_xs = self._embed_input(sentence)
            hidden_states, cell_states, attentions = self._encoder(None, None, [embedded_xs])

            wid = EOS
            result = []

            for i in range(max_length):
                output, hidden_states, cell_states = \
                    self._translate_one_word(wid, hidden_states, cell_states, attentions)

                wid = np.argmax(output.data)
                if wid == EOS:
                    break
                result.append(wid)

            return result

    def translate_with_beam_search(self, sentence: np.ndarray, max_length: int = 30, beam_width=3) -> List[int]:
        with chainer.no_backprop_mode(), chainer.using_config('train', False):
            sentence = sentence[::-1]

            embedded_xs = self._embed_input(sentence)
            hidden_states, cell_states, attentions = self._encoder(None, None, [embedded_xs])

            heaps = [[] for _ in range(max_length + 1)]
            heaps[0].append((0, [EOS], hidden_states, cell_states))  # (score, translation, hidden_states, cell_states)

            solution = []
            solution_score = 1e8

            for i in range(max_length):
                heaps[i] = sorted(heaps[i], key=lambda t: t[0])[:beam_width]

                for score, translation, i_hidden_states, i_cell_states in heaps[i]:
                    wid = translation[-1]
                    output, new_hidden_states, new_cell_states = \
                        self._translate_one_word(wid, i_hidden_states, i_cell_states, attentions)

                    for next_wid in np.argsort(output.data)[::-1]:
                        if output.data[next_wid] < 1e-6:
                            break
                        next_score = score - np.log(output.data[next_wid])
                        if next_score > solution_score:
                            break
                        next_translation = translation + [next_wid]
                        next_item = (next_score, next_translation, new_hidden_states, new_cell_states)

                        if next_wid == EOS:
                            if next_score < solution_score:
                                solution = translation[1:]  # [1:] drops first EOS
                                solution_score = next_score
                        else:
                            heaps[i + 1].append(next_item)

            return solution


def train(dataset: DataSet, n_epoch: int = 20, attention: bool = False):
    model = EncoderDecoder(
        input_dimension=dataset.ja_vocabulary.size,
        output_dimension=dataset.en_vocabulary.size,
        hidden_dimension=512,
        attention=attention)

    optimizer = optimizers.Adam()
    optimizer.setup(model)

    batch_size = 128

    for epoch in range(n_epoch):
        shuffled = np.random.permutation(dataset.n_sentences)

        for i in range(0, dataset.n_sentences, batch_size):
            logger.info("Epoch {}: Mini-Batch {}".format(epoch, i))

            indices = shuffled[i:i+batch_size]
            xs = [Variable(dataset.ja_sentences[j]) for j in indices]
            ys = [Variable(dataset.en_sentences[j]) for j in indices]

            model.cleargrads()
            loss = model(xs, ys)
            loss.backward()
            optimizer.update()

        yield model, epoch


def save_model(filename: str, model: EncoderDecoder) -> None:
    serializer = serializers.DictionarySerializer()

    pickled_params = np.frombuffer(pickle.dumps(model.hyper_params), dtype=np.uint8)
    serializer("hyper_parameters", pickled_params)

    serializer["model"].save(model)

    np.savez_compressed(filename, **serializer.target)


def load_model(filename: str) -> EncoderDecoder:
    with np.load(filename) as f:
        d = dict(f.iteritems())

        # 後方互換性のために _W を _extract_output に改名する
        for k, v in list(d.items()):
            old_prefix = "model/_W/"
            new_prefix = "model/_extract_output/"
            if k.startswith(old_prefix):
                d[new_prefix + k[len(old_prefix):]] = v

        deserializer = serializers.NpzDeserializer(d)

        pickled_params = deserializer("hyper_parameters", None)
        params = pickle.loads(pickled_params.tobytes())

        model = EncoderDecoder(*params)
        deserializer["model"].load(model)

        return model


def run():
    dataset = DataSet.load("./corpus/tatoeba/jpen.pickle", Vocabulary(), Vocabulary())
    training_set, test_set = dataset.split(0.8)
    for model, epoch in train(training_set, attention=True):
        save_model("./models/ed-at-s08-d512-epoch{}.npz".format(epoch), model)


def split_dataset(dataset: DataSet, ratio: float = 0.8) -> Tuple[DataSet, DataSet]:
    training_set, test_set = dataset.split(ratio)

    # test_set から日本語文が training_set に含まれるものを取り除く
    training_ja_sentences = set(tuple(s) for s in training_set.ja_sentences)
    deduplicated_ja = []
    deduplicated_en = []
    for ja, en in zip(test_set.ja_sentences, test_set.en_sentences):
        if tuple(ja) not in training_ja_sentences:
            deduplicated_ja.append(ja)
            deduplicated_en.append(en)

    new_test_set = DataSet(deduplicated_ja, test_set.ja_vocabulary,
                           deduplicated_en, test_set.en_vocabulary)
    return training_set, new_test_set


def translate_it(model: EncoderDecoder, dataset: DataSet, index: int):
    jv = dataset.ja_vocabulary
    ev = dataset.en_vocabulary
    print("    JA:", " ".join(jv.to_word(i) for i in dataset.ja_sentences[index]))
    print("    EN:", " ".join(ev.to_word(i) for i in dataset.en_sentences[index]))
    print("Output:", " ".join(ev.to_word(i) for i in model.translate_with_beam_search(dataset.ja_sentences[index])))


def translate_it2(model: EncoderDecoder, dataset: DataSet, index: int):
    jv = dataset.ja_vocabulary
    ev = dataset.en_vocabulary
    print("    JA:", " ".join(jv.to_word(i) for i in dataset.ja_sentences[index]))
    print("    EN:", " ".join(ev.to_word(i) for i in dataset.en_sentences[index]))
    print("Output:", " ".join(ev.to_word(i) for i in model.translate(dataset.ja_sentences[index])))


def translate_it3(models: Dict[str, EncoderDecoder], dataset: DataSet, index: int):
    max_name_len = max(len(name) for name in models)

    jv = dataset.ja_vocabulary
    ev = dataset.en_vocabulary

    print("{}:".format("JA".rjust(max_name_len)),
          " ".join(jv.to_word(i) for i in dataset.ja_sentences[index]))
    print("{}:".format("EN".rjust(max_name_len)),
          " ".join(ev.to_word(i) for i in dataset.en_sentences[index]))

    for name, model in models:
        print("{}:".format(name.rjust(max_name_len)),
              " ".join(ev.to_word(i) for i in model.translate(dataset.ja_sentences[index])))


def translate_all(model: EncoderDecoder, dataset: DataSet, use_beam_search: bool):
    result = []
    for i in range(dataset.n_sentences):
        if i % 100 == 0:
            logger.info("Translating {}".format(i))
        if use_beam_search:
            output = model.translate_with_beam_search(dataset.ja_sentences[i])
        else:
            output = model.translate(dataset.ja_sentences[i])
        result.append(output)
    return result


def show_translations(translations: Dict[str, List[List[int]]], dataset: DataSet, index: int):
    max_name_len = max(len(name) for name in translations)

    jv = dataset.ja_vocabulary
    ev = dataset.en_vocabulary

    print("{}: ----- :".format("JA".ljust(max_name_len)),
          " ".join(jv.to_word(i) for i in dataset.ja_sentences[index]))
    print("{}: ----- :".format("EN".ljust(max_name_len)),
          " ".join(ev.to_word(i) for i in dataset.en_sentences[index]))

    for name, outputs in translations.items():
        bleu = calculate_bleu(dataset.en_sentences[index], outputs[index])
        print("{}:".format(name.ljust(max_name_len)),
              "{:.3f} :".format(bleu),
              " ".join(ev.to_word(i) for i in outputs[index]))


def run_single(model_prefix, test_set, epoch, use_beam_search):
    logger.info("epoch {}, use_beam_search {}".format(epoch, use_beam_search))

    model = load_model("./models/{}-epoch{}.npz".format(model_prefix, epoch))
    result = translate_all(model, test_set, use_beam_search)

    b = "-b3" if use_beam_search else ""
    with open("./results/{}{}-epoch{}.pickle".format(model_prefix, b, epoch), "wb") as f:
        pickle.dump(result, f)


def run2():
    dataset = DataSet.load("./corpus/tatoeba/jpen.pickle", Vocabulary(), Vocabulary())
    _, test_set = dataset.split(0.8)

    model_prefix = "ed-s08-d512"

    with multiprocessing.Pool(processes=6) as pool:
        for epoch in [19, 3, 7]:
            for use_beam_search in [False, True]:
                pool.apply_async(run_single, args=(model_prefix, test_set, epoch, use_beam_search))
        pool.close()
        pool.join()


def n_gram(sentence, n):
    result = []
    for i in range(len(sentence) - n + 1):
        result.append(sentence[i:i+n])
    return result


def calculate_bleu(reference, output, max_n=4):
    if len(output) == 0:
        return 0.0

    precision_score = 1.0

    for n in range(1, max_n + 1):
        reference_ngram = n_gram(reference, n)

        counts = collections.defaultdict(int)
        for words in reference_ngram:
            counts[tuple(words)] += 1

        ok = 0
        total = 0
        for output_ngram in n_gram(output, n):
            t = tuple(output_ngram)
            if t in counts and counts[t] > 0:
                ok += 1
                counts[t] -= 1
            total += 1

        if total > 0:
            precision_score *= ok / total
        else:
            precision_score *= 0.0

    precision_score = np.power(precision_score, 1.0 / max_n)
    length_penalty = min(1.0, np.exp(1 - len(reference) / len(output)))

    return length_penalty * precision_score


def calculate_average_bleu(references, outputs, max_n=4):
    assert len(references) == len(outputs)
    result = 0.0
    for i, (reference, output) in enumerate(zip(references, outputs)):
        if i % 100 == 0:
            logger.info("Calculating {}...".format(i))
        result += calculate_bleu(reference, output, max_n)
    return result / len(references)


# 間違えて dedup 前の test_set で translations を計算してしまったので、それの修正用
def dedup_outputs(training_set, test_set, outputs) -> Tuple[DataSet, DataSet]:
    # test_set から日本語文が training_set に含まれるものを取り除く
    training_ja_sentences = set(tuple(s) for s in training_set.ja_sentences)

    new_outputs = []
    for ja, en, output in zip(test_set.ja_sentences, test_set.en_sentences, outputs):
        if tuple(ja) not in training_ja_sentences:
            new_outputs.append(output)

    return new_outputs


def run_bleu(max_n: int = 4):
    dataset = DataSet.load("./corpus/tatoeba/jpen.pickle", Vocabulary(), Vocabulary())

    no_dedup_training_set, no_dedup_test_set = dataset.split(0.8)
    training_set, test_set = split_dataset(dataset)

    r = {}
    for filename in glob.glob("./results/*.pickle"):
        with open(filename, "rb") as f:
            outputs = pickle.load(f)
        new_outputs = dedup_outputs(no_dedup_training_set, no_dedup_test_set, outputs)
        bleu = calculate_average_bleu(test_set.en_sentences, new_outputs, max_n)
        r[filename] = bleu

    return r
