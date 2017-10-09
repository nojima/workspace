import numpy as np
from chainer import Chain, links as L, Variable, functions as F
from chainer import optimizers, Variable, serializers
import chainer
from typing import List, Tuple
import pickle
from logging import getLogger, StreamHandler, DEBUG


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

    def translate(self, sentence: np.ndarray, max_length: int = 30):
        with chainer.no_backprop_mode(), chainer.using_config('train', False):
            sentence = sentence[::-1]

            embedded_xs = self._embed_input(sentence)
            hidden_states, cell_states, attentions = self._encoder(None, None, [embedded_xs])

            y = np.array([EOS], dtype=np.int32)
            result = []
            for i in range(max_length):
                embedded_y = self._embed_output(y)
                hidden_states, cell_states, embedded_outputs = \
                    self._decoder(hidden_states, cell_states, [embedded_y])

                if self._use_attention:
                    output = self._calculate_attention_layer_output(embedded_outputs[0], attentions[0])
                else:
                    output = self._extract_output(embedded_outputs[0])

                wid = np.argmax(output.data)
                if wid == EOS:
                    break
                result.append(wid)
                y = np.array([wid], dtype=np.int32)

            return result


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
        deserializer = serializers.NpzDeserializer(f)

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
    print("Output:", " ".join(ev.to_word(i) for i in model.translate(dataset.ja_sentences[index])))
