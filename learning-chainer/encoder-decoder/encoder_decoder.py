import numpy as np
from chainer import Chain, links as L, Variable, functions as F
from chainer import optimizers, Variable, serializers
import chainer
from typing import List
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
    def __init__(self, input_dimension: int, output_dimension: int, hidden_dimension: int):
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
            self._W = L.Linear(hidden_dimension, output_dimension)

        self._hyper_params = (input_dimension, output_dimension, hidden_dimension)

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

        hidden_states, cell_states, _ = self._encoder(None, None, embedded_xs)
        _, _, outputs = self._decoder(hidden_states, cell_states, embedded_ys)

        loss = 0
        for actual, expected in zip(outputs, ys_out):
            loss += F.softmax_cross_entropy(self._W(actual), expected)
        loss /= batch_size

        return loss

    def translate(self, sentence: np.ndarray, max_length: int = 30):
        with chainer.no_backprop_mode(), chainer.using_config('train', False):
            sentence = sentence[::-1]

            embedded_xs = self._embed_input(sentence)
            hidden_states, cell_states, _ = self._encoder(None, None, [embedded_xs])

            y = np.array([EOS], dtype=np.int32)
            result = []
            for i in range(max_length):
                embedded_y = self._embed_output(y)
                hidden_states, cell_states, outputs = self._decoder(hidden_states, cell_states, [embedded_y])
                output = self._W(outputs[0])
                wid = np.argmax(output.data)
                if wid == EOS:
                    break
                result.append(wid)
                y = np.array([wid], dtype=np.int32)

            return result


def train(dataset: DataSet, n_epoch: int = 20):
    model = EncoderDecoder(
        input_dimension=dataset.ja_vocabulary.size,
        output_dimension=dataset.en_vocabulary.size,
        hidden_dimension=512)

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
    for model, epoch in train(training_set):
        save_model("./models/ed-s08-d512-epoch{}.npz".format(epoch), model)
