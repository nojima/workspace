from logging import getLogger, StreamHandler, DEBUG
from typing import Tuple, Iterator, Dict

import chainer.functions as F
import chainer.links as L
import numpy as np
from chainer import Variable, optimizers, serializers, Chain
from chainer.utils import walker_alias
from scipy.spatial.distance import cosine
from sklearn.manifold import TSNE
from sklearn.decomposition import PCA
import matplotlib.pyplot as plt


logger = getLogger(__name__)
handler = StreamHandler()
handler.setLevel(DEBUG)
logger.setLevel(DEBUG)
logger.addHandler(handler)
logger.propagate = False


class Vocabulary:
    def __init__(self):
        self._word2id = {}  # type: Dict[str, int]
        self._id2word = {}  # type: Dict[int, str]

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
    def __init__(self, filename: str, vocabulary: Vocabulary = None) -> None:
        self._vocabulary = vocabulary or Vocabulary()

        data = []
        with open(filename) as f:
            for line in f:
                for word in line.split():
                    id = self._vocabulary.intern(word)
                    data.append(id)

        self._data = np.array(data, dtype=np.int32)

    @property
    def size(self) -> int:
        return len(self._data)

    @property
    def vocabulary(self) -> Vocabulary:
        return self._vocabulary

    @property
    def data(self) -> np.ndarray:
        return self._data

    def make_sampler(self) -> walker_alias.WalkerAlias:
        _, counts = np.unique(self._data, return_counts=True)
        counts = np.power(counts, 0.75)
        return walker_alias.WalkerAlias(counts)


class Word2Vec(Chain):
    def __init__(self, n_vocabulary: int, n_units: int) -> None:
        super().__init__()
        with self.init_scope():
            self._embed_input = L.EmbedID(n_vocabulary, n_units)
            self._embed_output = L.EmbedID(n_vocabulary, n_units)

    def __call__(self, x1: Variable, x2: Variable, t: Variable) -> Variable:
        output = self.forward(x1, x2)
        return F.sigmoid_cross_entropy(output, t)

    def forward(self, x1: Variable, x2: Variable) -> Variable:
        h1 = self._embed_input(x1)
        h2 = self._embed_output(x2)
        return F.sum(h1 * h2, axis=1)

    def distributed_representation(self, word_id: np.ndarray) -> np.ndarray:
        return self._embed_input(Variable(word_id)).data


class Word2VecOneW(Chain):
    def __init__(self, n_vocabulary: int, n_units: int) -> None:
        super().__init__()
        with self.init_scope():
            self._embed = L.EmbedID(n_vocabulary, n_units)

    def __call__(self, x1: Variable, x2: Variable, t: Variable) -> Variable:
        output = self.forward(x1, x2)
        return F.sigmoid_cross_entropy(output, t)

    def forward(self, x1: Variable, x2: Variable) -> Variable:
        h1 = self._embed(x1)
        h2 = self._embed(x2)
        return F.sum(h1 * h2, axis=1)

    def distributed_representation(self, word_id: np.ndarray) -> np.ndarray:
        return self._embed(Variable(word_id)).data


def train(dataset: DataSet, n_epoch: int = 10, batch_size: int = 100) -> Iterator[Tuple[Word2Vec, int]]:
    n_units = 100
    model = Word2Vec(dataset.vocabulary.size, n_units)

    optimizer = optimizers.Adam()
    optimizer.setup(model)

    sampler = dataset.make_sampler()
    window_size = 5
    n_negative_samples = 5

    def make_batch_set(indices: np.ndarray) -> Tuple[Variable, Variable, Variable]:
        x1, x2, t = [], [], []

        for index in indices:
            id1 = dataset.data[index]

            for i in range(-window_size, window_size+1):
                p = index + i
                if i == 0 or p < 0 or p >= dataset.size:
                    continue
                id2 = dataset.data[p]
                x1.append(id1)
                x2.append(id2)
                t.append(1)
                for nid in sampler.sample(n_negative_samples):
                    x1.append(id1)
                    x2.append(nid)
                    t.append(0)

        return (Variable(np.array(x1, dtype=np.int32)),
                Variable(np.array(x2, dtype=np.int32)),
                Variable(np.array(t,  dtype=np.int32)))

    for epoch in range(n_epoch):
        logger.info("epoch: {}".format(epoch))
        indices = np.random.permutation(dataset.size)

        for i in range(0, dataset.size, batch_size):
            logger.info("-- {}, {}".format(epoch, i))
            model.cleargrads()

            x1, x2, t = make_batch_set(indices[i:i+batch_size])
            loss = model(x1, x2, t)
            loss.backward()
            optimizer.update()

        yield model, epoch


class Search:
    def __init__(self, vocabulary: Vocabulary, model: Word2Vec):
        word_ids = np.arange(0, vocabulary.size, dtype=np.int32)
        self._vocabulary = vocabulary
        self._vectors = model.distributed_representation(word_ids)

    def find_similar_words(self, word: str, n: int = 10):
        return self.find_similar_words_by_vector(self.get_vector(word), n)

    def find_similar_words_by_vector(self, vector: np.ndarray, n: int = 10):
        vocabulary = self._vocabulary
        similar_ids = sorted(range(0, vocabulary.size),
                             key=lambda id: cosine(self._vectors[id], vector))[:n]
        return [vocabulary.to_word(id) for id in similar_ids]

    def get_vector(self, word: str):
        id = self._vocabulary.to_id(word)
        return self._vectors[id]


def save_model(dir_name: str, model: Word2Vec, epoch: int) -> None:
    filename = "{}/w2v_model_epoch{}.npz".format(dir_name, epoch)
    serializers.save_npz(filename, model)


def load_model(filename: str, vocabulary: Vocabulary, model_class: type = Word2Vec) -> Word2Vec:
    n_units = 100   # TODO
    model = model_class(vocabulary.size, n_units)
    serializers.load_npz(filename, model)
    return model


def project_to_2d_by_tsne(vocabulary: Vocabulary, model: Word2Vec, perplexity: int = 25):
    word_ids = np.arange(0, vocabulary.size, dtype=np.int32)
    vectors = model.distributed_representation(word_ids)

    tsne = TSNE(n_components=2, verbose=3, perplexity=perplexity, random_state=12345)
    return tsne.fit_transform(vectors)


def project_to_2d_by_pca(vocabulary: Vocabulary, model: Word2Vec):
    word_ids = np.arange(0, vocabulary.size, dtype=np.int32)
    vectors = model.distributed_representation(word_ids)

    pca = PCA(n_components=2)
    return pca.fit_transform(vectors)


def visualize(vocabulary: Vocabulary, vectors_2d: np.ndarray, ax: plt.Axes = None):
    countries = ['u.s.', 'u.k.', 'italy', 'korea', 'china', 'germany', 'japan', 'france', 'russia', 'egypt']
    capitals = ['washington', 'london', 'rome', 'seoul', 'beijing', 'berlin', 'tokyo', 'paris', 'moscow', 'cairo']
    mask = [vocabulary.to_id(word) for word in countries + capitals]

    if ax is None:
        fig, ax = plt.subplots()
    else:
        fig = None

    target_vectors = vectors_2d[mask]
    ax.scatter(target_vectors[:, 0], target_vectors[:, 1])
    for i, label in enumerate(countries + capitals):
        ax.annotate(label, (target_vectors[i, 0], target_vectors[i, 1]))
    for country, capital in zip(countries, capitals):
        v1 = vectors_2d[vocabulary.to_id(country)]
        v2 = vectors_2d[vocabulary.to_id(capital)]
        ax.arrow(v1[0], v1[1], (v2 - v1)[0], (v2 - v1)[1])

    if fig is not None:
        fig.show()


def run(seed: int = 12345) -> None:
    np.random.seed(seed)

    dataset = DataSet("ptb.train.txt")
    for model, epoch in train(dataset, n_epoch=50):
        save_model("./models/v3", model, epoch)
