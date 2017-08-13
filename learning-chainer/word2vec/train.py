import pickle
from collections import namedtuple
from logging import getLogger, StreamHandler, DEBUG
from typing import Iterator, Tuple

import numpy as np
from chainer import optimizers, Variable, serializers
from chainer.utils import walker_alias

from word2vec.dataset import DataSet
from word2vec.models import Word2Vec

logger = getLogger(__name__)
handler = StreamHandler()
handler.setLevel(DEBUG)
logger.setLevel(DEBUG)
logger.addHandler(handler)
logger.propagate = False


HyperParameters = namedtuple('HyperParameters', [
    'model_class',          # 利用するモデル (クラス)
    'vocabulary_size',      # 語彙数
    'vector_dimension',     # 分散表現ベクトルの次元
    'window_size',          # ウィンドウの半径
    'n_negative_samples',   # １単語につきネガティブサンプルする単語の数
    'batch_size',           # １回のミニバッチで処理する単語数
    'n_epoch',              # 総エポック数
])


def _make_model(params: HyperParameters) -> Word2Vec:
    return params.model_class(params.vocabulary_size, params.vector_dimension)


def _make_sampler(dataset: DataSet) -> walker_alias.WalkerAlias:
    _, counts = np.unique(dataset.data, return_counts=True)
    counts = np.power(counts, 0.75)
    return walker_alias.WalkerAlias(counts)


def _make_batch_set(
        indices: np.ndarray,
        sampler: walker_alias.WalkerAlias,
        dataset: DataSet,
        params: HyperParameters) -> Tuple[Variable, Variable, Variable]:

    window_size = params.window_size
    n_negative_samples = params.n_negative_samples

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


def train(dataset: DataSet, params: HyperParameters) -> Iterator[Tuple[Word2Vec, int]]:
    assert dataset.vocabulary.size <= params.vocabulary_size

    model = _make_model(params)

    optimizer = optimizers.Adam()
    optimizer.setup(model)

    sampler = _make_sampler(dataset)

    batch_size = params.batch_size
    n_epoch = params.n_epoch

    for epoch in range(n_epoch):
        logger.info("epoch: {}".format(epoch))
        indices = np.random.permutation(dataset.size)

        for i in range(0, dataset.size, batch_size):
            logger.info("-- {}, {}".format(epoch, i))
            model.cleargrads()

            x1, x2, t = _make_batch_set(indices[i:i+batch_size], sampler, dataset, params)
            loss = model(x1, x2, t)
            loss.backward()
            optimizer.update()

        yield model, epoch


def save_model(filename: str, model: Word2Vec, params: HyperParameters) -> None:
    serializer = serializers.DictionarySerializer()

    pickled_params = np.frombuffer(pickle.dumps(params), dtype=np.uint8)
    serializer("hyper_parameters", pickled_params)

    serializer["model"].save(model)

    np.savez_compressed(filename, **serializer.target)


def load_model(filename: str) -> Tuple[Word2Vec, HyperParameters]:
    with np.load(filename) as f:
        deserializer = serializers.NpzDeserializer(f)

        pickled_params = deserializer("hyper_parameters", None)
        params = pickle.loads(pickled_params.tobytes())  # type: HyperParameters

        model = _make_model(params)
        deserializer["model"].load(model)

        return model, params
