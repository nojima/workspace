from logging import getLogger, StreamHandler, DEBUG
from typing import Iterator, Tuple

import numpy as np
from chainer import optimizers, Variable
from chainer.utils import walker_alias

from word2vec.dataset import DataSet
from word2vec.models import DoubleMatrixWord2Vec


logger = getLogger(__name__)
handler = StreamHandler()
handler.setLevel(DEBUG)
logger.setLevel(DEBUG)
logger.addHandler(handler)
logger.propagate = False


def _make_sampler(dataset: DataSet) -> walker_alias.WalkerAlias:
    _, counts = np.unique(dataset.data, return_counts=True)
    counts = np.power(counts, 0.75)
    return walker_alias.WalkerAlias(counts)


def train(dataset: DataSet, n_epoch: int = 10, batch_size: int = 100) -> Iterator[Tuple[DoubleMatrixWord2Vec, int]]:
    n_units = 100
    model = DoubleMatrixWord2Vec(dataset.vocabulary.size, n_units)

    optimizer = optimizers.Adam()
    optimizer.setup(model)

    sampler = _make_sampler()
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
