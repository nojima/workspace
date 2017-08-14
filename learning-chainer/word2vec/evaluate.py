import chainer
from chainer import Variable
from chainer.utils import walker_alias

import numpy as np

from word2vec.train import HyperParameters
from word2vec.dataset import DataSet
from word2vec.models import Word2Vec


def _make_sampler(dataset: DataSet) -> walker_alias.WalkerAlias:
    _, counts = np.unique(dataset.data, return_counts=True)
    counts = np.power(counts, 0.75)
    return walker_alias.WalkerAlias(counts)


def _calculate_loss(model: Word2Vec, x1: np.ndarray, x2: np.ndarray, t: np.ndarray) -> float:
    with chainer.no_backprop_mode():
        loss = model(Variable(x1), Variable(x2), Variable(t))
        return np.sum(loss.data)


def evaluate(model: Word2Vec, params: HyperParameters, test_set: DataSet) -> float:
    sampler = _make_sampler(test_set)

    window_size = params.window_size

    # positive
    positive_x1 = []
    positive_x2 = []
    n_positives = 0
    for index in range(window_size, test_set.size - window_size):
        id1 = test_set.data[index]
        for i in range(-window_size, window_size+1):
            p = index + i
            id2 = test_set.data[p]
            positive_x1.append(id1)
            positive_x2.append(id2)
            n_positives += 1

    # negative
    negative_x1 = []
    n_negatives = 0
    for index in range(window_size, test_set.size - window_size):
        id1 = test_set.data[index]
        for i in range(-window_size, window_size + 1):
            p = index + i
            negative_x1.append(id1)
            n_negatives += 1
    negative_x2 = sampler.sample(n_negatives)

    # concat positives and negatives
    x1 = np.concatenate((np.array(positive_x1, dtype=np.int32), np.array(negative_x1, dtype=np.int32)))
    x2 = np.concatenate((np.array(positive_x2, dtype=np.int32), negative_x2))
    t = np.concatenate((np.ones(n_positives, dtype=np.int32), np.zeros(n_negatives, dtype=np.int32)))

    return _calculate_loss(model, x1, x2, t)
