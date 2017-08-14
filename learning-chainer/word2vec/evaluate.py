from chainer.utils import walker_alias

import numpy as np
from scipy.special import expit

from word2vec import HyperParameters
from word2vec.dataset import DataSet
from word2vec.models import Word2Vec


def _make_sampler(dataset: DataSet) -> walker_alias.WalkerAlias:
    _, counts = np.unique(dataset.data, return_counts=True)
    counts = np.power(counts, 0.75)
    return walker_alias.WalkerAlias(counts)


def _log_likelihood(model: Word2Vec, x1: np.ndarray, x2: np.ndarray, t: np.ndarray) -> float:
    v1 = model.distributed_representation(x1)
    v2 = model.distributed_representation(x2)

    p = expit(np.sum(v1 * v2, axis=1))

    # discard extreme values
    mask = np.logical_and(0.0001 < p, p < 0.9999)
    p = p[mask]
    t = t[mask]

    return np.sum(t * np.log(p) + (1 - t) * np.log(1 - p))


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
    t = np.concatenate((np.ones(n_positives), np.zeros(n_negatives)))

    return -_log_likelihood(model, x1, x2, t)
