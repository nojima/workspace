from datetime import datetime
from os.path import join

import numpy as np
from scipy.spatial.distance import cosine

from word2vec.dataset import DataSet, Vocabulary
from word2vec.models import DoubleMatrixWord2Vec
from word2vec.train import train, save_model, HyperParameters


class Search:
    def __init__(self, vocabulary: Vocabulary, model: DoubleMatrixWord2Vec):
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


def make_base_name(params: HyperParameters):
    name = "word2vec"

    # Add model name
    name += "_" + params.model_class.__name__.replace("Word2Vec", "").lower()

    # Add vector_dimension
    name += "_vd{}".format(params.vector_dimension)

    # Add window_size
    name += "_w{}".format(params.window_size)

    # Add n_negative_samples
    name += "_ns{}".format(params.n_negative_samples)

    # Add batch_size
    name += "_bs{}".format(params.batch_size)

    return name


def run(seed: int = 12345) -> None:
    np.random.seed(seed)

    dataset = DataSet("./word2vec/ptb.train.txt")
    params = HyperParameters(
        model_class=DoubleMatrixWord2Vec,
        vocabulary_size=dataset.vocabulary.size,
        vector_dimension=100,
        window_size=5,
        n_negative_samples=5,
        batch_size=100,
        n_epoch=30,
    )

    dir_name = './word2vec/results'
    base_name = make_base_name(params)

    for model, epoch in train(dataset, params):
        save_model(join(dir_name, base_name + "_epoch{}.npz".format(epoch)), model, params)
