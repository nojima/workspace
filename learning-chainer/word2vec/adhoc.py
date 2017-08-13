import numpy as np
from scipy.spatial.distance import cosine

from word2vec.dataset import DataSet, Vocabulary
from word2vec.models import save_model, DoubleMatrixWord2Vec
from word2vec.train import train


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


def run(seed: int = 12345) -> None:
    np.random.seed(seed)

    dataset = DataSet("ptb.train.txt")
    for model, epoch in train(dataset, n_epoch=50):
        save_model("./models/v3", model, epoch)
