import numpy as np
from chainer import Chain, links as L, Variable, functions as F, serializers

from word2vec.dataset import Vocabulary


class DoubleMatrixWord2Vec(Chain):
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


class SingleMatrixWord2Vec(Chain):
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


def save_model(dir_name: str, model: DoubleMatrixWord2Vec, epoch: int) -> None:
    filename = "{}/w2v_model_epoch{}.npz".format(dir_name, epoch)
    serializers.save_npz(filename, model)


def load_model(filename: str, vocabulary: Vocabulary, model_class: type = DoubleMatrixWord2Vec) -> DoubleMatrixWord2Vec:
    n_units = 100   # TODO
    model = model_class(vocabulary.size, n_units)
    serializers.load_npz(filename, model)
    return model
