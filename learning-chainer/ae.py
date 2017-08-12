import numpy as np
import pandas as pd
import chainer
from chainer import cuda, Function, gradient_check, Variable, optimizers, serializers, utils, Link, Chain, ChainList
import chainer.functions as F
import chainer.links as L
from sklearn import datasets
import matplotlib.pyplot as plt
from typing import Tuple, Iterator


class DataSet:
    def __init__(self, input: np.ndarray, target: np.ndarray) -> None:
        assert input.shape[0] == target.shape[0]
        self._input = input
        self._target = target

    @property
    def size(self):
        return self._input.shape[0]

    @property
    def input(self) -> np.ndarray:
        return self._input

    @property
    def target(self) -> np.ndarray:
        return self._target

    def split(self, frac: float = 0.5) -> 'Tuple[DataSet, DataSet]':
        n_train = int(frac * self.size)
        shuffled = np.random.permutation(self.size)
        train_mask = shuffled < n_train
        test_mask = shuffled >= n_train
        return (DataSet(self._input[train_mask], self._target[train_mask]),
                DataSet(self._input[test_mask],  self._target[test_mask]))


def load_iris_dataset() -> DataSet:
    iris = datasets.load_iris()
    input = iris['data'].astype(np.float32)
    target = iris['target'].astype(np.int32)
    return DataSet(input, target)


class AutoEncoder(Chain):
    def __init__(self, input_dimension: int, hidden_dimension: int) -> None:
        super().__init__()
        with self.init_scope():
            self.layer1 = L.Linear(input_dimension, hidden_dimension)
            self.layer2 = L.Linear(hidden_dimension, input_dimension)

    def __call__(self, x: Variable) -> Variable:
        output = self.forward(x)
        return F.mean_squared_error(output, x)

    def forward(self, x: Variable) -> Variable:
        code = self.encode(x)
        return self.layer2(code)

    def encode(self, x: Variable) -> Variable:
        return F.sigmoid(self.layer1(x))


def train(dataset: DataSet, n_iter: int = 3000, batch_size: int = 25) -> Iterator[AutoEncoder]:
    n = dataset.size

    input_dimension = dataset.input.shape[1]
    hidden_dimension = 2
    model = AutoEncoder(input_dimension, hidden_dimension)

    optimizer = optimizers.Adam()
    optimizer.setup(model)

    for j in range(n_iter):
        shuffled = np.random.permutation(n)

        for i in range(0, n, batch_size):
            indices = shuffled[i:i+batch_size]
            x = Variable(dataset.input[indices])
            model.cleargrads()
            loss = model(x)
            loss.backward()
            optimizer.update()

        yield model


def visualize(ax: plt.Axes, dataset: DataSet, model: AutoEncoder) -> None:
    x = Variable(dataset.input)
    code = model.encode(x).data

    for t in np.unique(dataset.target):
        mask = dataset.target == t
        ax.scatter(code[mask, 0], code[mask, 1])


def draw_learning_process(seed=12345) -> None:
    np.random.seed(seed)

    dataset = load_iris_dataset()
    fig = plt.figure(figsize=(10, 10))

    for epoch, model in enumerate(train(dataset)):
        if epoch % 250 != 0:
            continue
        ax = fig.add_subplot(4, 3, epoch//250 + 1)
        ax.set_title("epoch {}".format(epoch))
        visualize(ax, dataset, model)

    fig.tight_layout()
    fig.show()


def draw_difference_by_initial_values(seed=12345) -> None:
    np.random.seed(seed)

    dataset = load_iris_dataset()
    fig, axes = plt.subplots(3, 3, figsize=(10, 10))

    for ax in axes.flatten():
        model = None
        for model in train(dataset):
            pass
        visualize(ax, dataset, model)

    fig.tight_layout()
    fig.show()
