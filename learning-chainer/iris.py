import numpy as np
import pandas as pd
import chainer
from chainer import cuda, Function, gradient_check, Variable, optimizers, serializers, utils, Link, Chain, ChainList
import chainer.functions as F
import chainer.links as L
from sklearn import datasets
import matplotlib.pyplot as plt
from typing import Tuple


class DataSet:
    def __init__(self, train: pd.DataFrame, test: pd.DataFrame) -> None:
        self._train = train
        self._test = test

    @property
    def train(self) -> pd.DataFrame:
        return self._train

    @property
    def test(self) -> pd.DataFrame:
        return self._test

    @staticmethod
    def load() -> "DataSet":
        """Load iris dataset from sklearn."""
        iris = datasets.load_iris()
        data = iris['data'].astype(np.float32)
        target = iris['target'].astype(np.int32)
        df = pd.DataFrame({
            'sepal_length': data[:, 0],
            'sepal_width': data[:, 1],
            'petal_length': data[:, 2],
            'petal_width': data[:, 3],
            'class': target,
        })
        train = df.sample(frac=0.5, random_state=12345)
        test = df.drop(train.index)  # type: pd.DataFrame
        return DataSet(train, test)


def to_hot_vector(classes: pd.Series) -> pd.Series:
    return pd.get_dummies(classes).astype(np.float32)


class IrisChain(Chain):
    def __init__(self):
        super().__init__()
        with self.init_scope():
            self.l1 = L.Linear(4, 2)
            self.l2 = L.Linear(2, 3)

    def __call__(self, x, y):
        return F.mean_squared_error(self.forward(x), y)

    def forward(self, x):
        h1 = F.sigmoid(self.l1(x))
        h2 = self.l2(h1)
        return h2


class IrisAutoEncoder(Chain):
    def __init__(self):
        super().__init__()
        with self.init_scope():
            self.l1 = L.Linear(4, 2)
            self.l2 = L.Linear(2, 4)

    def __call__(self, x):
        return F.mean_squared_error(self.forward(x), x)

    def intermediate(self, x):
        return F.sigmoid(self.l1(x))

    def forward(self, x):
        h1 = self.intermediate(x)
        h2 = self.l2(h1)
        return h2


def learn(dataset: DataSet, n_iter: int = 10000) -> IrisChain:
    model = IrisChain()
    optimizer = optimizers.Adam()
    optimizer.setup(model)

    x_train = dataset.train.drop('class', axis=1).values
    y_train = to_hot_vector(dataset.train['class']).values

    for i in range(n_iter):
        model.cleargrads()
        x = Variable(x_train)
        y = Variable(y_train)
        loss = model(x, y)
        loss.backward()
        optimizer.update()

    return model


def learn_by_mini_batch(dataset: DataSet, batch_size: int = 25, n_iter: int = 5000) -> IrisChain:
    n = len(dataset.train)

    model = IrisChain()
    optimizer = optimizers.Adam()
    optimizer.setup(model)

    x_train = dataset.train.drop('class', axis=1).values
    y_train = to_hot_vector(dataset.train['class']).values

    for j in range(n_iter):
        shuffled = np.random.permutation(n)
        for i in range(0, n, batch_size):
            indices = shuffled[i:i+batch_size]
            x = Variable(x_train[indices])
            y = Variable(y_train[indices])
            model.cleargrads()
            loss = model(x, y)
            loss.backward()
            optimizer.update()

    return model


def evaluate(dataset: DataSet, model: IrisChain) -> Tuple[int, int]:
    x_test = dataset.test.drop('class', axis=1).values

    with chainer.no_backprop_mode():
        x = Variable(x_test)
        y = model.forward(x)
    actual = np.argmax(y.data, axis=1)

    y_test = to_hot_vector(dataset.test['class']).values
    expected = np.argmax(y_test, axis=1)

    ok = np.count_nonzero(actual == expected)
    return ok, actual.size


def pretrain(dataset: DataSet, batch_size: int = 25, n_iter: int = 3000) -> IrisAutoEncoder:
    n = len(dataset.train)

    model = IrisAutoEncoder()
    optimizer = optimizers.Adam()
    optimizer.setup(model)

    x_train = dataset.train.drop('class', axis=1).values

    for j in range(n_iter):
        shuffled = np.random.permutation(n)
        for i in range(0, n, batch_size):
            indices = shuffled[i:i+batch_size]
            x = Variable(x_train[indices])
            model.cleargrads()
            loss = model(x)
            loss.backward()
            optimizer.update()

    return model


def visualize(dataset: DataSet, model: IrisAutoEncoder) -> None:
    x_train = dataset.train.drop('class', axis=1).values
    y_train = dataset.train['class'].values
    x = Variable(x_train)
    ans = model.intermediate(x).data

    fig, ax = plt.subplots(1, 1)
    for label, marker in zip([0, 1, 2], ['^', 'o', '+']):
        mask = y_train == label
        ax.scatter(ans[mask, 0], ans[mask, 1], marker=marker)
    fig.show()


def main() -> None:
    dataset = DataSet.load()
    model = learn_by_mini_batch(dataset)
    print(evaluate(dataset, model))


if __name__ == '__main__':
    main()
