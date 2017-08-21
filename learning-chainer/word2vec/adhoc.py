import os
import re
from os.path import join, basename
from glob import glob
import multiprocessing
from distutils.version import LooseVersion

import numpy as np
import matplotlib.pyplot as plt
from scipy.spatial.distance import cosine

from word2vec.dataset import DataSet, Vocabulary
from word2vec.evaluate import evaluate
from word2vec.models import Word2Vec, SingleMatrixWord2Vec, DoubleMatrixWord2Vec
from word2vec.train import train, save_model, load_model, HyperParameters
from word2vec.visualize import visualize_countries


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


def run_single(dataset: DataSet, params: HyperParameters) -> None:
    dir_name = "./word2vec/results"
    base_name = make_base_name(params)

    for model, epoch in train(dataset, params):
        save_model(join(dir_name, base_name + "_epoch{}.npz".format(epoch)), model, params)


def run_parallel() -> None:
    dataset = DataSet("./word2vec/ptb.train.txt")
    params_list = []

    # make a directory to save results.
    os.makedirs("./word2vec/results", exist_ok=True)

    for model_class in [SingleMatrixWord2Vec, DoubleMatrixWord2Vec]:
        for vector_dimension in [50, 100, 200]:
            for window_size in [3, 5]:
                params_list.append(HyperParameters(
                    model_class=model_class,
                    vocabulary_size=dataset.vocabulary.size,
                    vector_dimension=vector_dimension,
                    window_size=window_size,
                    n_negative_samples=5,
                    batch_size=100,
                    n_epoch=30,
                ))

    with multiprocessing.Pool(processes=6) as pool:
        for params in params_list:
            pool.apply_async(run_single, args=(dataset, params))
        pool.close()
        pool.join()


def visualize_models(vocabulary: Vocabulary) -> None:
    fig, axes = plt.subplots(4, 3, figsize=(13, 13))

    for filename, ax in zip(sorted(glob("./word2vec/results/*_epoch29.npz")), axes.flatten()):
        model, params = load_model(filename)

        ax.set_title("{} vd={} w={}".format(
            params.model_class.__name__.replace("Word2Vec", "").lower(),
            params.vector_dimension,
            params.window_size))
        visualize_countries(model, vocabulary, ax)

    fig.tight_layout()
    fig.show()


def visualize_model_learning_process(vocabulary: Vocabulary) -> None:
    filename_template = "./word2vec/results/word2vec_singlematrix_vd100_w5_ns5_bs100_epoch{}.npz"

    fig, axes = plt.subplots(4, 3, figsize=(13, 13))

    for epoch, ax in zip(range(0, 31, 3), axes.flatten()):
        epoch = min(epoch, 29)
        model, params = load_model(filename_template.format(epoch))

        ax.set_title("epoch={}".format(epoch))
        visualize_countries(model, vocabulary, ax)

    fig.tight_layout()

    fig.suptitle("word2vec singlematrix vd=100 w=5 ns=5 bs=100")
    fig.subplots_adjust(top=0.93)

    fig.show()


def print_loss(vocabulary: Vocabulary) -> None:
    test_set = DataSet("./word2vec/ptb.test.txt", vocabulary)

    filenames = glob("./word2vec/results/*.npz")
    for filename in sorted(filenames, key=lambda n: LooseVersion(basename(n))):
        model, params = load_model(filename)
        nll = evaluate(model, params, test_set)
        print("{}: {}".format(basename(filename), nll))


def visualize_loss() -> None:
    xs = {}
    ys = {}

    with open("./word2vec/results/loss.txt") as f:
        for line in f:
            name, nll = line.strip().split(": ")
            nll = float(nll)

            m = re.match(r"word2vec_(.*)_epoch([0-9]*)\.npz", name)
            label = m.group(1)
            epoch = int(m.group(2))

            m = re.search(r"_w([0-9]*)_", label)
            window_size = int(m.group(1))

            xs.setdefault(window_size, {}).setdefault(label, []).append(epoch)
            ys.setdefault(window_size, {}).setdefault(label, []).append(nll)

    fig, axes = plt.subplots(2, 1, figsize=(10, 10))
    for w, ax in zip(xs.keys(), axes.flatten()):
        for label in xs[w].keys():
            ax.plot(xs[w][label], ys[w][label], label=label)
            ax.legend()

    fig.tight_layout()
    fig.show()


def visualize_models(vocabulary: Vocabulary) -> None:
    fig, axes = plt.subplots(4, 3, figsize=(13, 13))

    for filename, ax in zip(sorted(glob("./word2vec/results/*_epoch29.npz")), axes.flatten()):
        model, params = load_model(filename)

        ax.set_title("{} vd={} w={}".format(
            params.model_class.__name__.replace("Word2Vec", "").lower(),
            params.vector_dimension,
            params.window_size))
        visualize_countries(model, vocabulary, ax)

    fig.tight_layout()
    fig.show()