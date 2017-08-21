import matplotlib.pyplot as plt
import numpy as np
from sklearn.decomposition import PCA
from sklearn.manifold import TSNE

from word2vec.dataset import Vocabulary, DataSet
from word2vec.models import Word2Vec


def project_to_2d_by_tsne(model: Word2Vec, vocabulary: Vocabulary, perplexity: int = 25):
    word_ids = np.arange(0, vocabulary.size, dtype=np.int32)
    vectors = model.distributed_representation(word_ids)

    tsne = TSNE(n_components=2, verbose=3, perplexity=perplexity, random_state=12345)
    return tsne.fit_transform(vectors)


def project_to_2d_by_pca(model: Word2Vec, vocabulary: Vocabulary):
    word_ids = np.arange(0, vocabulary.size, dtype=np.int32)
    vectors = model.distributed_representation(word_ids)

    pca = PCA(n_components=2)
    return pca.fit_transform(vectors)


def visualize_countries(model: Word2Vec, vocabulary: Vocabulary, ax: plt.Axes = None):
    countries = ['u.s.', 'u.k.', 'italy', 'korea', 'china', 'germany', 'japan', 'france', 'russia', 'egypt']
    capitals = ['washington', 'london', 'rome', 'seoul', 'beijing', 'berlin', 'tokyo', 'paris', 'moscow', 'cairo']

    vectors_2d = project_to_2d_by_pca(model, vocabulary)

    if ax is None:
        fig, ax = plt.subplots()
    else:
        fig = None

    # Plot countries
    country_ids = [vocabulary.to_id(word) for word in countries]
    country_vectors = vectors_2d[country_ids]
    ax.scatter(country_vectors[:, 0], country_vectors[:, 1], c='blue', alpha=0.7)
    for i, label in enumerate(countries):
        ax.annotate(label, (country_vectors[i, 0], country_vectors[i, 1]))

    # Plot capitals
    capital_ids = [vocabulary.to_id(word) for word in capitals]
    capital_vectors = vectors_2d[capital_ids]
    ax.scatter(capital_vectors[:, 0], capital_vectors[:, 1], c='orange', alpha=0.7)
    for i, label in enumerate(capitals):
        ax.annotate(label, (capital_vectors[i, 0], capital_vectors[i, 1]))

    # Draw arrows
    for country, capital in zip(countries, capitals):
        v1 = vectors_2d[vocabulary.to_id(country)]
        v2 = vectors_2d[vocabulary.to_id(capital)]
        ax.arrow(v1[0], v1[1], (v2 - v1)[0], (v2 - v1)[1], alpha=0.5)

    if fig is not None:
        fig.show()


def visualize_frequent_words(vectors_2d: np.ndarray, dataset: DataSet, k: int, ax: plt.Axes = None) -> None:
    word_ids, counts = np.unique(dataset.data, return_counts=True)

    indices = np.argpartition(-counts, k)[:k]
    frequent_word_ids = word_ids[indices]

    if ax is None:
        fig, ax = plt.subplots(figsize=(13, 13))
    else:
        fig = None

    vectors_2d = vectors_2d[frequent_word_ids]

    ax.scatter(vectors_2d[:, 0], vectors_2d[:, 1], s=2, alpha=0.25)
    for i, id in enumerate(frequent_word_ids):
        ax.annotate(dataset.vocabulary.to_word(id), (vectors_2d[i, 0], vectors_2d[i, 1]))

    if fig is not None:
        fig.tight_layout()
        fig.show()
