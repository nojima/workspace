import matplotlib.pyplot as plt
import numpy as np
from sklearn.decomposition import PCA
from sklearn.manifold import TSNE

from word2vec.dataset import Vocabulary
from word2vec.models import DoubleMatrixWord2Vec


def project_to_2d_by_tsne(vocabulary: Vocabulary, model: DoubleMatrixWord2Vec, perplexity: int = 25):
    word_ids = np.arange(0, vocabulary.size, dtype=np.int32)
    vectors = model.distributed_representation(word_ids)

    tsne = TSNE(n_components=2, verbose=3, perplexity=perplexity, random_state=12345)
    return tsne.fit_transform(vectors)


def project_to_2d_by_pca(vocabulary: Vocabulary, model: DoubleMatrixWord2Vec):
    word_ids = np.arange(0, vocabulary.size, dtype=np.int32)
    vectors = model.distributed_representation(word_ids)

    pca = PCA(n_components=2)
    return pca.fit_transform(vectors)


def visualize(vocabulary: Vocabulary, vectors_2d: np.ndarray, ax: plt.Axes = None):
    countries = ['u.s.', 'u.k.', 'italy', 'korea', 'china', 'germany', 'japan', 'france', 'russia', 'egypt']
    capitals = ['washington', 'london', 'rome', 'seoul', 'beijing', 'berlin', 'tokyo', 'paris', 'moscow', 'cairo']
    mask = [vocabulary.to_id(word) for word in countries + capitals]

    if ax is None:
        fig, ax = plt.subplots()
    else:
        fig = None

    target_vectors = vectors_2d[mask]
    ax.scatter(target_vectors[:, 0], target_vectors[:, 1])
    for i, label in enumerate(countries + capitals):
        ax.annotate(label, (target_vectors[i, 0], target_vectors[i, 1]))
    for country, capital in zip(countries, capitals):
        v1 = vectors_2d[vocabulary.to_id(country)]
        v2 = vectors_2d[vocabulary.to_id(capital)]
        ax.arrow(v1[0], v1[1], (v2 - v1)[0], (v2 - v1)[1])

    if fig is not None:
        fig.show()
