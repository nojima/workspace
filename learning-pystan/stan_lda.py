import pystan
import numpy as np
import matplotlib.pyplot as plt


class Vocabulary:
    def __init__(self):
        self._word2id = {}
        self._id2word = {}

    def intern(self, word):
        if word in self._word2id:
            return self._word2id[word]
        new_id = len(self._word2id) + 1
        self._word2id[word] = new_id
        self._id2word[new_id] = word
        return new_id

    def word(self, wid):
        return self._id2word[wid]

    @property
    def size(self):
        return len(self._word2id)


def read_corpus(filename, max_lines):
    vocab = Vocabulary()
    vocab.intern("<unk>")

    word_ids = []
    doc_ids = []

    with open(filename) as f:
        for i, line in enumerate(f):
            if i >= max_lines:
                break
            line = line.strip()
            words = line.split(" ")
            for word in words:
                wid = vocab.intern(word)
                word_ids.append(wid)
                doc_ids.append(i + 1)

    return (word_ids, doc_ids, vocab)


def run_stan(word_ids, doc_ids, vocab, n_topics=10):
    # https://stats.stackexchange.com/questions/59684/what-are-typical-values-to-use-for-alpha-and-beta-in-latent-dirichlet-allocation
    alpha = np.full(n_topics, 50 / n_topics)
    beta = np.full(vocab.size, 0.1)

    data = {
        "n_topics": n_topics,
        "n_vocab": vocab.size,
        "n_words": len(word_ids),
        "n_docs": max(doc_ids),
        "words": word_ids,
        "doc_of": doc_ids,
        "alpha": alpha,
        "beta": beta,
    }

    with open("lda.stan", encoding="utf-8") as f:
        model_code = f.read()
        # pystan は非ASCII文字があると例外が飛んでしまうので、非ASCII文字を消す
        model_code = model_code.encode("ascii", errors="ignore").decode("ascii")

    fit = pystan.stan(model_code=model_code, data=data, iter=300)
    return fit
