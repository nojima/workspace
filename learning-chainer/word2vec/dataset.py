import numpy as np


class Vocabulary:
    def __init__(self):
        self._word2id = {}  # type: Dict[str, int]
        self._id2word = {}  # type: Dict[int, str]

    def intern(self, word: str) -> int:
        if word not in self._word2id:
            id = len(self._word2id)
            self._word2id[word] = id
            self._id2word[id] = word
        return self._word2id[word]

    def to_word(self, id: int) -> str:
        return self._id2word[id]

    def to_id(self, word: str) -> int:
        return self._word2id[word]

    @property
    def size(self):
        return len(self._word2id)


class DataSet:
    def __init__(self, filename: str, vocabulary: Vocabulary = None) -> None:
        self._vocabulary = vocabulary or Vocabulary()

        data = []
        with open(filename) as f:
            for line in f:
                for word in line.split():
                    id = self._vocabulary.intern(word)
                    data.append(id)

        self._data = np.array(data, dtype=np.int32)

    @property
    def size(self) -> int:
        return len(self._data)

    @property
    def vocabulary(self) -> Vocabulary:
        return self._vocabulary

    @property
    def data(self) -> np.ndarray:
        return self._data
