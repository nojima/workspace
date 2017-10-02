"""日英京都関連文書対訳コーパスとtatoeba.orgのコーパスを学習に使いやすい形式に変換するためのモジュール。"""

import glob
import logging
import os.path
import subprocess
import xml.etree.ElementTree as ET


def setup_logger():
    logger = logging.getLogger(__name__)
    handler = logging.StreamHandler()
    handler.setLevel(logging.DEBUG)
    logger.setLevel(logging.DEBUG)
    logger.addHandler(handler)
    logger.propagate = False
    return logger


logger = setup_logger()


def read_xml(filename):
    tree = ET.parse(filename)
    result = []
    for sentence in tree.iter("sen"):
        japanese = sentence.find("j").text
        english = None
        for e in sentence.iter("e"):
            if e.get("type") == "check":
                english = e.text
                break
        if english is not None:
            result.append((japanese, english))
    return result


def read_all_xmls(dir_name):
    result = []
    for filename in glob.glob(dir_name + "/*/*.xml"):
        logger.info("Reading {}".format(filename))
        result.extend(read_xml(filename))
    return result


def read_tatoeba_corpus(dir_name):
    japanese = {}
    english = {}
    with open(os.path.join(dir_name, "sentences.csv")) as f:
        for line in f:
            sid, language, sentence = line.strip().split("\t")
            sid = int(sid)
            if language == "jpn":
                japanese[sid] = sentence
            elif language == "eng":
                english[sid] = sentence

    pairs = []
    with open(os.path.join(dir_name, "links.csv")) as f:
        for line in f:
            src, dst = line.strip().split("\t")
            src = int(src)
            dst = int(dst)
            if (src in japanese) and (dst in english):
                pairs.append((japanese[src], english[dst]))

    return pairs


class Splitter:
    def __init__(self, cmd):
        self._p = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE)

    def split(self, sentence):
        # XXX: このコードはデッドロックする可能性がある
        self._p.stdin.write(sentence.strip().encode("utf-8"))
        self._p.stdin.write(b"\n")
        self._p.stdin.flush()
        line = self._p.stdout.readline().decode("utf-8")
        return line.strip().split(" ")

    def close(self):
        self._p.kill()
        self._p.wait()


class JapaneseSplitter(Splitter):
    def __init__(self):
        super().__init__(["mecab", "-Owakati"])


class EnglishSplitter(Splitter):
    def __init__(self):
        super().__init__(["/opt/opennlp/bin/opennlp", "TokenizerME", "/opt/opennlp/models/en-token.bin"])


def split_translation_pairs(pairs):
    ja_splitter = JapaneseSplitter()
    en_splitter = EnglishSplitter()
    try:
        result = []
        for i, (ja, en) in enumerate(pairs):
            if i % 1000 == 0:
                logger.info("Processing sentence-{}...".format(i))
            ja_words = ja_splitter.split(ja)
            en_words = en_splitter.split(en)
            result.append({"ja": ja_words, "en": en_words})
        return result
    finally:
        en_splitter.close()
        ja_splitter.close()
