from typing import Optional, Iterator, Tuple
import unittest


class Matcher:
    def match(self, string: str) -> Iterator[int]:
        raise NotImplementedError()


class ZeroMatcher(Matcher):
    def match(self, string: str) -> Iterator[int]:
        yield 0


class CharacterMatcher(Matcher):
    def __init__(self, ch: str) -> None:
        self._ch = ch

    def match(self, string: str) -> Iterator[int]:
        if len(string) > 0 and string[0] == self._ch:
            yield 1


class AnyCharacterMatcher(Matcher):
    def match(self, string: str) -> Iterator[int]:
        if len(string) > 0:
            yield 1


class RepeatMatcher(Matcher):
    def __init__(self, inner: Matcher) -> None:
        self._inner = inner

    def match(self, string: str) -> Iterator[int]:
        for n1 in self._inner.match(string):
            if n1 == 0:
                yield 0
            else:
                for n2 in self.match(string[n1:]):
                    yield n1 + n2
        yield 0


class ConcatenationMatcher(Matcher):
    def __init__(self, head: Matcher, tail: Matcher) -> None:
        self._head = head
        self._tail = tail

    def match(self, string: str) -> Iterator[int]:
        for n1 in self._head.match(string):
            for n2 in self._tail.match(string[n1:]):
                yield n1 + n2


class AlternationMatcher(Matcher):
    def __init__(self, left: Matcher, right: Matcher) -> None:
        self._left = left
        self._right = right

    def match(self, string: str) -> Iterator[int]:
        for n in self._left.match(string):
            yield n
        for n in self._right.match(string):
            yield n


def _compile_character(pattern: str) -> Tuple[Matcher, str]:
    if len(pattern) == 0:
        return ZeroMatcher(), pattern
    if pattern[0] in ('|', ')'):
        return ZeroMatcher(), pattern
    if pattern[0] == '(':
        matcher, rest = _compile_alternation(pattern[1:])
        if not rest.startswith(')'):
            raise ValueError("カッコが対応していません。")
        return matcher, rest[1:]
    if pattern[0] == '.':
        return AnyCharacterMatcher(), pattern[1:]
    if pattern[0] == '\\' and len(pattern) >= 2:
        return CharacterMatcher(pattern[1]), pattern[2:]
    return CharacterMatcher(pattern[0]), pattern[1:]


def _compile_quantifier(pattern: str) -> Tuple[Matcher, str]:
    inner, rest = _compile_character(pattern)
    if rest.startswith('*'):
        return RepeatMatcher(inner), rest[1:]
    return inner, rest


def _compile_concatenation(pattern: str) -> Tuple[Matcher, str]:
    matcher, rest = _compile_quantifier(pattern)
    while len(rest) > 0 and rest[0] not in ('|', ')'):
        m, rest = _compile_quantifier(rest)
        matcher = ConcatenationMatcher(matcher, m)
    return matcher, rest


def _compile_alternation(pattern: str) -> Tuple[Matcher, str]:
    matcher, rest = _compile_concatenation(pattern)
    while rest.startswith('|'):
        m, rest = _compile_concatenation(rest[1:])
        matcher = AlternationMatcher(matcher, m)
    return matcher, rest


def _compile(pattern: str) -> Matcher:
    matcher, rest = _compile_alternation(pattern)
    if len(rest) > 0:
        raise ValueError("なんかおかしい")
    return matcher


def regexp_match(pattern: str, string: str) -> Optional[str]:
    matcher = _compile(pattern)
    for n in matcher.match(string):
        return string[:n]
    return None


class TestRegexp(unittest.TestCase):
    def test_regexp(self) -> None:
        cases = [
            ("", "abc", ""),
            ("", "", ""),
            ("hello", "hello", "hello"),
            ("hello", "world", None),
            ("...", "Beer", "Bee"),
            ("...", "He", None),
            ("foo|bar", "barxxx", "bar"),
            ("foo|bar", "buzzxxx", None),
            ("a*", "aaaaa", "aaaaa"),
            ("a*", "bbbbb", ""),
            ("c(abc)*", "cabcabcd", "cabcabc"),
            ("c(abc)*", "cabacaabcd", "c"),
            ("(hello|world)*", "hellohelloworldhelloheywww", "hellohelloworldhello"),
            (".*Foo.*Bar", "This is Foo and that is Bar.", "This is Foo and that is Bar"),
            (".*Foo.*Bar", "This is Bar and that is Foo.", None),
            ("(0|1|2|3|4|5|6|7|8|9)* yen", "972 yen.", "972 yen"),
            ("(0|1|2|3|4|5|6|7|8|9)* yen", "972 dollers.", None),
            ("c(a*b*)*d", "caaabbbbbbabaaabdaaaaa", "caaabbbbbbabaaabd"),
            ("(a|b)(a|b)*|c", "cabab", "c"),
            (r"\(foo\|bar\)\\\\", r"(foo|bar)\\", r"(foo|bar)\\"),
        ]
        for pattern, string, expected in cases:
            self.assertEqual(expected, regexp_match(pattern, string))


if __name__ == '__main__':
    unittest.main()
