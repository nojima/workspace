#![feature(box_syntax)]

extern crate either;

use either::{Left, Right};
use std::iter;

type Positions<'a> = Box<Iterator<Item = usize> + 'a>;

trait Matcher {
    fn match_<'a>(&'a self, s: &'a str) -> Positions<'a>;
}

//-----------------------------------------------------------------------------
// ZeroMatcher (matches to empty string)

struct ZeroMatcher;

impl ZeroMatcher {
    fn new() -> ZeroMatcher {
        ZeroMatcher {}
    }
}

impl Matcher for ZeroMatcher {
    fn match_<'a>(&'a self, s: &'a str) -> Positions<'a> {
        box iter::once(0)
    }
}

//-----------------------------------------------------------------------------
// CharacterMatcher (matches to specified single character)

struct CharacterMatcher {
    ch: char,
}

impl CharacterMatcher {
    fn new(ch: char) -> CharacterMatcher {
        CharacterMatcher { ch: ch }
    }
}

impl Matcher for CharacterMatcher {
    fn match_<'a>(&'a self, s: &'a str) -> Positions<'a> {
        box s.chars().take(1).filter_map(|c| {
            if c == self.ch {
                Some(c.len_utf8())
            } else {
                None
            }
        })
    }
}

//-----------------------------------------------------------------------------
// AnyCharacterMatcher (macthes to any single character)

struct AnyCharacterMatcher;

impl AnyCharacterMatcher {
    fn new() -> AnyCharacterMatcher {
        AnyCharacterMatcher {}
    }
}

impl Matcher for AnyCharacterMatcher {
    fn match_<'a>(&'a self, s: &'a str) -> Positions<'a> {
        box s.chars().take(1).map(|c| c.len_utf8())
    }
}

//-----------------------------------------------------------------------------
// RepeatMatcher

struct RepeatMatcher {
    inner: Box<Matcher>,
}

impl RepeatMatcher {
    fn new(inner: Box<Matcher>) -> RepeatMatcher {
        RepeatMatcher { inner: inner }
    }
}

impl Matcher for RepeatMatcher {
    fn match_<'a>(&'a self, s: &'a str) -> Positions<'a> {
        box self.inner
            .match_(s)
            .flat_map(|n1| {
                if n1 == 0 {
                    Left(iter::once(0))
                } else {
                    Right(self.match_(&s[n1..]).map(|n2| n1 + n2))
                }
            })
            .chain(iter::once(0))
    }
}

//-----------------------------------------------------------------------------
// ConcatenationMatcher

struct ConcatenationMatcher {
    head: Box<Matcher>,
    tail: Box<Matcher>,
}

impl ConcatenationMatcher {
    fn new(head: Box<Matcher>, tail: Box<Matcher>) -> ConcatenationMatcher {
        ConcatenationMatcher {
            head: head,
            tail: tail,
        }
    }
}

impl Matcher for ConcatenationMatcher {
    fn match_<'a>(&'a self, s: &'a str) -> Positions<'a> {
        box self.head
            .match_(s)
            .flat_map(|n1| self.tail.match_(&s[n1..]).map(|n2| n1 + n2))
    }
}

//-----------------------------------------------------------------------------
// AlternationMatcher

struct AlternationMatcher {
    left: Box<Matcher>,
    right: Box<Matcher>,
}

impl AlternationMatcher {
    fn new(left: Box<Matcher>, right: Box<Matcher>) -> AlternationMatcher {
        AlternationMatcher {
            left: left,
            right: right,
        }
    }
}

impl Matcher for AlternationMatcher {
    fn match_<'a>(&'a self, s: &'a str) -> Positions<'a> {
        box self.left.match_(s).chain(self.right.match_(s))
    }
}
