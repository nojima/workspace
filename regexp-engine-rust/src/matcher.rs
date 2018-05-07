use std::iter;
use either::{Left, Right};

pub type Positions<'a> = Box<Iterator<Item=usize> + 'a>;

pub trait Matcher {
    // Returns a sequence of the lengths of matched strings
    // from the beginning of `s`.
    fn matches<'a>(&'a self, s: &'a str) -> Positions<'a>;
}

//-----------------------------------------------------------------------------
// ZeroMatcher (matches to empty string)

pub struct ZeroMatcher;

impl ZeroMatcher {
    pub fn new() -> ZeroMatcher {
        ZeroMatcher{}
    }
}

impl Matcher for ZeroMatcher {
    fn matches<'a>(&'a self, _: &'a str) -> Positions<'a> {
        box iter::once(0)
    }
}

//-----------------------------------------------------------------------------
// CharacterMatcher (matches to specified single character)

pub struct CharacterMatcher {
    ch: char,
}

impl CharacterMatcher {
    pub fn new(ch: char) -> CharacterMatcher {
        CharacterMatcher{
            ch: ch,
        }
    }
}

impl Matcher for CharacterMatcher {
    fn matches<'a>(&'a self, s: &'a str) -> Positions<'a> {
        let expected = self.ch;
        box s.chars().take(1).filter_map(move |c|
            if c == expected {
                Some(c.len_utf8())
            } else {
                None
            }
        )
    }
}

//-----------------------------------------------------------------------------
// AnyCharacterMatcher (macthes to any single character)

pub struct AnyCharacterMatcher;

impl AnyCharacterMatcher {
    pub fn new() -> AnyCharacterMatcher {
        AnyCharacterMatcher{}
    }
}

impl Matcher for AnyCharacterMatcher {
    fn matches<'a>(&'a self, s: &'a str) -> Positions<'a> {
        box s.chars().take(1).map(|c| c.len_utf8())
    }
}

//-----------------------------------------------------------------------------
// RepeatMatcher

pub struct RepeatMatcher {
    inner: Box<Matcher>,
}

impl RepeatMatcher {
    pub fn new(inner: Box<Matcher>) -> RepeatMatcher {
        RepeatMatcher{
            inner: inner,
        }
    }
}

impl Matcher for RepeatMatcher {
    fn matches<'a>(&'a self, s: &'a str) -> Positions<'a> {
        box self.inner.matches(s).flat_map(move |n1|
            if n1 == 0 {
                Left(iter::once(0))
            } else {
                Right(self.matches(&s[n1..]).map(move |n2| n1 + n2))
            }
        ).chain(iter::once(0))
    }
}

//-----------------------------------------------------------------------------
// ConcatenationMatcher

pub struct ConcatenationMatcher {
    head: Box<Matcher>,
    tail: Box<Matcher>,
}

impl ConcatenationMatcher {
    pub fn new(head: Box<Matcher>, tail: Box<Matcher>) -> ConcatenationMatcher {
        ConcatenationMatcher{
            head: head,
            tail: tail,
        }
    }
}

impl Matcher for ConcatenationMatcher {
    fn matches<'a>(&'a self, s: &'a str) -> Positions<'a> {
        box self.head.matches(s).flat_map(move |n1|
            self.tail.matches(&s[n1..]).map(move |n2| n1 + n2)
        )
    }
}

//-----------------------------------------------------------------------------
// AlternationMatcher

pub struct AlternationMatcher {
    left: Box<Matcher>,
    right: Box<Matcher>,
}

impl AlternationMatcher {
    pub fn new(left: Box<Matcher>, right: Box<Matcher>) -> AlternationMatcher {
        AlternationMatcher{
            left: left,
            right: right,
        }
    }
}

impl Matcher for AlternationMatcher {
    fn matches<'a>(&'a self, s: &'a str) -> Positions<'a> {
        box self.left.matches(s).chain(self.right.matches(s))
    }
}
