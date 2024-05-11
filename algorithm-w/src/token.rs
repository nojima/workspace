use std::fmt::{self, Display, Formatter};

use compact_str::CompactString;

#[derive(Clone, PartialEq, Debug)]
pub enum Token {
    True,
    False,
    Integer(i64),
    Identifier(CompactString),

    If,
    Then,
    Else,
    Let,
    In,
    Lambda,

    Dot,
    Colon,
    Semicolon,
    Comma,
    LParen,
    RParen,
    LBracket,
    RBracket,
    LBrace,
    RBrace,
    Plus,
    Minus,
    Asterisk,
    Slash,
    Percent,
    Eq,
    EqEq,
    Exclamation,
    NotEq,
    Ampersand,
    AndAnd,
    Pipe,
    OrOr,
}

impl Display for Token {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{:?}", self)
    }
}
