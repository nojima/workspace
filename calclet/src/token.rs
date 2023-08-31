#[derive(Debug, Clone, PartialEq)]
pub enum Token {
    Number(f64),
    String(String),
    Identifier(String),

    Let,
    If,
    Then,
    Else,

    Exclamation,
    LParen,
    RParen,
    Asterisk,
    Plus,
    Minus,
    Slash,
    Semicolon,
    Lt,
    Eq,
    Gt,
    LtEq,
    EqEq,
    NotEq,
    GtEq,
}
