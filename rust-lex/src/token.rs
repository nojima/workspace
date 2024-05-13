#[derive(Debug, Clone, PartialEq)]
pub enum Token {
    True,
    False,
    Null,

    Number(f64),
    Identifier(String),
    String(String),

    Colon,
    Comma,
    LBrace,
    RBrace,
    LBracket,
    RBracket,
}
