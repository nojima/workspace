use crate::{ast::Expr, token::Token};

#[derive(Debug, Clone, PartialEq, thiserror::Error)]
pub enum ParseError {
    #[error("unexpected end-of-file")]
    UnexpectedEndOfFile,

    #[error("unexpected token: {0}")]
    UnexpectedToken(Token),

    #[error("unexpected token: {0} was expected, but got {1}")]
    UnexpectedToken2(String, Token),
}

type Result<T> = std::result::Result<T, ParseError>;

fn ok(expr: Expr, tokens: &[Token]) -> Result<(Box<Expr>, &[Token])> {
    Ok((Box::new(expr), tokens))
}

fn take_one(tokens: &[Token]) -> Result<(&Token, &[Token])> {
    let Some(token) = tokens.first() else {
        return Err(ParseError::UnexpectedEndOfFile);
    };
    Ok((token, &tokens[1..]))
}

macro_rules! take_exact {
    ($pattern:pat, $tokens:ident, $expected:expr) => {
        let (token, $tokens) = take_one($tokens)?;
        let $pattern = token else {
            return Err(ParseError::UnexpectedToken2($expected.into(), token.clone()));
        };
    };
}

pub fn parse(tokens: &[Token]) -> Result<Box<Expr>> {
    let (token, rest) = parse_expr(tokens)?;
    if let Some(token) = rest.first() {
        return Err(ParseError::UnexpectedToken(token.clone()));
    }
    Ok(token)
}

// expr ::=
//   | simple_expr+
fn parse_expr(tokens: &[Token]) -> Result<(Box<Expr>, &[Token])> {
    let (mut expr, mut tokens) = parse_simple_expr(tokens)?;
    loop {
        match parse_simple_expr(tokens) {
            Ok((expr_, tokens_)) => {
                expr = Box::new(Expr::Apply(expr, expr_));
                tokens = tokens_;
            }
            Err(_) => return Ok((expr, tokens)),
        }
    }
}

// simple_expr ::=
//   | bool
//   | integer
//   | identifier
//   | "(" expr ")"
//   | "lambda" identifier "." expr
//   | "if" expr "then" expr "else" expr
fn parse_simple_expr(tokens: &[Token]) -> Result<(Box<Expr>, &[Token])> {
    let (token, tokens) = take_one(tokens)?;
    match token {
        Token::True => ok(Expr::Bool(true), tokens),
        Token::False => ok(Expr::Bool(false), tokens),
        Token::Integer(n) => ok(Expr::Integer(*n), tokens),
        Token::Identifier(ident) => ok(Expr::Variable(ident.clone()), tokens),
        Token::LParen => parse_paren(tokens),
        Token::Lambda => parse_lambda(tokens),
        Token::If => parse_if(tokens),
        t => return Err(ParseError::UnexpectedToken(t.clone())),
    }
}

// "(" expr ")"
fn parse_paren(tokens: &[Token]) -> Result<(Box<Expr>, &[Token])> {
    let (expr, tokens) = parse_expr(tokens)?;
    take_exact!(Token::RParen, tokens, "')'");
    Ok((expr, tokens))
}

// "lambda" identifier "." expr
fn parse_lambda(tokens: &[Token]) -> Result<(Box<Expr>, &[Token])> {
    take_exact!(Token::Identifier(t_ident), tokens, "identifier");
    take_exact!(Token::Dot, tokens, "'.'");
    let (expr, tokens) = parse_expr(tokens)?;
    let lambda = Expr::Lambda(t_ident.clone(), expr);
    ok(lambda, tokens)
}

// "if" expr "then" expr "else" expr
fn parse_if(tokens: &[Token]) -> Result<(Box<Expr>, &[Token])> {
    let (cond_expr, tokens) = parse_expr(tokens)?;
    take_exact!(Token::Then, tokens, "'then'");
    let (then_expr, tokens) = parse_expr(tokens)?;
    take_exact!(Token::Else, tokens, "'else'");
    let (else_expr, tokens) = parse_expr(tokens)?;
    let if_expr = Expr::If(cond_expr, then_expr, else_expr);
    ok(if_expr, tokens)
}
