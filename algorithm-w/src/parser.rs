use std::rc::Rc;

use crate::{
    ast::{BinOp, Expr, LetType},
    token::Token,
};

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
            return Err(ParseError::UnexpectedToken2(
                $expected.into(),
                token.clone(),
            ));
        };
    };
}

macro_rules! take_one_if_match {
    ($pattern:pat, $tokens:ident) => {{
        let (token, tokens) = take_one($tokens)?;
        if let $pattern = token {
            (Some(token), tokens)
        } else {
            (None, $tokens)
        }
    }};
}

pub fn parse(tokens: &[Token]) -> Result<Box<Expr>> {
    let (token, rest) = parse_expr(tokens)?;
    if let Some(token) = rest.first() {
        return Err(ParseError::UnexpectedToken(token.clone()));
    }
    Ok(token)
}

// expr ::=
//   | term
//   | expr "+" term
//   | expr "==" term
// TODO: 演算子の優先順位を実装する
fn parse_expr(tokens: &[Token]) -> Result<(Box<Expr>, &[Token])> {
    let (mut expr, mut tokens) = parse_term(tokens)?;
    loop {
        let Ok((t_binop, tokens_)) = take_one(tokens) else {
            break;
        };
        match t_binop {
            Token::Plus => {
                let (expr_, tokens_) = parse_term(tokens_)?;
                expr = Box::new(Expr::BinOp(BinOp::Add, expr, expr_));
                tokens = tokens_;
            }
            Token::EqEq => {
                let (expr_, tokens_) = parse_term(tokens_)?;
                expr = Box::new(Expr::BinOp(BinOp::Eq, expr, expr_));
                tokens = tokens_;
            }
            _ => break,
        }
    }
    Ok((expr, tokens))
}

// term ::=
//   | factor
//   | factor factor...
//   | "[" identifier "]" expr
//   | "if" expr "then" expr "else" expr
//   | "let" "rec"? identifier "=" expr ";" expr
fn parse_term(tokens: &[Token]) -> Result<(Box<Expr>, &[Token])> {
    let (token, tokens_) = take_one(tokens)?;
    match token {
        Token::LBracket => parse_lambda(tokens_),
        Token::If => parse_if(tokens_),
        Token::Let => parse_let(tokens_),
        _ => {
            // factor | factor factor...
            let (mut expr, mut tokens) = parse_factor(tokens)?;
            while let Ok((expr_, tokens_)) = parse_factor(tokens) {
                expr = Box::new(Expr::Apply(expr, expr_));
                tokens = tokens_;
            }
            Ok((expr, tokens))
        }
    }
}

// factor ::=
//   | bool
//   | integer
//   | identifier
//   | "(" expr ")"
fn parse_factor(tokens: &[Token]) -> Result<(Box<Expr>, &[Token])> {
    let (token, tokens) = take_one(tokens)?;
    match token {
        Token::True => ok(Expr::Bool(true), tokens),
        Token::False => ok(Expr::Bool(false), tokens),
        Token::Int(n) => ok(Expr::Int(*n), tokens),
        Token::Identifier(ident) => ok(Expr::Variable(ident.clone()), tokens),
        Token::LParen => parse_paren(tokens),
        t => return Err(ParseError::UnexpectedToken(t.clone())),
    }
}

// "(" expr ")"
fn parse_paren(tokens: &[Token]) -> Result<(Box<Expr>, &[Token])> {
    let (expr, tokens) = parse_expr(tokens)?;
    take_exact!(Token::RParen, tokens, "')'");
    Ok((expr, tokens))
}

// "[" identifier "]" expr
fn parse_lambda(tokens: &[Token]) -> Result<(Box<Expr>, &[Token])> {
    take_exact!(Token::Identifier(t_ident), tokens, "identifier");
    take_exact!(Token::RBracket, tokens, "']'");
    let (expr, tokens) = parse_expr(tokens)?;
    let lambda = Expr::Lambda(t_ident.clone(), Rc::new(*expr));
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

// "let" "rec"? identifier "=" expr ";" expr
fn parse_let(tokens: &[Token]) -> Result<(Box<Expr>, &[Token])> {
    let (t_rec, tokens) = take_one_if_match!(Token::Rec, tokens);
    take_exact!(Token::Identifier(t_ident), tokens, "identifier");
    take_exact!(Token::Eq, tokens, "'='");
    let (bound_expr, tokens) = parse_expr(tokens)?;
    take_exact!(Token::Semicolon, tokens, "';'");
    let (body_expr, tokens) = parse_expr(tokens)?;
    let let_expr = Expr::Let(
        t_ident.clone(),
        bound_expr,
        body_expr,
        if t_rec.is_some() {
            LetType::Rec
        } else {
            LetType::Normal
        },
    );
    ok(let_expr, tokens)
}
