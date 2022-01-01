use crate::{Node, Token};
use anyhow::Result;

fn ok<Tokens: Iterator<Item = Token>>(
    node: Box<Node>,
    mut tokens: Tokens,
) -> Result<(Box<Node>, Token, Tokens)> {
    let t = tokens.next().unwrap_or_default();
    Ok((node, t, tokens))
}

fn parse_expr<Tokens: Iterator<Item = Token>>(
    t: Token,
    tokens: Tokens,
) -> Result<(Box<Node>, Token, Tokens)> {
    let (mut node, mut t, mut tokens) = parse_term(t, tokens)?;
    loop {
        match t {
            Token::Plus => {
                t = tokens.next().unwrap_or_default();
                let (rhs, next_t, next_tokens) = parse_term(t, tokens)?;
                node = Box::new(Node::Add(node, rhs));
                t = next_t;
                tokens = next_tokens;
            }
            Token::Minus => {
                t = tokens.next().unwrap_or_default();
                let (rhs, next_t, next_tokens) = parse_term(t, tokens)?;
                node = Box::new(Node::Sub(node, rhs));
                t = next_t;
                tokens = next_tokens;
            }
            _ => {
                return Ok((node, t, tokens));
            }
        }
    }
}

fn parse_term<Tokens: Iterator<Item = Token>>(
    t: Token,
    tokens: Tokens,
) -> Result<(Box<Node>, Token, Tokens)> {
    let (mut node, mut t, mut tokens) = parse_factor(t, tokens)?;
    loop {
        match t {
            Token::Asterisk => {
                t = tokens.next().unwrap_or_default();
                let (rhs, next_t, next_tokens) = parse_factor(t, tokens)?;
                node = Box::new(Node::Mul(node, rhs));
                t = next_t;
                tokens = next_tokens;
            }
            Token::Slash => {
                t = tokens.next().unwrap_or_default();
                let (rhs, next_t, next_tokens) = parse_factor(t, tokens)?;
                node = Box::new(Node::Div(node, rhs));
                t = next_t;
                tokens = next_tokens;
            }
            _ => {
                return Ok((node, t, tokens));
            }
        }
    }
}

fn parse_factor<Tokens: Iterator<Item = Token>>(
    mut t: Token,
    mut tokens: Tokens,
) -> Result<(Box<Node>, Token, Tokens)> {
    match t {
        Token::Integer(n) => ok(Box::new(Node::Integer(n)), tokens),
        Token::LeftParen => {
            t = tokens.next().unwrap_or_default();
            let (node, next_t, next_tokens) = parse_expr(t, tokens)?;
            if next_t != Token::RightParen {
                anyhow::bail!("the opening and closing parentheses do not correspond to each other")
            }
            ok(node, next_tokens)
        }
        Token::Eof => {
            anyhow::bail!("a factor expected, but reached to EOF")
        }
        _ => {
            anyhow::bail!("a factor expected, but got token: {:?}", t)
        }
    }
}

pub fn parse<Tokens: Iterator<Item = Token>>(mut tokens: Tokens) -> Result<Box<Node>> {
    let t = tokens.next().unwrap_or_default();
    let (node, t, _) = parse_expr(t, tokens)?;
    if t != Token::Eof {
        anyhow::bail!("EOF expected, but got token: {:?}", t)
    }
    Ok(node)
}
