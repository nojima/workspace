mod parse;
mod tokenize;

use crate::parse::parse;
use crate::tokenize::tokenize;
use anyhow::Result;
use std::io::{self, Write};

fn print_prompt() -> io::Result<()> {
    print!("expr> ");
    io::stdout().flush()?;
    Ok(())
}

fn read_line() -> io::Result<Option<String>> {
    let mut input = String::new();
    match io::stdin().read_line(&mut input)? {
        0 => Ok(None),
        _ => Ok(Some(input)),
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Token {
    Eof,
    Integer(i64),
    Plus,
    Minus,
    Asterisk,
    Slash,
    LeftParen,
    RightParen,
}

impl Default for Token {
    fn default() -> Self {
        Token::Eof
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Node {
    Integer(i64),
    Add(Box<Node>, Box<Node>),
    Sub(Box<Node>, Box<Node>),
    Mul(Box<Node>, Box<Node>),
    Div(Box<Node>, Box<Node>),
}

fn do_something(line: &str) -> Result<()> {
    let tokens = tokenize(&line)?;
    println!("Tokens: {:?}", tokens);
    let node = parse(tokens.into_iter())?;
    println!("AST: {:?}", node);
    Ok(())
}

fn main() -> Result<()> {
    loop {
        print_prompt()?;
        match read_line()? {
            Some(line) => {
                do_something(&line)?;
            }
            None => {
                println!("\nByebye!");
                return Ok(());
            }
        }
    }
}
