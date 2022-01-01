use crate::Token;
use anyhow::Result;
use std::str::Chars;

fn tokenize_positive_integer(mut ch: char, mut chars: Chars) -> (i64, char, Chars) {
    let mut n: i64 = 0;
    while ch.is_ascii_digit() {
        n = n * 10 + (ch as i64) - ('0' as i64);
        ch = chars.next().unwrap_or_default();
    }
    (n, ch, chars)
}

fn ok(token: Token, mut chars: Chars) -> Result<(Token, char, Chars)> {
    let ch = chars.next().unwrap_or_default();
    Ok((token, ch, chars))
}

fn tokenize_one(mut ch: char, mut chars: Chars) -> Result<(Token, char, Chars)> {
    // skip whitespaces
    while ch.is_whitespace() {
        ch = chars.next().unwrap_or_default();
    }

    match ch {
        '\0' => ok(Token::Eof, chars),
        '+' => ok(Token::Plus, chars),
        '-' => ok(Token::Minus, chars),
        '*' => ok(Token::Asterisk, chars),
        '/' => ok(Token::Slash, chars),
        '(' => ok(Token::LeftParen, chars),
        ')' => ok(Token::RightParen, chars),
        _ => {
            if ch.is_ascii_digit() {
                let (n, ch, chars) = tokenize_positive_integer(ch, chars);
                Ok((Token::Integer(n), ch, chars))
            } else {
                anyhow::bail!("unexpected character: {}", ch);
            }
        }
    }
}

pub fn tokenize(s: &str) -> Result<Vec<Token>> {
    let mut ret = vec![];
    let mut chars = s.chars();
    let mut ch = chars.next().unwrap_or_default();
    loop {
        let (token, next_ch, next_chars) = tokenize_one(ch, chars)?;
        if token == Token::Eof {
            return Ok(ret);
        }
        ret.push(token);
        chars = next_chars;
        ch = next_ch;
    }
}
