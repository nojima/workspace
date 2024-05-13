use once_cell::sync::Lazy;
use regex::Regex;

use crate::token::Token;

#[derive(Debug, Clone, PartialEq, thiserror::Error)]
pub enum LexicalError {
    #[error("Unexpected character: {0}")]
    UnexpectedCharacter(char),
    #[error("Unexpected end of input")]
    UnexpectedEndOfInput,
}

macro_rules! regex {
    ($pattern:expr) => {{
        static RE: Lazy<Regex> = Lazy::new(|| Regex::new($pattern).unwrap());
        &RE
    }};
}

// 成功: Ok(Some((Token, 消費したバイト数)))
// 失敗: Err(LexicalError)
// EOF: Ok(None)
type LexResult = std::result::Result<Option<(Token, usize)>, LexicalError>;

fn ok(token: Token, bytes_consumed: usize) -> LexResult {
    Ok(Some((token, bytes_consumed)))
}

fn err(e: LexicalError) -> LexResult {
    Err(e)
}

fn eof() -> LexResult {
    Ok(None)
}

// input からトークンをひとつ読み取り、トークンと消費したバイト数を返す。
pub fn lex(input: &str) -> LexResult {
    if input.is_empty() {
        return eof();
    }

    let re_whitespace = regex!(r"^[ \t\r\n]+");
    if let Some(m) = re_whitespace.find(input) {
        let r = lex(&input[m.end()..]);
        return match r {
            Ok(Some((token, bytes_consumed))) => ok(token, m.end() + bytes_consumed),
            _ => r,
        };
    }

    let re_identifier_or_keyword = regex!(r"^[a-zA-Z_][a-zA-Z0-9_]*");
    if let Some(m) = re_identifier_or_keyword.find(input) {
        let s = m.as_str();
        let token = match s {
            "true" => Token::True,
            "false" => Token::False,
            "null" => Token::Null,
            _ => Token::Identifier(s.to_owned()),
        };
        return ok(token, m.end());
    }

    let re_digits = regex!(r"^[0-9]+");
    if let Some(m) = re_digits.find(input) {
        let n = m.as_str().parse::<f64>().unwrap();
        return ok(Token::Number(n), m.end());
    }

    unimplemented!()
}

// バイトオフセットを (行, 列) に変換する。
// 行と列は 0 から始まる。
// line_breaks はソースコードの改行文字のバイトオフセットの配列である。
pub fn to_line_col(line_breaks: &[usize], pos: usize) -> (usize, usize) {
    let line = line_breaks.partition_point(|&x| x < pos);
    let col = if line == 0 {
        pos
    } else {
        pos - line_breaks[line - 1] - 1
    };
    (line, col)
}

#[test]
fn test_to_line_col() {
    let source_code = [
        "#include <stdio.h>",
        "",
        "int main(void) {",
        "  return 0;",
        "}",
    ].join("\n");

    let line_breaks: Vec<usize> = source_code
        .match_indices('\n')
        .map(|(i, _)| i)
        .collect();

    assert_eq!(to_line_col(&line_breaks, 0), (0, 0));
    assert_eq!(to_line_col(&line_breaks, 1), (0, 1));
    assert_eq!(to_line_col(&line_breaks, 18), (0, 18));
    assert_eq!(to_line_col(&line_breaks, 19), (1, 0));
    assert_eq!(to_line_col(&line_breaks, 20), (2, 0));
    assert_eq!(to_line_col(&line_breaks, 21), (2, 1));
    assert_eq!(to_line_col(&line_breaks, 36), (2, 16));
}
