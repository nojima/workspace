use parse_error::*;
use matcher::*;

fn uncons(s: &str) -> (char, &str) {
    let mut it = s.chars();
    match it.next() {
        Some(ch) => (ch, it.as_str()),
        None => ('\0', s),
    }
}

type ParseResult<'a> = Result<(Box<Matcher>, &'a str), ParseError>;

fn compile_character(pattern: &str) -> ParseResult {
    let (ch, rest) = uncons(pattern);
    match ch {
        '\0' | '|' | ')' => Ok((box ZeroMatcher::new(), pattern)),
        '.' => Ok((box AnyCharacterMatcher::new(), rest)),
        '(' => {
            let (matcher, rest) = compile_alternation(rest)?;
            let (paren, rest) = uncons(rest);
            if paren == ')' {
                Ok((matcher, rest))
            } else {
                Err(ParseError::new("unmatched parenthese"))
            }
        },
        '\\' => {
            let (escaped, rest) = uncons(rest);
            if escaped == '\0' {
                Err(ParseError::new("unexpected end of pattern"))
            } else {
                Ok((box CharacterMatcher::new(escaped), rest))
            }
        },
        _ => Ok((box CharacterMatcher::new(ch), rest)),
    }
}

fn compile_quantifier(pattern: &str) -> ParseResult {
    let (inner, rest1) = compile_character(pattern)?;
    let (ch, rest2) = uncons(rest1);
    if ch == '*' {
        Ok((box RepeatMatcher::new(inner), rest2))
    } else {
        Ok((inner, rest1))
    }
}

fn compile_concatenation(pattern: &str) -> ParseResult {
    let (mut matcher, mut rest) = compile_quantifier(pattern)?;

    loop {
        let (ch, _) = uncons(rest);
        if ch == '\0' || ch == '|' || ch == ')' {
            break;
        }
        let (m, rest3) = compile_quantifier(rest)?;
        rest = rest3;
        matcher = box ConcatenationMatcher::new(matcher, m);
    }

    Ok((matcher, rest))
}

fn compile_alternation(pattern: &str) -> ParseResult {
    let (mut matcher, mut rest) = compile_concatenation(pattern)?;

    loop {
        let (ch, rest2) = uncons(rest);
        if ch != '|' {
            break;
        }
        let (m, rest3) = compile_alternation(rest2)?;
        rest = rest3;
        matcher = box AlternationMatcher::new(matcher, m)
    }

    Ok((matcher, rest))
}

pub fn compile(pattern: &str) -> Result<Box<Matcher>, ParseError> {
    let (matcher, rest) = compile_alternation(pattern)?;
    if !rest.is_empty() {
        Err(ParseError::new("expected end of pattern"))
    } else {
        Ok(matcher)
    }
}
