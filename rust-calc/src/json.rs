use std::collections::HashMap;

use crate::parsers;

#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    Null,
    False,
    True,
    Number(f64),
    String(String),
    Array(Vec<Value>),
    Object(HashMap<String, Value>),
}

fn null(s: &str) -> Option<(Value, &str)> {
    let p = parsers::lexeme(parsers::string("null"));
    let p = parsers::map(p, |_| Value::Null);
    p(s)
}

fn false_(s: &str) -> Option<(Value, &str)> {
    let p = parsers::lexeme(parsers::string("false"));
    let p = parsers::map(p, |_| Value::False);
    p(s)
}

fn true_(s: &str) -> Option<(Value, &str)> {
    let p = parsers::lexeme(parsers::string("true"));
    let p = parsers::map(p, |_| Value::True);
    p(s)
}

fn number(s: &str) -> Option<(Value, &str)> {
    const PATTERN: &str = r"^-?(0|[1-9][0-9]*)(\.[0-9]+)?([eE][+-]?[0-9]+)?";
    let p = crate::regex!(PATTERN, |s| s.parse::<f64>().ok());
    let p = parsers::lexeme(p);
    let p = parsers::map(p, |x| Value::Number(x));
    p(s)
}

#[test]
fn test_number() {
    assert_eq!(number("0"), Some((Value::Number(0.0), "")));
    assert_eq!(number("1"), Some((Value::Number(1.0), "")));
    assert_eq!(number("10"), Some((Value::Number(10.0), "")));
    assert_eq!(number("-1"), Some((Value::Number(-1.0), "")));
    assert_eq!(number("0.0"), Some((Value::Number(0.0), "")));
    assert_eq!(number("0.1"), Some((Value::Number(0.1), "")));
    assert_eq!(number("3.14"), Some((Value::Number(3.14), "")));
    assert_eq!(number("1.23e-4"), Some((Value::Number(1.23e-4), "")));
    assert_eq!(number("1.23e10"), Some((Value::Number(1.23e10), "")));
    assert_eq!(number("hoge"), None);
    assert_eq!(number("a123"), None);
    assert_eq!(number(""), None);
}

fn string_raw(s: &str) -> Option<(String, &str)> {
    // string = '"' character* '"'
    let p = crate::join![
        parsers::character('"'),
        parsers::many(character),
        parsers::character('"'),
    ];
    let p = parsers::lexeme(p);
    let p = parsers::map(p, |((_, chars), _)| {
        chars.into_iter().collect()
    });
    p(s)
}

fn string(s: &str) -> Option<(Value, &str)> {
    parsers::map(string_raw, Value::String)(s)
}

#[test]
fn test_string() {
    assert_eq!(
        string(r#""hello, world!!""#),
        Some((Value::String("hello, world!!".to_string()), "")),
    )
}

fn character(s: &str) -> Option<(char, &str)> {
    // character = <Any codepoint except " or \ or control characters>
    //           | '\u' <4 hex digits>
    //           | '\"' | '\\' | '\/' | '\b' | '\f' | '\n' | '\r' | '\t'
    crate::choice![
        crate::regex!(r#"^[^"\\[:cntrl:]]"#, |s| s.chars().next()),
        crate::regex!(r#"^\\u[0-9a-fA-F]{4}"#, hex_code),
        crate::regex!(r#"^\\."#, escape),
    ](s)
}

fn hex_code(code: &str) -> Option<char> {
    code.strip_prefix(r"\u").and_then(|hex|
        u32::from_str_radix(hex, 16).ok().and_then(|cp|
            char::from_u32(cp)
        )
    )
}

fn escape(s: &str) -> Option<char> {
    match s {
        r#"\""# => Some('"'),
        r#"\\"# => Some('\\'),
        r#"\/"# => Some('/'),
        r#"\b"# => Some('\x08'),
        r#"\f"# => Some('\x0C'),
        r#"\n"# => Some('\n'),
        r#"\r"# => Some('\r'),
        r#"\t"# => Some('\t'),
        _ => None // undefined escape sequence
    }
}

fn array(s: &str) -> Option<(Value, &str)> {
    let p = crate::join![
        parsers::lexeme(parsers::character('[')),
        parsers::separated(json_value, parsers::lexeme(parsers::character(','))),
        parsers::lexeme(parsers::character(']')),
    ];
    let p = parsers::map(p, |((_, values), _)| Value::Array(values));
    p(s)
}

fn object(s: &str) -> Option<(Value, &str)> {
    let p = crate::join![
        parsers::lexeme(parsers::character('{')),
        parsers::separated(key_value, parsers::lexeme(parsers::character(','))),
        parsers::lexeme(parsers::character('}')),
    ];
    let p = parsers::map(p, |((_, key_values), _)| {
        let h = HashMap::from_iter(key_values.into_iter());
        Value::Object(h)
    });
    p(s)
}

fn key_value(s: &str) -> Option<((String, Value), &str)> {
    // key_value = string ':' json_value
    let p = crate::join![
        string_raw,
        parsers::lexeme(parsers::character(':')),
        json_value,
    ];
    let p = parsers::map(p, |((key, _), value)| (key, value));
    p(s)
}

fn json_value(s: &str) -> Option<(Value, &str)> {
    crate::choice![
        null,
        false_,
        true_,
        number,
        string,
        array,
        object,
    ](s)
}

pub fn parse(s: &str) -> Option<Value> {
    json_value(s).and_then(|(value, rest)| {
        if rest.chars().all(|c| c.is_ascii_whitespace()) {
            Some(value)
        } else {
            None
        }
    })
}
