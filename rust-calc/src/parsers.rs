use regex::Regex;

pub trait Parser<T>: Fn(&str) -> Option<(T, &str)> {}
impl<T, F> Parser<T> for F where F: Fn(&str) -> Option<(T, &str)> {}

// https://github.com/rust-lang/rust/issues/70263#issuecomment-623169045
fn generalize_lifetime<F, T>(f: F) -> F
where
    F: Fn(&str) -> Option<(T, &str)>,
{
    f
}

pub fn character(ch: char) -> impl Parser<char> {
    generalize_lifetime(move |s| {
        let mut chars = s.chars();
        match chars.next() {
            Some(c) if c == ch => Some((c, chars.as_str())),
            _ => None,
        }
    })
}

#[test]
fn test_character() {
    let parser = character('x');
    assert_eq!(parser("xabc"), Some(('x', "abc")));
    assert_eq!(parser("abc"), None);
    assert_eq!(parser("x"), Some(('x', "")));
}

pub fn digits(s: &str) -> Option<(i64, &str)> {
    let end = s.find(|ch: char| !ch.is_ascii_digit()).unwrap_or(s.len());
    if let Ok(n) = s[..end].parse() {
        Some((n, &s[end..]))
    } else {
        None
    }
}

#[test]
fn test_digits() {
    assert_eq!(digits("123 hello"), Some((123, " hello")));
    assert_eq!(digits("hello"), None);
    assert_eq!(digits("100"), Some((100, "")));
    assert_eq!(digits("abc"), None);
    assert_eq!(digits(""), None);
}

pub fn whitespaces(s: &str) -> Option<((), &str)> {
    let end = s
        .find(|ch: char| !ch.is_ascii_whitespace())
        .unwrap_or(s.len());
    Some(((), &s[end..]))
}

pub fn string(target: &'static str) -> impl Parser<()> {
    generalize_lifetime(move |s| {
        if s.starts_with(target) {
            let rest = &s[target.len()..];
            Some(((), rest))
        } else {
            None
        }
    })
}

#[test]
fn test_string() {
    let parser = string("hello");
    assert_eq!(parser("hello world"), Some(((), " world")));
    assert_eq!(parser("world hello"), None);
}

pub fn many<T>(parser: impl Parser<T>) -> impl Parser<Vec<T>> {
    generalize_lifetime(move |mut s| {
        let mut ret = vec![];
        while let Some((value, rest)) = parser(s) {
            ret.push(value);
            s = rest;
        }
        Some((ret, s))
    })
}

#[test]
fn test_many() {
    let parser = many(character('x'));
    assert_eq!(parser("xy"), Some((vec!['x'], "y")));
    assert_eq!(parser("xxxxyy"), Some((vec!['x', 'x', 'x', 'x'], "yy")));
    assert_eq!(parser("y"), Some((vec![], "y")));
}

pub fn join<T1, T2>(parser1: impl Parser<T1>, parser2: impl Parser<T2>) -> impl Parser<(T1, T2)> {
    generalize_lifetime(move |s| {
        parser1(s).and_then(|(v1, rest1)| parser2(rest1).map(|(v2, rest2)| ((v1, v2), rest2)))
    })
}

#[macro_export]
macro_rules! join {
    ($parser0:expr, $($parser:expr),*) => {{
        let p = $parser0;
        $(
            let p = crate::parsers::join(p, $parser);
        )*
        p
    }};
    // remove trailing commas
    ($($parser:expr),*, $(,)*) => {
        crate::join!($($parser),*)
    };
}

#[test]
fn test_join() {
    let parser = join(string("x="), digits);
    assert_eq!(parser("x=10, y=20"), Some((((), 10), ", y=20")));
    assert_eq!(parser("10=x"), None);
}

pub fn map<A, B>(parser: impl Parser<A>, f: impl Fn(A) -> B) -> impl Parser<B> {
    generalize_lifetime(move |s| parser(s).map(|(v, rest)| (f(v), rest)))
}

#[test]
fn test_map() {
    let parser = map(digits, |n| n * n);
    assert_eq!(parser("7"), Some((49, "")));
    assert_eq!(parser("hoge"), None)
}

pub fn bind<A, B, ParserB: Parser<B>>(
    parser: impl Parser<A>,
    f: impl Fn(A) -> ParserB,
) -> impl Parser<B> {
    generalize_lifetime(move |s| parser(s).and_then(|(v, rest)| f(v)(rest)))
}

pub fn alternative<T>(parser1: impl Parser<T>, parser2: impl Parser<T>) -> impl Parser<T> {
    generalize_lifetime(move |s| parser1(s).or_else(|| parser2(s)))
}

#[macro_export]
macro_rules! choice {
    ($parser0:expr, $($parser:expr),*) => {{
        let p = $parser0;
        $(
            let p = crate::parsers::alternative(p, $parser);
        )*
        p
    }};
    // remove trailing commas
    ($($parser:expr),*, $(,)*) => {
        crate::choice!($($parser),*)
    }
}

#[test]
fn test_choice() {
    let parser = choice![
        map(string("one"), |_| 1),
        map(string("two"), |_| 2),
        digits,
    ];
    assert_eq!(parser("one"), Some((1, "")));
    assert_eq!(parser("two"), Some((2, "")));
    assert_eq!(parser("123"), Some((123, "")));
    assert_eq!(parser("aaa"), None);
}

pub fn lexeme<T>(parser: impl Parser<T>) -> impl Parser<T> {
    generalize_lifetime(move |s| parser(s.trim_start()))
}

pub fn regex<T>(
    re: &'static Regex,
    f: impl Fn(&str) -> Option<T>,
) -> impl Parser<T> {
    generalize_lifetime(move |s| {
        re.find(s).and_then(|matched| {
            f(matched.as_str()).map(|value| {
                let rest = &s[matched.end()..];
                (value, rest)
            })
        })
    })
}

#[macro_export]
macro_rules! regex {
    ($pattern:expr, $f:expr) => {{
        use regex::Regex;
        use once_cell::sync::Lazy;
        static RE: Lazy<Regex> = Lazy::new(|| Regex::new($pattern).unwrap());
        crate::parsers::regex(&RE, $f)
    }};
}

#[test]
fn test_regex() {
    let parser = regex!("^(abc)+", |s| Some(s.to_owned()));
    assert_eq!(parser("abcabcdef"), Some(("abcabc".to_owned(), "def")))
}

pub fn separated<T, U>(
    parser: impl Parser<T>,
    separator: impl Parser<U>,
) -> impl Parser<Vec<T>> {
    generalize_lifetime(move |mut s| {
        let mut ret = vec![];

        match parser(s) {
            Some((value, rest)) => {
                ret.push(value);
                s = rest;
            }
            None => {
                return Some((ret, s));
            }
        }

        while let Some((_, rest)) = separator(s) {
            s = rest;
            match parser(s) {
                Some((value, rest)) => {
                    ret.push(value);
                    s = rest;
                }
                None => {
                    return None;
                }
            }
        }

        Some((ret, s))
    })
}
