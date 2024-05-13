pub trait Parser {
    type Output;
    fn parse<'a>(&self, s: &'a str) -> Option<(Self::Output, &'a str)>;

    fn map<B, F>(self, f: F) -> Map<Self, F>
    where
        Self: Sized,
        F: Fn(Self::Output) -> B,
    {
        Map { parser: self, f }
    }
}

pub struct Map<P, F> {
    parser: P,
    f: F,
}

impl<A, B, P, F> Parser for Map<P, F>
where
    P: Parser<Output = A>,
    F: Fn(A) -> B,
{
    type Output = B;
    fn parse<'a>(&self, s: &'a str) -> Option<(Self::Output, &'a str)> {
        self.parser
            .parse(s)
            .map(|(value, rest)| ((self.f)(value), rest))
    }
}

impl<F, T> Parser for F
where
    F: Fn(&str) -> Option<(T, &str)>,
{
    type Output = T;
    fn parse<'a>(&self, s: &'a str) -> Option<(Self::Output, &'a str)> {
        self(s)
    }
}

// https://github.com/rust-lang/rust/issues/70263#issuecomment-623169045
fn generalize_lifetime<F, T>(f: F) -> F
where
    F: Fn(&str) -> Option<(T, &str)>,
{
    f
}

fn dummy<T>(f: impl Fn(&str) -> Option<(T, &str)>) -> impl Parser<Output = T> {
    f
}

fn digits(s: &str) -> Option<(i64, &str)> {
    let end = s.find(|ch: char| !ch.is_ascii_digit()).unwrap_or(s.len());
    if let Ok(n) = s[..end].parse() {
        Some((n, &s[end..]))
    } else {
        None
    }
}

fn digits_(s: &str) -> Option<(i64, &str)> {
    lexeme(digits).parse(s)
}

fn lexeme<T>(parser: impl Parser<Output = T>) -> impl Parser<Output = T> {
    generalize_lifetime(move |s: &str| {
        parser.parse(s).map(|(value, rest)| {
            // skip whitespaces
            let k = rest
                .find(|ch: char| !ch.is_whitespace())
                .unwrap_or(rest.len());
            dbg!(k);
            (value, &rest[k..])
        })
    })
}

#[test]
fn test_lexeme() {
    let parser = lexeme(digits);
    assert_eq!(parser.parse("123 hello"), Some((123, "hello")));
    assert_eq!(parser.parse("hello"), None);
}
