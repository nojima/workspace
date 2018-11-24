#![feature(box_syntax)]

extern crate either;
extern crate failure;

mod matcher;
mod parse_error;
mod parser;

fn regexp_match<'a, 'b>(pattern: &'a str, s: &'b str) -> Option<&'b str> {
    let matcher = parser::compile(pattern).expect("invalid pattern");
    let mut it = matcher.matches(s);
    it.next().map(|n| &s[..n])
}

#[test]
fn test_regexp() {
    let cases = vec![
        ("", "abc", Some("")),
        ("", "", Some("")),
        ("hello", "hello", Some("hello")),
        ("hello", "world", None),
        ("...", "Beer", Some("Bee")),
        ("...", "He", None),
        ("foo|bar", "barxxx", Some("bar")),
        ("foo|bar", "buzzxxx", None),
        ("a*", "aaaaa", Some("aaaaa")),
        ("a*", "bbbbb", Some("")),
        ("c(abc)*", "cabcabcd", Some("cabcabc")),
        ("c(abc)*", "cabacaabcd", Some("c")),
        (
            "(hello|world)*",
            "hellohelloworldhelloheywww",
            Some("hellohelloworldhello"),
        ),
        (
            ".*Foo.*Bar",
            "This is Foo and that is Bar.",
            Some("This is Foo and that is Bar"),
        ),
        (".*Foo.*Bar", "This is Bar and that is Foo.", None),
        ("(0|1|2|3|4|5|6|7|8|9)* yen", "972 yen.", Some("972 yen")),
        ("(0|1|2|3|4|5|6|7|8|9)* yen", "972 dollers.", None),
        (
            "c(a*b*)*d",
            "caaabbbbbbabaaabdaaaaa",
            Some("caaabbbbbbabaaabd"),
        ),
        ("(a|b)(a|b)*|c", "cabab", Some("c")),
        (r"\(foo\|bar\)\\\\", r"(foo|bar)\\", Some(r"(foo|bar)\\")),
    ];

    for (pattern, s, expected) in cases {
        assert_eq!(expected, regexp_match(pattern, s));
    }
}
