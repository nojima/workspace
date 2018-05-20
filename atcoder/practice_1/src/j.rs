use std::io::{Read, StdinLock};
use std::str::{from_utf8, FromStr};
use std::vec::Vec;

struct StdinReader<'a> {
    reader: StdinLock<'a>,
}

impl<'a> StdinReader<'a> {
    pub fn new(reader: StdinLock<'a>) -> StdinReader {
        StdinReader { reader: reader }
    }

    pub fn read<T: FromStr>(&mut self) -> T {
        fn is_whitespace(ch: u8) -> bool {
            ch == 0x20 || ch == 0x0a || ch == 0x0d
        }

        let token: Vec<u8> = self.reader
            .by_ref()
            .bytes()
            .map(|ch| ch.expect("failed to read a byte"))
            .skip_while(|ch| is_whitespace(*ch))
            .take_while(|ch| !is_whitespace(*ch))
            .collect();
        let token_str = from_utf8(&token)
            .unwrap_or_else(|_| panic!(format!("invalid utf8 sequence: {:?}", token)));
        token_str
            .parse()
            .unwrap_or_else(|_| panic!(format!("failed to parse input: {}", token_str)))
    }
}

fn ok(r: &str, patterns: &[&str]) -> bool {
    if r.is_empty() {
        return true;
    }
    for pattern in patterns {
        if r.starts_with(pattern) {
            return ok(&r[pattern.len()..], patterns);
        }
    }
    false
}

fn main() {
    let stdin = std::io::stdin();
    let mut reader = StdinReader::new(stdin.lock());

    let s: String = reader.read();

    let b = &s.bytes().rev().collect::<Vec<u8>>();
    let r = from_utf8(b).unwrap();

    let patterns = vec!["remaerd", "maerd", "resare", "esare"];

    println!("{}", if ok(r, &patterns) { "YES" } else { "NO" });
}
