use std::cmp::{max, min};
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

fn main() {
    let stdin = std::io::stdin();
    let mut reader = StdinReader::new(stdin.lock());

    let a: i64 = reader.read();
    let b: i64 = reader.read();
    let c: i64 = reader.read();
    let x: i64 = reader.read();
    let y: i64 = reader.read();

    let mut min_cost = std::i64::MAX;

    for k in 0..(x + y + 1) {
        // ABピザを 2*k 個買う
        let i = max(x - k, 0);
        let j = max(y - k, 0);
        let cost = i * a + j * b + 2 * k * c;
        min_cost = min(min_cost, cost);
    }

    println!("{}", min_cost);
}
