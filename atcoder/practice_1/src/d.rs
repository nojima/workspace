use std::cmp::min;
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

    let mut min_shift_count = 100;

    let n: usize = reader.read();
    for _i in 0..n {
        let mut a: i32 = reader.read();

        let mut shift_count = 0;
        while a % 2 == 0 {
            a /= 2;
            shift_count += 1;
        }

        min_shift_count = min(min_shift_count, shift_count);
    }

    println!("{}", min_shift_count);
}
