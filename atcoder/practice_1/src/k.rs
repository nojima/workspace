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

    let mut prev_time = 0;
    let mut prev_x = 0;
    let mut prev_y = 0;
    let mut ok = true;

    let n: usize = reader.read();
    for _ in 0..n {
        let t: i32 = reader.read();
        let x: i32 = reader.read();
        let y: i32 = reader.read();

        let dt = t - prev_time;
        let dist = (x - prev_x).abs() + (y - prev_y).abs();

        if !(dt >= dist && (dt - dist) % 2 == 0) {
            ok = false;
        }

        prev_time = t;
        prev_x = x;
        prev_y = y;
    }

    println!("{}", if ok { "Yes" } else { "No" })
}
