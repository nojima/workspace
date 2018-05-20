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

fn f_50(c: i32, x: i32) -> i64 {
    if c * 50 >= x {
        1
    } else {
        0
    }
}

fn f_100(b: i32, c: i32, x: i32) -> i64 {
    let mut sum: i64 = 0;
    for i in 0..(b + 1) {
        if x - i * 100 >= 0 {
            sum += f_50(c, x - i * 100);
        }
    }
    sum
}

fn f_500(a: i32, b: i32, c: i32, x: i32) -> i64 {
    let mut sum: i64 = 0;
    for i in 0..(a + 1) {
        if x - i * 500 >= 0 {
            sum += f_100(b, c, x - i * 500);
        }
    }
    sum
}

fn main() {
    let stdin = std::io::stdin();
    let mut reader = StdinReader::new(stdin.lock());

    let a: i32 = reader.read();
    let b: i32 = reader.read();
    let c: i32 = reader.read();
    let x: i32 = reader.read();

    println!("{}", f_500(a, b, c, x));
}
