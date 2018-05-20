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

    let n: i32 = reader.read();
    let y: i32 = reader.read::<i32>() / 1000;

    for i1 in 0..(n + 1) {
        for i2 in 0..(n - i1 + 1) {
            let i3 = n - i2 - i1;
            if 10 * i1 + 5 * i2 + i3 == y {
                println!("{} {} {}", i1, i2, i3);
                return;
            }
        }
    }
    println!("-1 -1 -1");
}
