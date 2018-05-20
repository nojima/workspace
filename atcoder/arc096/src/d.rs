use std::cmp::max;
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

fn rank(v: &[i64]) -> Vec<usize> {
    let mut indexed: Vec<(usize, &i64)> = v.iter().enumerate().collect();
    indexed.sort_by_key(|t| -t.1);
    indexed.iter().map(|t| t.0).collect()
}

fn solve(n: usize, c: i64, xs: &[i64], vs: &[i64]) -> i64 {
    // value[dir][n] = dir の方向に歩いて n 個の寿司を食べた時の正味栄養価
    let mut value: Vec<Vec<i64>> = vec![vec![0; n + 1]; 2];
    let mut max_value = 0;
    for dir in 0..2 {
        for i in 1..(n + 1) {
            let curr = if dir == 0 { i } else { n - i + 1 };
            let prev = if dir == 0 { curr - 1 } else { curr + 1 };
            value[dir][i] = value[dir][i - 1] + vs[curr] - (xs[curr] - xs[prev]).abs();
            max_value = max(max_value, value[dir][i]);
        }
    }

    let ranking = rank(&value[0]);

    // 半時計回りにm2個食べ、引き返して時計回りにm1個食べる場合
    let mut ri = 0;
    let mut m1 = ranking[ri];
    for m2 in 1..n {
        // 与えられたm2に対して最良のm1を見つける
        while m1 + m2 > n {
            ri += 1;
            m1 = ranking[ri];
        }
        let v = value[0][m1] + value[1][m2] - (c - xs[(n + 1) - m2]);
        max_value = max(max_value, v);
    }

    max_value
}

fn main() {
    let stdin = std::io::stdin();
    let mut reader = StdinReader::new(stdin.lock());

    let n: usize = reader.read();
    let c: i64 = reader.read();

    let (mut xs, mut vs) = {
        let mut a: Vec<(i64, i64)> = Vec::new();
        a.push((0, 0));
        a.push((c, 0));
        for _ in 0..n {
            let x: i64 = reader.read();
            let v: i64 = reader.read();
            a.push((x, v));
        }
        a.sort();
        let xs: Vec<i64> = a.iter().map(|t| t.0).collect();
        let vs: Vec<i64> = a.iter().map(|t| t.1).collect();
        (xs, vs)
    };

    let max_value1 = solve(n, c, &xs, &vs);

    // 反転させる
    xs.reverse();
    vs.reverse();
    for x in xs.iter_mut() {
        *x = c - *x
    }

    let max_value2 = solve(n, c, &xs, &vs);

    println!("{}", max(max_value1, max_value2));
}
