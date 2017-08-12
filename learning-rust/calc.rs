use std::io::{self, Read, Write};
use std::process::exit;
use std::error::Error;
use std::fmt;

// 型宣言 ////////////////////////////////////////////////////////////////////////

// ParseError -----------------------------------

#[derive(Debug)]
struct ParseError {
    message: String,
}

impl Error for ParseError {
    fn description(&self) -> &str {
        return &self.message;
    }
}

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "ParseError: {}", self.message)
    }
}

// Node -----------------------------------------

#[derive(Debug)]
enum Node {
    Integer(i64),
    Add(Box<Node>, Box<Node>),
    Mul(Box<Node>, Box<Node>),
}

// alias ----------------------------------------

type ParseState<'a> = (Node, &'a str);
type ParseResult<'a> = Result<ParseState<'a>, ParseError>;

// パース関数 ////////////////////////////////////////////////////////////////////

fn uncons(s: &str) -> (char, &str) {
    let mut it = s.chars();
    if let Some(ch) = it.next() {
        (ch, it.as_str())
    } else {
        ('\0', s)
    }
}

// digit ::= [0-9]
fn parse_digit(s: &str) -> Result<(i64, &str), ParseError> {
    let (ch, rest) = uncons(s);
    match ch.to_digit(10) {
        Some(d) => Ok((d as i64, rest)),
        None => Err(ParseError{ message: "expected a digit".to_owned() }),
    }
}

// integer ::= digit | integer digit
fn parse_integer(s: &str) -> ParseResult {

    fn iter(s: &str, acc: i64) -> ParseResult {
        match parse_digit(s) {
            Ok((d, rest)) => iter(rest, 10 * acc + d),
            Err(_) => Ok((Node::Integer(acc), s)),
        }
    }

    let (d, rest) = parse_digit(s)?;
    iter(rest, d)
}

// factor ::= integer | '(' expression ')'
fn parse_factor(s: &str) -> ParseResult {
    let (ch, rest1) = uncons(s);
    match ch {
        '(' => {
            let (expr, rest2) = parse_expression(rest1)?;
            let (ch3, rest3) = uncons(rest2);
            if ch3 != ')' {
                return Err(ParseError{ message: "missing ')'".to_owned() });
            }
            Ok((expr, rest3))
        },
        _ => parse_integer(s),
    }
}

// term ::= factor | term '*' factor
fn parse_term(s: &str) -> ParseResult {

    fn iter(s: &str, acc: Node) -> ParseResult {
        let (ch, rest1) = uncons(s);
        match ch {
            '*' => {
                let (rhs, rest2) = parse_factor(rest1)?;
                iter(rest2, Node::Mul(Box::new(acc), Box::new(rhs)))
            },
            _ => Ok((acc, s)),
        }
    }

    let (factor, rest) = parse_factor(s)?;
    iter(rest, factor)
}

// expression := term | expression '+' term
fn parse_expression(s: &str) -> ParseResult {

    fn iter(s: &str, acc: Node) -> ParseResult {
        let (ch, rest1) = uncons(s);
        match ch {
            '+' => {
                let (rhs, rest2) = parse_term(rest1)?;
                iter(rest2, Node::Add(Box::new(acc), Box::new(rhs)))
            },
            _ => Ok((acc, s)),
        }
    }

    let (term, rest) = parse_term(s)?;
    iter(rest, term)
}

// 評価器 ////////////////////////////////////////////////////////////////////////

fn eval(node: &Node) -> i64 {
    match node {
        &Node::Integer(x) => x,
        &Node::Add(ref lhs, ref rhs) => eval(lhs) + eval(rhs),
        &Node::Mul(ref lhs, ref rhs) => eval(lhs) * eval(rhs),
    }
}

// その他 ////////////////////////////////////////////////////////////////////////

fn print_answer(answer: i64) {
    println!("Answer = {}", answer);
}

fn read_input() -> io::Result<String> {
    let mut buffer = String::new();
    io::stdin().read_to_string(&mut buffer)?;
    return Ok(buffer);
}

// TODO: あとで綺麗にする。
fn do_main() -> Result<(), Box<Error>> {
    let input = try!(read_input());
    let (node, rest) = try!(parse_expression(input.trim()));
    if !rest.is_empty() {
        let e = ParseError{ message: "unexpected token".to_owned() };
        return Err(From::from(e));
    }
    let answer = eval(&node);
    print_answer(answer);
    Ok(())
}

fn main() {
    exit(match do_main() {
        Ok(_) => 0,
        Err(e) => { writeln!(io::stderr(), "Error: {:?}", e).unwrap(); 1 },
    });
}
