use std::io::stdin;

mod ast;
mod lexer;
mod parser;
mod span;
mod symbol;
mod token;

fn main() -> anyhow::Result<()> {
    let mut line = String::new();
    loop {
        line.clear();
        stdin().read_line(&mut line)?;

        let token_and_spans = lexer::lex(&line)?;
        let tokens: Vec<_> = token_and_spans.into_iter().map(|(t, _)| t).collect();
        let ast = parser::parse(&tokens)?;
        println!("{:?}", ast);
    }
}
