use rustyline::{error::ReadlineError, DefaultEditor};

mod ast;
mod lexer;
mod parser;
mod span;
mod symbol;
mod token;

fn main() -> anyhow::Result<()> {
    let mut rl = DefaultEditor::new()?;
    loop {
        let readline = rl.readline("expr> ");
        let line = match readline {
            Ok(line) => line,
            Err(ReadlineError::Eof) => return Ok(()),
            Err(e) => {
                eprintln!("{e}");
                continue;
            }
        };
        let _ = rl.add_history_entry(line.as_str());
        if let Err(e) = eval(&line) {
            eprintln!("{e}");
            continue;
        }
    }
}

fn eval(input: &str) -> anyhow::Result<()> {
    let token_and_spans = lexer::lex(input)?;
    let tokens: Vec<_> = token_and_spans.into_iter().map(|(t, _)| t).collect();
    let ast = parser::parse(&tokens)?;
    println!("{:?}", ast);
    Ok(())
}
