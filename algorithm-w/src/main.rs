use std::rc::Rc;

use rustyline::{error::ReadlineError, DefaultEditor};

use crate::value::{Frame, Value};

mod ast;
mod eval;
mod lexer;
mod parser;
mod span;
mod symbol;
mod token;
mod value;

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
        if let Err(e) = do_eval(&line) {
            eprintln!("{e}");
            continue;
        }
    }
}

fn do_eval(input: &str) -> anyhow::Result<()> {
    let token_and_spans = lexer::lex(input)?;
    let tokens: Vec<_> = token_and_spans.into_iter().map(|(t, _)| t).collect();
    let ast = parser::parse(&tokens)?;
    println!("AST = {:?}", ast);
    let frame = Frame {
        parent: None,
        v_name: "false".into(),
        v_value: Value::Bool(false),
    };
    let value = eval::eval(&ast, Rc::new(frame))?;
    println!("Value = {:?}", value);
    Ok(())
}
