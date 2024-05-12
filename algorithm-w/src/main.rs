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
mod types;
mod typing;
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
    let (env, t) = typing::primary_type(&ast)?;
    println!("Env = {:?}", env);
    println!("Type = {}", t);
    let value = eval::eval(&ast, Rc::new(frame))?;
    println!("Value = {:?}", value);
    Ok(())
}

#[cfg(test)]
mod tests {
    use std::rc::Rc;

    use crate::{
        eval, lexer, parser,
        value::{Frame, Value},
    };

    fn doit(input: &str) -> anyhow::Result<Value> {
        let token_and_spans = lexer::lex(input)?;
        let tokens: Vec<_> = token_and_spans.into_iter().map(|(t, _)| t).collect();
        let ast = parser::parse(&tokens)?;
        let frame = Frame {
            parent: None,
            v_name: "false".into(),
            v_value: Value::Bool(false),
        };
        let value = eval::eval(&ast, Rc::new(frame))?;
        Ok(value)
    }

    #[test]
    fn test() -> anyhow::Result<()> {
        assert_eq!(Value::Integer(42), doit("42")?);
        assert_eq!(Value::Integer(7), doit("3 + 4")?);
        assert_eq!(Value::Bool(true), doit("true")?);
        assert_eq!(Value::Bool(false), doit("false")?);
        assert_eq!(Value::Bool(true), doit("0 == 0")?);
        assert_eq!(Value::Bool(false), doit("0 == 1")?);
        assert_eq!(Value::Integer(2), doit("if 1 == 1 then 2 else 3")?);
        assert_eq!(Value::Integer(3), doit("if 1 == 2 then 2 else 3")?);
        assert_eq!(Value::Integer(42), doit("([x] x) 42")?);
        assert_eq!(Value::Integer(5), doit("([x][y] x+y+y) 1 2")?);
        Ok(())
    }
}
