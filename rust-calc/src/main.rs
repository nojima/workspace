mod parsers;
mod json;

use anyhow::Result;
use std::io::{self, Write};

fn print_prompt() -> io::Result<()> {
    print!("json> ");
    io::stdout().flush()?;
    Ok(())
}

fn read_line() -> io::Result<Option<String>> {
    let mut input = String::new();
    match io::stdin().read_line(&mut input)? {
        0 => Ok(None),
        _ => Ok(Some(input)),
    }
}

fn do_something(line: &str) -> Result<()> {
    match crate::json::parse(line) {
        Some(value) => {
            print!("{:?}\n\n", value);
        }
        None => {
            eprintln!("parse error");
        }
    }
    Ok(())
}

fn main() -> Result<()> {
    loop {
        print_prompt()?;
        match read_line()? {
            Some(line) => {
                do_something(&line)?;
            }
            None => {
                println!("\nByebye!");
                return Ok(());
            }
        }
    }
}
