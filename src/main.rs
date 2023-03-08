mod c;
mod cli;
mod compile;
mod core;
mod global;
mod name;
mod parse;

use cli::{parse_args, Action, Cli};
use std::fs;
use std::io;

use io::Result as ioRes;

use crate::core::Term;

mod repl {
    use super::*;
    use std::io::Write;

    /// Gets a single line of code from the user.
    fn get_line(buffer: &mut String) -> ioRes<usize> {
        print!(">>> ");
        io::stdout().flush()?;
        io::stdin().read_line(buffer)
    }

    /// Reads a section of code, that may be multiple lines.
    fn read_snippit(buffer: &mut String) -> ioRes<usize> {
        // For now, read until an empty line.
        // This line is empty if we read only a "\n". It has 2 bytes.
        let bytes = get_line(buffer)?;
        Ok(if bytes != 2 {
            bytes + read_snippit(buffer)?
        } else {
            bytes
        })
    }

    pub fn run(mut eval: impl FnMut(&str) -> ioRes<bool>) -> ioRes<()> {
        let mut buffer = String::new();
        loop {
            read_snippit(&mut buffer)?;

            let source = buffer.trim();

            let cont = eval(&source)?;

            if !cont {
                break Ok(());
            }

            buffer.clear();
        }
    }
}

fn main() -> ioRes<()> {
    let Cli { action } = parse_args();

    match action {
        Action::Eval { filename: None } => {
            // Begin a repl!
            repl::run(|source| {
                if source == "q" {
                    return Ok(false);
                } else if source.chars().all(char::is_whitespace) {
                    return Ok(true);
                }
                let expr = dbg!(parse::parse(&source).expect("Failed to parse"));
                let typ = dbg!(expr.infer_type().expect("Failed to infer type"));
                println!("Type is {}", typ);
                let evaluated = Term::eval_or(expr.into());
                println!("{}", evaluated);
                Ok(true)
            })
        }
        Action::Eval {
            filename: Some(filename),
        } => {
            let source = fs::read_to_string(filename)?;
            let expr = parse::parse(&source).unwrap();
            let ty = expr.infer_type().unwrap();
            let evaluated = Term::eval_or(expr.into());
            println!("{}", evaluated);
            println!("Is of type:");
            println!("{}", ty);
            Ok(())
        }
        Action::Compile { filename } => {
            let source = fs::read_to_string(filename)?;
            let expr = parse::parse(&source).unwrap();
            let _ty = expr.infer_type().unwrap();
            let evaluated = Term::eval_or(expr.into());
            println!("{}", evaluated);
            let program = compile::compile(evaluated.into());
            println!("{}", program.to_code());
            Ok(())
        }
    }
}

/*
fn main() -> io::Result<()> {
    let source = read_stdin()?;
    let output = dbg!(parse::parse(&source).expect("Failed to parse"));
    let typ = dbg!(output.infer_type().expect("Failed to infer type"));
    let c = dbg!(compile::compile(&output));
    let code = c.to_code();
    println!("{}", code);
    Ok(())
}
*/
