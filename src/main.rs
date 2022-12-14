mod c;
mod cli;
mod compile;
mod core;
mod name;
mod parse;

use cli::{parse_args, Action, Cli};
use std::{io, path::PathBuf};

use io::Result as ioRes;

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

fn read_stdin() -> ioRes<String> {
    let mut ret = String::new();
    let mut last_line_empty = false;

    loop {
        let bytes_read = io::stdin().read_line(&mut ret)?;
        // This line is empty if we read only a "\n". It has 2 bytes.
        let this_line_empty = bytes_read <= 2;

        if last_line_empty && this_line_empty {
            break Ok(ret);
        }

        last_line_empty = this_line_empty;
    }
}

fn read_file_or_stdin(filename: Option<PathBuf>) -> io::Result<String> {
    if let Some(filename) = filename {
        std::fs::read_to_string(filename)
    } else {
        read_stdin()
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
                }
                let expr = dbg!(parse::parse(&source).expect("Failed to parse"));
                let typ = dbg!(expr.infer_type().expect("Failed to infer type"));
                println!("Type is {}", typ);
                let evaluated = expr.eval();
                println!("{}", evaluated);
                Ok(true)
            })
        }
        Action::Eval { filename } => {
            todo!()
        }
        Action::Compile { filename } => {
            todo!()
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
