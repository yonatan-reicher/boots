mod ast;
mod ast_to_term;
mod c;
mod cli;
mod compile;
mod engine;
mod global;
mod lex;
mod located;
mod name;
mod parse;
mod term;
mod yes_no;

use cli::{parse_args, Action, Cli};
use std::fs;
use std::io::{self, Result as IORes};

use crate::term::{ArrowKind, PTerm, Term, Literal};

mod repl {
    use super::*;
    use std::io::Write;

    /// Gets a single line of code from the user.
    fn get_line(buffer: &mut String) -> IORes<usize> {
        print!(">>> ");
        io::stdout().flush()?;
        io::stdin().read_line(buffer)
    }

    /// Reads a section of code, that may be multiple lines.
    fn read_snippit(buffer: &mut String) -> IORes<usize> {
        // For now, read until an empty line.
        // This line is empty if we read only a "\n". It has 2 bytes.
        let bytes = get_line(buffer)?;
        Ok(if bytes != 2 {
            bytes + read_snippit(buffer)?
        } else {
            bytes
        })
    }

    pub fn run(mut eval: impl FnMut(&str) -> IORes<bool>) -> IORes<()> {
        let mut buffer = String::new();
        loop {
            read_snippit(&mut buffer)?;

            let source = buffer.trim();

            let cont = eval(source)?;

            if !cont {
                break Ok(());
            }

            buffer.clear();
        }
    }
}

fn main() -> IORes<()> {
    let Cli { action } = parse_args();
    let mut engine = engine::Engine::new();

    engine.add_variable(
        "string-append".into(),
        Term::Arrow {
            kind: ArrowKind::Type,
            param_name: "_".into(),
            ty: Literal::Str.into(),
            body: Term::Arrow {
                kind: ArrowKind::Type,
                param_name: "_".into(),
                ty: Literal::Str.into(),
                body: Literal::Str.into(),
            }
            .into(),
        }
        .into(),
        Literal::StringAppend.into(),
    );

    engine.add_variable("str".into(), Literal::Type.into(), Literal::Str.into());

    match action {
        Action::Eval { filename: None } => {
            // Begin a repl!
            repl::run(|source| {
                if source == "q" {
                    return Ok(false);
                } else if source.chars().all(char::is_whitespace) {
                    return Ok(true);
                }
                let ast = parse::parse(source).expect("Failed to parse");
                let expr: PTerm = ast_to_term::ast_to_term(&ast).unwrap();
                let typ = engine
                    .infer_type(expr.clone())
                    .expect("Failed to infer type");
                println!("Type is {typ}");
                let evaluated = engine.eval(expr);
                println!("{evaluated}");
                Ok(true)
            })
        }
        Action::Eval {
            filename: Some(filename),
        } => {
            let source = fs::read_to_string(filename)?;
            let ast = parse::parse(&source).unwrap();
            let expr: PTerm = ast_to_term::ast_to_term(&ast).unwrap();
            let ty = engine.infer_type(expr.clone()).unwrap();
            let evaluated = engine.eval(expr);
            println!("{evaluated}");
            println!("Is of type:");
            println!("{ty}");
            Ok(())
        }
        Action::Compile { filename } => {
            let source = fs::read_to_string(filename)?;
            let ast = parse::parse(&source).unwrap();
            let expr: PTerm = ast_to_term::ast_to_term(&ast).unwrap();
            let _ty = engine.infer_type(expr.clone()).unwrap();
            let evaluated = engine.eval(expr);
            println!("{evaluated}");
            let program = engine.compile(evaluated);
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
