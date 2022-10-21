mod core;
mod parse;
mod c;
mod compile;
mod collections;

use std::io::{self, prelude::*, stdin};

fn read_stdin() -> io::Result<String> {
    let mut ret = String::new();
    let mut last_line_empty = false;

    loop {
        let bytes_read = stdin().read_line(&mut ret)?;
        // This line is empty if we read only a "\n". It has 2 bytes.
        let this_line_empty = bytes_read <= 2;

        if last_line_empty && this_line_empty {
            break Ok(ret);
        }

        last_line_empty = this_line_empty;
    }
}

fn main() -> io::Result<()> {
    let source = read_stdin()?;
    let output = parse::parse(&source).expect("Failed to parse");
    dbg!(&output);
    let typ = output.infer_type().expect("Failed to infer type");
    dbg!(&typ);
    let code = c::generate(&typ);
    dbg!(&code);
    Ok(())
}
