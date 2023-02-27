use clap::{Parser, Subcommand};
use std::path::PathBuf;

#[derive(Parser)]
#[command(
    author = "Yonatan Reicher",
    version = "0.0.1",
    about = "A test compiler from ML-like functional language to C."
)]
pub struct Cli {
    #[command(subcommand)]
    pub action: Action,
}

#[derive(Subcommand)]
pub enum Action {
    Eval { filename: Option<PathBuf> },
    Compile { filename: PathBuf },
}

pub fn parse_args() -> Cli {
    Cli::parse()
}
