use crate::ast::{ArrowType, Ast, Literal};
use crate::lex::{lex, LToken, NewLine, Symbol, Token, Keyword};
use crate::located::{Pos, Range};

#[derive(Debug, Clone)]
pub enum Error {
    TermNotFound(Pos),
    UnclosedParenthesis {
        open: Pos,
        expected_close: Pos,
        found_close: Option<Pos>,
    },
}

struct TokenReader<'source> {
    tokens: Vec<LToken<'source>>,
    index: usize,
    errors: Vec<Error>,
}

impl<'source> TokenReader<'source> {
    pub fn new(tokens: Vec<LToken<'source>>) -> Self {
        Self {
            tokens,
            index: 0,
            errors: Vec::new(),
        }
    }

    pub fn current(&self) -> Option<LToken<'source>> {
        self.tokens.get(self.index).cloned()
    }

    pub fn pop(&mut self) -> Option<LToken<'source>> {
        let token = self.current();
        self.index += 1;
        token
    }

    pub fn pop_token(&mut self) -> Option<Token<'source>> {
        self.pop().map(|t| t.0)
    }

    pub fn curr_token(&self) -> Option<Token<'source>> {
        self.current().map(|t| t.0)
    }

    pub fn get_range(&self, index: usize) -> Range {
        self.tokens
            .get(index)
            .map(|t| t.1)
            .or(self.tokens.last().map(|t| (t.1 .1..t.1 .1).into()))
            .unwrap_or((0..0).into())
    }

    pub fn curr_range(&self) -> Range {
        self.get_range(self.index)
    }

    pub fn prev_range(&self) -> Range {
        self.get_range(self.index.saturating_sub(1))
    }

    pub fn pop_token_eq<'a>(&mut self, token: impl Into<Token<'a>>) -> bool {
        if self.curr_token() == Some(token.into()) {
            self.pop_token();
            true
        } else {
            false
        }
    }

    pub fn pop_token_string(&mut self) -> Option<&'source str> {
        if let Some(Token::String(string)) = self.curr_token() {
            self.pop_token();
            Some(string)
        } else {
            None
        }
    }

    pub fn pop_token_ident(&mut self) -> Option<&'source str> {
        if let Some(Token::Ident(ident)) = self.curr_token() {
            self.pop_token();
            Some(ident)
        } else {
            None
        }
    }

    pub fn pop_token_int(&mut self) -> Option<i32> {
        if let Some(Token::Int(int)) = self.curr_token() {
            self.pop_token();
            Some(int)
        } else {
            None
        }
    }

    pub fn pop_token_newline(&mut self) -> Option<NewLine> {
        if let Some(Token::NewLine(newline)) = self.curr_token() {
            self.pop_token();
            Some(newline)
        } else {
            None
        }
    }

    pub fn error(&mut self, error: Error) {
        self.errors.push(error);
    }
}

/// Parses a program from a source code string.
pub fn parse(source: &str) -> Result<Ast, Vec<Error>> {
    let mut tokens = TokenReader::new(lex(source));

    // For now just parse a single term.
    let the_term = term(&mut tokens);
    if tokens.errors.is_empty() {
        Ok(the_term)
    } else {
        Err(tokens.errors)
    }
}

/// Parses a term from the current position.
fn term(tokens: &mut TokenReader) -> Ast {
    let start = tokens.curr_range().0;

    // First, parse an atom.
    let first_atom = match atom(tokens) {
        Some(tokens) => tokens,
        None => {
            tokens.error(Error::TermNotFound(start));
            return Ast::Error;
        }
    };

    if tokens.pop_token_eq(Symbol::FatArrow) {
        let ret = term(tokens);
        return Ast::Arrow(ArrowType::Value, first_atom.into(), ret.into());
    }

    if tokens.pop_token_eq(Symbol::ThinArrow) {
        let ret = term(tokens);
        return Ast::Arrow(ArrowType::Type, first_atom.into(), ret.into());
    }

    if tokens.pop_token_eq(Token::Symbol(Symbol::Colon)) {
        let typ = term(tokens);
        return Ast::TypeAnnotation(first_atom.into(), typ.into());
    }

    // Then, parse a list of more atoms!
    let mut applications = vec![];
    while let Some(next_atom) = atom(tokens) {
        applications.push(next_atom);
    }

    let applicationTerm = applications
        .into_iter()
        .fold(first_atom, |acc, atom| Ast::Appl(acc.into(), atom.into()))

    // Is this a assign expression?
    if tokens.pop_token_eq(Symbol::Equal) {
        let rhs = term(tokens);
        return Ast::Let(applictionTerm
    }

    applicationTerm
}

/// Parses an atom from the current position.
fn atom(tokens: &mut TokenReader) -> Option<Ast> {
    let start = tokens.get_range(tokens.index).0;

    if let Some(literal) = literal(tokens) {
        return Some(Ast::Literal(literal));
    }

    if tokens.pop_token_eq(Symbol::OpenParen) {
        let term = term(tokens);
        if !tokens.pop_token_eq(Symbol::CloseParen) {
            let expected_close = tokens.get_range(tokens.index).0;
            // Try to find where the parenthesis is closed.
            while !matches!(
                tokens.curr_token(),
                None | Some(Token::Symbol(Symbol::CloseParen))
            ) {
                tokens.pop_token();
            }
            let found_close = tokens.current().map(|t| t.1 .1);
            tokens.error(Error::UnclosedParenthesis {
                open: start,
                expected_close,
                found_close,
            });
        }
        return Some(term);
    }

    if let Some(ident) = tokens.pop_token_ident() {
        return Some(Ast::Var(ident.into(), tokens.prev_range()));
    }

    None
}

fn literal(tokens: &mut TokenReader) -> Option<Literal> {
    if let Some(string) = tokens.pop_token_string() {
        return Some(Literal::String(string.to_owned()));
    }

    if let Some(int) = tokens.pop_token_int() {
        return Some(Literal::Int(int));
    }

    None
}
