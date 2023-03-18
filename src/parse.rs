use crate::ast::{ArrowType, Ast, Literal};
use crate::lex::{lex, LToken, NewLine, Symbol, Token, Keyword};
use crate::located::{Pos, Range};
use crate::name::Name;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Error {
    TermNotFound(Pos),
    UnclosedParenthesis {
        open: Pos,
        expected_close: Pos,
        found_close: Option<Pos>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct TokenReader<'source> {
    tokens: Vec<LToken<'source>>,
    index: usize,
    indent: usize,
    parens_depth: usize,
    errors: Vec<Error>,
}

impl<'source> TokenReader<'source> {
    pub fn new(tokens: Vec<LToken<'source>>) -> Self {
        Self {
            tokens,
            index: 0,
            indent: 0,
            parens_depth: 0,
            errors: Vec::new(),
        }
    }

    pub fn current(&self) -> Option<LToken<'source>> {
        self.tokens.get(self.index).cloned()
    }

    pub fn pop(&mut self) -> Option<LToken<'source>> {
        let ret = self.current();
        self.index += 1;
        // Update the indent tracker.
        let token: Option<Token> = ret.as_deref().cloned();
        if let Some(Token::NewLine(NewLine::NewLine { indent })) = token {
            self.indent = indent;
        } else if let Some(Token::Symbol(Symbol::CloseParen)) = token {
            self.parens_depth -= 1;
        } else if let Some(Token::Symbol(Symbol::OpenParen)) = token {
            self.parens_depth += 1;
        }
        // Update the parens tracker.
        ret
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

    fn pop_indent_helper(&mut self, predicate: impl FnOnce(usize, usize) -> bool) -> bool {
        let start_indent = self.indent;
        let init_state = self.clone();
        let ret = self
            .pop_token_newline()
            .map(|newline| match newline {
                NewLine::NewLine { indent } => predicate(indent, start_indent),
                NewLine::EmptyLine => self.pop_indent_in(),
            })
            .unwrap_or(false);
        if !ret {
            *self = init_state;
        }
        ret
    }

    pub fn pop_indent_in(&mut self) -> bool {
        self.pop_indent_helper(|indent, start_indent| indent > start_indent)
    }

    pub fn pop_indent_same(&mut self, to_indent: usize) -> bool {
        self.pop_indent_helper(|indent, _| indent == to_indent)
    }

    pub fn pop_indent(&mut self) -> bool {
        self.pop_indent_helper(|_, _| true)
    }

    pub fn error(&mut self, error: Error) {
        self.errors.push(error);
    }
}

/// Parses a program from a source code string.
pub fn parse(source: &str) -> Result<Ast, Vec<Error>> {
    let mut tokens = TokenReader::new(lex(source));

    // Read until start of term line.
    tokens.pop_indent_same(0);

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
        // Allow indenting in!
        tokens.pop_indent_in();
        let ret = term(tokens);
        return Ast::Arrow(ArrowType::Value, first_atom.into(), ret.into());
    }

    if tokens.pop_token_eq(Symbol::ThinArrow) {
        // Allow indenting in!
        tokens.pop_indent_in();
        let ret = term(tokens);
        return Ast::Arrow(ArrowType::Type, first_atom.into(), ret.into());
    }

    if tokens.pop_token_eq(Token::Symbol(Symbol::Colon)) {
        // Allow indenting in!
        tokens.pop_indent_in();
        let typ = term(tokens);
        return Ast::TypeAnnotation(first_atom.into(), typ.into());
    }

    // Then, parse a list of more atoms!
    let second_atom = atom_after_linebreak(tokens);
    let mut rest_of_applications = vec![];
    if second_atom.is_some() {
        while let Some(next_atom) = atom_after_linebreak(tokens) {
            rest_of_applications.push(next_atom);
        }
    }

    // Combine the atoms into a single term.
    let application_term = match second_atom {
        Some(second_atom) => Ast::Appl(first_atom.into(), second_atom.into(), rest_of_applications),
        None => first_atom,
    };

    // Is this a assign expression?
    if tokens.pop_token_eq(Symbol::Equal) {
        let start_indent = tokens.indent;
        tokens.pop_indent_in(); // Fine if this fails.
        let rhs = term(tokens);
        if !tokens.pop_indent_same(start_indent) {
            todo!("error: expected expression with same indent");
        }
        let ret = term(tokens);
        return Ast::Let(application_term.into(), rhs.into(), ret.into());
    }

    application_term
}

/// Parses an atom from the current position.
fn atom(tokens: &mut TokenReader) -> Option<Ast> {
    let start = tokens.get_range(tokens.index).0;

    if let Some(literal) = literal(tokens) {
        return Some(Ast::Literal(literal, (start..tokens.prev_range().1).into()));
    }

    if tokens.pop_token_eq(Symbol::OpenParen) {
        // Allow newlines after the opening parenthesis.
        tokens.pop_indent();

        // Parse the term.
        let term = term(tokens);

        // skip more linebreaks.
        tokens.pop_indent();
        
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
        return Some(Ast::Var(Name::from_str(ident), tokens.prev_range()));
    }

    None
}

fn atom_after_linebreak(tokens: &mut TokenReader) -> Option<Ast> {
    let initial_state = tokens.clone();

    tokens.pop_indent_same(tokens.indent);
    let atom = atom(tokens);

    // If parsing the atom failed, we go back to the initial state.
    if atom.is_none() {
        *tokens = initial_state;
    }

    atom
}

fn literal(tokens: &mut TokenReader) -> Option<Literal> {
    if let Some(string) = tokens.pop_token_string() {
        return Some(Literal::String(Name::from_str(string)));
    }

    if let Some(int) = tokens.pop_token_int() {
        return Some(Literal::Int(int));
    }

    if tokens.pop_token_eq(Token::Keyword(Keyword::Type)) {
        return Some(Literal::Type);
    }

    if tokens.pop_token_eq(Token::Keyword(Keyword::Prop)) {
        return Some(Literal::Prop);
    }

    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use indoc::indoc;

    fn r(x: impl Into<Range>) -> Range {
        x.into()
    }

    #[test]
    fn test_1() {
        let source = indoc! {r#"
            (x: str) => string-append x "!"
        "#};
        assert_eq!(
            parse(source),
            Ok(Ast::Arrow(
                ArrowType::Value,
                Ast::TypeAnnotation(
                    Ast::Var("x".into(), r(1..2)).into(),
                    Ast::Var("str".into(), r(4..7)).into()
                )
                .into(),
                Ast::Appl(
                    Ast::Var("string-append".into(), r(12..25)).into(),
                    Ast::Var("x".into(), r(26..27)).into(),
                    vec![Ast::Literal(Literal::String("!".into()), r(28..31))]
                )
                .into(),
            ))
        );
    }
}
