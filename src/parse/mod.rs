use std::rc::Rc;

use crate::core::*;
use crate::name::Name;

#[derive(Debug, Clone)]
pub enum Error {
    TermNotFound,
    UnclosedParenthesis,
    ExpectedTypeAnnotation { found: Term },
    ExpectedNameInParameter { found: Term },
}

#[derive(Debug, Clone, Copy)]
pub enum Keyword {
    Prop,
    Type,
}

#[derive(Debug)]
enum IdentifierOrKeyword<'source> {
    Identifier(&'source str),
    Keyword(Keyword),
}

struct State<'source> {
    index: usize,
    line: usize,
    column: usize,
    indent: Vec<usize>,
    /// Hold a phatom reference to the source code lifetime. Why? Because we 
    /// might hold actual references to the source code in the future.
    source_marker: std::marker::PhantomData<&'source str>,
}

impl<'source> IdentifierOrKeyword<'source> {
    #[allow(dead_code)]
    pub fn ident(self) -> Result<&'source str, Keyword> {
        match self {
            Self::Identifier(string) => Ok(string),
            Self::Keyword(keyword) => Err(keyword),
        }
    }

    #[allow(dead_code)]
    pub fn keyword(self) -> Result<Keyword, &'source str> {
        match self {
            Self::Keyword(keyword) => Ok(keyword),
            Self::Identifier(string) => Err(string),
        }
    }
}

impl<'source> State<'source> {
    pub fn start() -> Self {
        Self {
            index: 0,
            line: 1,
            column: 1,
            indent: Vec::new(),
            source_marker: std::marker::PhantomData,
        }
    }

    /// Returns the indent depth of the current line.
    fn current_indent(&self) -> usize {
        self.indent.last().cloned().unwrap_or(0)
    }
}

/// Parses a program from a source code string.
pub fn parse(source: &str) -> Result<Term, Vec<Error>> {
    let mut state = State::start();

    // For now just parse a single term.
    skip_whitespace(source, &mut state);
    let the_term = term(source, &mut state)?;
    Ok(the_term)
}

type ParseResult<T> = Result<T, Vec<Error>>;

fn res_combine<T, U>(a: ParseResult<T>, b: ParseResult<U>) -> ParseResult<(T, U)> {
    match (a, b) {
        (Ok(a), Ok(b)) => Ok((a, b)),
        (Err(e), Ok(_)) | (Ok(_), Err(e)) => Err(e),
        (Err(mut a), Err(b)) => {
            a.extend(b);
            Err(a)
        }
    }
}

/// Parses a term from the current position.
fn term<'source>(source: &'source str, state: &mut State<'source>) -> Result<Term, Vec<Error>> {
    // First, parse an atom.
    let first_atom = atom(source, state)
        .transpose()
        .ok_or(vec![Error::TermNotFound])?;
    skip_whitespace(source, state);

    if pop_eq_str(source, state, "->") {
        skip_whitespace(source, state);
        // TODO: Make a ParseResult type.
        let ret = term(source, state);
        let (first_atom, ret) = res_combine(first_atom, ret)?;
        return Ok(Term::Binder {
            binder: BinderKind::Pi,
            param_name: "_".into(),
            ty: Rc::new(first_atom),
            body: Rc::new(ret),
        });
    }

    if pop_eq_str(source, state, "=>") {
        skip_whitespace(source, state);
        let ret = term(source, state);
        let (first_atom, ret) = res_combine(first_atom, ret)?;
        let (param_name, param_type) = match &first_atom {
            Term::TypeAnnotation(param_expr, param_type) => match param_expr.as_ref() {
                Term::Var(param_name) => (param_name.clone(), param_type.clone()),
                _ => {
                    return Err(vec![Error::ExpectedNameInParameter {
                        found: first_atom,
                    }])
                }
            },
            _ => {
                return Err(vec![Error::ExpectedTypeAnnotation {
                    found: first_atom,
                }])
            }
        };
        return Ok(Term::Binder {
            binder: BinderKind::Lam,
            param_name,
            ty: param_type,
            body: Rc::new(ret),
        });
    }

    if pop_eq(source, state, ':') {
        skip_whitespace(source, state);
        let typ = term(source, state);
        let (first_atom, typ) = res_combine(first_atom, typ)?;
        return Ok(Term::TypeAnnotation(first_atom.into(), typ.into()))
    }

    // Then, parse a list of more atoms!
    let mut applications: Result<Vec<Term>, Vec<Error>> = match &first_atom {
        Ok(_) => Ok(Vec::new()),
        Err(errors) => Err(errors.clone()),
    };

    loop {
        let next_atom = atom(source, state);
        match (next_atom, &mut applications) {
            (Ok(None), _) => break,
            (Ok(Some(atom)), Ok(applications)) => {
                applications.push(atom);
            }
            (Ok(Some(_)), Err(_)) => (),
            (Err(next_errors), Err(errors)) => {
                errors.extend(next_errors);
            }
            (Err(errors), applications @ Ok(_)) => {
                *applications = Err(errors);
            }
        }
        skip_whitespace(source, state);
    }

    applications.map(|applications| {
        let atom = first_atom.unwrap();
        applications
            .into_iter()
            .fold(atom, |acc, atom| Term::Appl(Rc::new(acc), Rc::new(atom)))
    })
}

/// Parses an atom from the current position.
fn atom<'source>(
    source: &'source str,
    state: &mut State<'source>,
) -> Result<Option<Term>, Vec<Error>> {
    skip_whitespace(source, state);

    if pop_eq(source, state, '"') {
        let mut string = String::new();
        while let Some(c) = peek(source, state) {
            line_pop(source, state);
            if c == '"' {
                break;
            }
            string.push(c);
        }
        return Ok(Some(Term::StringLiteral(string)));
    }

    if pop_eq(source, state, '(') {
        skip_whitespace(source, state);
        let term = term(source, state);
        skip_whitespace(source, state);
        if !skip_until(source, state, ')') {
            return Err(vec![Error::UnclosedParenthesis]);
        }
        term.map(Some)
    } else if let Some(ident) = identifier_or_keyword(source, state) {
        match ident {
            IdentifierOrKeyword::Identifier(ident) => Ok(Some(Term::Var(Name::from_str(ident)))),
            IdentifierOrKeyword::Keyword(keyword) => match keyword {
                Keyword::Prop => Ok(Some(Term::Prop)),
                Keyword::Type => Ok(Some(Term::Type)),
            },
        }
    } else {
        Ok(None)
    }
}

fn identifier_or_keyword<'source>(
    source: &'source str,
    state: &mut State,
) -> Option<IdentifierOrKeyword<'source>> {
    fn identifier<'source>(source: &'source str, state: &mut State) -> Option<&'source str> {
        fn identifier_start(c: char) -> bool {
            c.is_ascii_alphabetic() || c == '_'
        }

        fn identifier_continue(c: char) -> bool {
            c.is_ascii_alphanumeric() || c == '_' || c == '-'
        }

        if peek(source, state).map(identifier_start).unwrap_or(false) == false {
            return None;
        }

        let start = state.index;
        loop {
            let cont = peek(source, state)
                .map(identifier_continue)
                .unwrap_or(false);
            if !cont {
                break;
            }
            pop(source, state);
        }

        Some(source[start..state.index].into())
    }

    Some(IdentifierOrKeyword::Keyword(
        match identifier(source, state)? {
            "prop" => Keyword::Prop,
            "type" => Keyword::Type,
            ident => return Some(IdentifierOrKeyword::Identifier(ident.into())),
        },
    ))
}

/// Returns the rest of the string from the current position.
fn rest<'source>(source: &'source str, state: &mut State) -> &'source str {
    &source[state.index..]
}

/// Returns the next character from the current position, or none if we are
/// at the end of the string.
fn peek(source: &str, state: &mut State) -> Option<char> {
    rest(source, state).chars().next()
}

/// Returns the current character in the line from the current position, or
/// none if we are at the end of the line.
fn line_peek(source: &str, state: &mut State) -> Option<char> {
    rest(source, state).lines().next()?.chars().next()
}

/// Are we at the end of the code?
#[allow(dead_code)]
fn is_eof(source: &str, state: &mut State) -> bool {
    rest(source, state).is_empty()
}

/// Pop a character from the current line if there is one, else return none.
fn line_pop(source: &str, state: &mut State) -> Option<char> {
    // Is there a character?
    line_peek(source, state).map(|ch| {
        // Advance the index.
        state.index += 1;
        state.column += 1;
        ch
    })
}

/// Same as `pop`, but ignores indent.
fn pop_no_indent(source: &str, state: &mut State) -> Option<char> {
    // Is there a character?
    if let Some(ch) = peek(source, state) {
        // Advance the index.
        state.index += 1;
        // Is this a newline?
        if ch == '\n' {
            // Reset counters.
            state.column = 1;
            state.line += 1;
        } else {
            state.column += 1;
        }
        Some(ch)
    } else {
        None
    }
}

/// Pops while the current character is whitespace. Does not pop newlines.
//fn skip_whitespace(source: &str, state: &mut State) {
fn skip_whitespace1(source: &str, state: &mut State) {
    loop {
        if line_peek(source, state)
            .map(char::is_whitespace)
            .unwrap_or(false)
            == false
        {
            break;
        }
        line_pop(source, state);
    }
}

/// Pops the current character from the source. If it is a newline it will
/// also advance over the whitespace on the next line and updates indent.
fn pop(source: &str, state: &mut State) -> Option<char> {
    let ch = pop_no_indent(source, state)?;
    if ch == '\n' {
        // Skip over the spaces, and count to get the indent.
        let start = state.index;
        skip_whitespace1(source, state);
        let end = state.index;

        // Get the new indent.
        let new_indent = {
            end - start +
            // Also add the amount of tabs, times three, because each tab
            // is (assumed to be) 4 characters long.
            3 * source[start..end].chars()
                .filter(|&ch| ch == '\t')
                .count()
        };

        // Update the indent list.
        while new_indent < state.current_indent() {
            state.indent.pop();
        }
        if state.current_indent() != new_indent {
            state.indent.push(new_indent);
        }
    }
    Some(ch)
}

/// Pops the current character from the source if it is equal to the given
/// character. Returns true if it was equal, false otherwise.
fn pop_eq(source: &str, state: &mut State, ch: char) -> bool {
    if peek(source, state) == Some(ch) {
        pop(source, state);
        true
    } else {
        false
    }
}

/// Skips characters until the given character is found. Also skips over
/// that character. Returns true if the character was found, false otherwise.
fn skip_until(source: &str, state: &mut State, ch: char) -> bool {
    loop {
        match pop(source, state) {
            Some(ch2) if ch2 == ch => return true,
            Some(_) => (),
            None => return false,
        }
    }
}

// fn skip_whitespace_and_newlines(source: &str, state: &mut State) {
fn skip_whitespace(source: &str, state: &mut State) {
    loop {
        let ch = peek(source, state);
        // Stop if not whitespace or eol.
        if ch.map(char::is_whitespace).unwrap_or(true) == false {
            break;
        }
        if is_eof(source, state) {
            break;
        }
        pop(source, state);
    }
}

fn pop_eq_str(source: &str, state: &mut State, string: &str) -> bool {
    let end_index = string.len() + state.index;

    if !rest(source, state).starts_with(string) {
        return false;
    }
    while end_index > state.index {
        let res = line_pop(source, state);
        // If EOL is reached, exit early (Otherwise it won't exit at
        // all).
        if res.is_none() {
            return false;
        }
    }

    return true;
}
