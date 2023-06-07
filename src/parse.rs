mod token_reader;

use crate::ast::{ArrowKind, Ast, Literal};
use crate::lex::{lex, Keyword, Symbol, Token};
use crate::located::Pos;
use crate::name::Name;
use token_reader::TokenReader;


#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Error {
    TermNotFound(Pos),
    // TODO
    UnclosedParenthesis {
        open: Pos,
        expected_close: Pos,
        found_close: Option<Pos>,
    },
}

struct State<'source> {
    tokens: TokenReader<'source>,
    errors: Vec<Error>,
}

impl<'a> std::ops::Deref for State<'a> {
    type Target = TokenReader<'a>;

    fn deref(&self) -> &Self::Target {
        &self.tokens
    }
}

impl<'a> std::ops::DerefMut for State<'a> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.tokens
    }
}

impl State<'_> {
    pub fn error(&mut self, error: Error) {
        self.errors.push(error)
    }
}

// Grammer:
// <program> ::= <term>
// <term> ::=
//      | <match_term>
//      | `|`? <atom> (`|` <atom>)+
//      | <atom> (`=>` | `->` | `:`) (<term> | @indented(<term>))
//      | <application_term>
//      | <assign_term>
// <application_term> ::= <atom> <atom>* @indented(<term>+)?
// <assign_term> ::= <atom> <atom>* `=` (@indented(<term>) <term> | <term> `\n` <term>)
// <match_term> ::= `match` <term> with { @indented(<cases>) }
// <atom> ::=
//      | <literal>
//      | `(` <term> `)`
//      | `(` (<term>),* `)`
//      | `{` (<term>),* `}`
//      | <ident>

/// Parses a program from a source code string.
pub fn parse(source: &str) -> Result<Ast, Vec<Error>> {
    let mut state = State {
        tokens: TokenReader::new(lex(source)),
        errors: Vec::new(),
    };

    // Read until start of term line.
    state.tokens.pop_indent_same(0);

    // For now just parse a single term.
    let the_term = term(&mut state);
    if state.errors.is_empty() {
        Ok(the_term)
    } else {
        Err(state.errors)
    }
}

fn match_term(state: &mut State) -> Ast {
    let start_indent = state.tokens.indent();

    let input = term(state);

    if !state.pop_token_eq(Keyword::With) {
        todo!("Fail here.")
    }

    // Parse the match cases.
    if !state.pop_token_eq(Symbol::OpenCurly) {
        todo!("Fail here.")
    }

    if !state.pop_indent_in() {
        todo!("Fail here.")
    }

    let inner_indent = state.indent();

    let mut cases = Vec::new();

    while {
        let pattern = atom(state).unwrap_or_else(|| todo!("Fail here."));
        if !state.pop_token_eq(Symbol::FatArrow) {
            todo!("Fail here.")
        }
        let result = term(state);
        cases.push((pattern, result));
        state.pop_indent_same(inner_indent)
    } {}

    if !state.pop_indent_same(start_indent) {
        todo!("Fail here.")
    }

    if !state.pop_token_eq(Symbol::CloseCurly) {
        todo!("Fail on no curly.")
    }

    Ast::Match(input.into(), cases)
}

/// Parses a term from the current position.
fn term(state: &mut State) -> Ast {
    let start = state.curr_range().0;

    if state.pop_token_eq(Keyword::Match) {
        return match_term(state);
    }

    // First, parse an atom.
    let first_atom = match atom(state) {
        Some(tokens) => tokens,
        None => {
            state.error(Error::TermNotFound(start));
            return Ast::Error;
        }
    };

    if state.pop_token_eq(Symbol::FatArrow) {
        // Allow indenting in!
        state.pop_indent_in();
        let ret = term(state);
        return Ast::Arrow(ArrowKind::Value, first_atom.into(), ret.into());
    }

    if state.pop_token_eq(Symbol::ThinArrow) {
        // Allow indenting in!
        state.pop_indent_in();
        let ret = term(state);
        return Ast::Arrow(ArrowKind::Type, first_atom.into(), ret.into());
    }

    if state.pop_token_eq(Symbol::Colon) {
        // Allow indenting in!
        state.pop_indent_in();
        let typ = term(state);
        return Ast::TypeAnnotation(first_atom.into(), typ.into());
    }

    if state.pop_token_eq(Symbol::Pipe) {
        let mut elements = Vec::new();
        let Some(second_atom) = atom(state) else {
            todo!("Error: Expected atom after pipe");
        };
        while state.pop_token_eq(Symbol::Pipe) {
            let Some(next_atom) = atom(state) else {
                todo!("Error: Expected atom after pipe");
            };
            elements.push(next_atom);
        }
        return Ast::UnionType(first_atom.into(), second_atom.into(), elements.into());
    }

    // Then, parse a list of more atoms!
    let second_atom = atom(state);
    let mut rest_of_applications = vec![];
    if second_atom.is_some() {
        while let Some(next_atom) = atom(state) {
            rest_of_applications.push(next_atom);
        }
    }

    // Combine the atoms into a single term.
    let application_term = match second_atom {
        Some(second_atom) => Ast::Appl(first_atom.into(), second_atom.into(), rest_of_applications),
        None => first_atom,
    };

    // Is this an indented application expression?
    if state.pop_indent_in() {
        let start_indent = state.indent();
        let mut rest_of_applications = Vec::new();
        let first_argument = term(state);
        while state.pop_indent_same(start_indent) {
            let next_argument = term(state);
            rest_of_applications.push(next_argument);
        }

        return Ast::Appl(
            application_term.into(),
            first_argument.into(),
            rest_of_applications,
        );
    }

    // Is this a assign expression?
    if state.pop_token_eq(Symbol::Equal) {
        let start_indent = state.indent();
        state.pop_indent_in(); // Fine if this fails.
        let rhs = term(state);
        if !state.pop_indent_same(start_indent) {
            todo!("error: expected expression with same indent");
        }
        let ret = term(state);
        return Ast::Let(application_term.into(), rhs.into(), ret.into());
    }

    application_term
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Commas {
    HasCommas,
    NoCommas,
}

/// Parses a list of terms seperated by commas.
/// The list can be seperated on both sides.
fn parse_list<'source>(
    state: &mut State<'source>,
    end: impl Copy + Into<Token<'source>>,
) -> (Vec<Ast>, Commas) {
    // Edge case: Empty list.
    if state.pop_token_eq(end) {
        return (Vec::new(), Commas::NoCommas);
    }

    let mut ret = Vec::new();
    let mut commas = Commas::NoCommas;

    let out_indent = state.indent();
    state.pop_indent_in();
    let in_indent = state.indent();

    // TODO: Allow elm style lists.
    loop {
        // Parse a term.
        ret.push(term(state));
        // Expect a potential comma.
        let seen_comma = state.pop_token_eq(Symbol::Comma);
        if seen_comma {
            commas = Commas::HasCommas;
        }
        // After wards, if we indent out, we should reach the end.
        if state.pop_indent_same(out_indent) {
            if !state.pop_token_eq(end) {
                todo!("Put error here")
            }
            break (ret, commas);
        }
        // Or if we reach the end token.
        if state.pop_token_eq(end) {
            break (ret, commas);
        }

        // If this is not the end of the list, and there was no comma, then
        // the list is not written correctly.
        if !seen_comma {
            todo!("Error");
        }

        state.pop_indent_same(in_indent);
    }
}

/// Parses an atom from the current position.
fn atom(state: &mut State) -> Option<Ast> {
    let start = state.get_range(state.index()).0;

    if let Some(literal) = literal(state) {
        return Some(Ast::Literal(literal, (start..state.prev_range().1).into()));
    }

    if state.pop_token_eq(Symbol::OpenParen) {
        let (mut terms, commas) = parse_list(state, Symbol::CloseParen);

        // Just parenthesis with commas and a single element is not a tuple.
        if Commas::NoCommas == commas && terms.len() == 1 {
            return Some(terms.pop().unwrap());
        }

        // Every other case is a tuple.
        return Some(Ast::Tuple(terms));

        /*
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
        */
    }

    if state.pop_token_eq(Symbol::OpenCurly) {
        let (terms, _) = parse_list(state, Symbol::CloseCurly);
        return Some(Ast::TupleType(terms));
    }

    if let Some(ident) = state.pop_token_ident() {
        return Some(Ast::Var(Name::from_str(ident), state.prev_range()));
    }

    None
}

fn literal(state: &mut TokenReader) -> Option<Literal> {
    if let Some(string) = state.pop_token_string() {
        return Some(Literal::String(Name::from_str(string)));
    }

    if let Some(int) = state.pop_token_int() {
        return Some(Literal::Int(int));
    }

    if state.pop_token_eq(Token::Keyword(Keyword::Type)) {
        return Some(Literal::Type);
    }

    if state.pop_token_eq(Token::Keyword(Keyword::Prop)) {
        return Some(Literal::Prop);
    }

    None
}

// TODO: Define a grammer for the language, and make tests based on that.

#[cfg(test)]
mod tests {
    use super::*;
    use indoc::indoc;
    use crate::located::Range;

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
                ArrowKind::Value,
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

    #[test]
    fn parse_nested_annotation() {
        assert_eq!(
            parse("x: y: type"),
            Ok(Ast::TypeAnnotation(
                Ast::Var("x".into(), r(0..1)).into(),
                Ast::TypeAnnotation(
                    Ast::Var("y".into(), r(3..4)).into(),
                    Ast::Literal(Literal::Type, r(6..10)).into()
                )
                .into()
            ))
        )
    }

    #[test]
    fn parse_union() {
        assert_eq!(
            parse("x: y | z"),
            Ok(Ast::TypeAnnotation(
                Ast::Var("x".into(), r(0..1)).into(),
                Ast::UnionType(
                    Ast::Var("y".into(), r(3..4)).into(),
                    Ast::Var("z".into(), r(7..8)).into(),
                    vec![],
                )
                .into()
            ))
        );
    }
}
