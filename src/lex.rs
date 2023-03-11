use indoc::indoc;
use std::fmt::{self, Display, Formatter};

use crate::global::*;
use crate::located::{AsLocated, Located as L, Range};

#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub enum Token<'source> {
    Ident(&'source str),
    Keyword(Keyword),
    Symbol(Symbol),
    NewLine(NewLine),
    InvalidChar(char),
    String(&'source str), // TODO
}

pub type LToken<'a> = L<Token<'a>>;

/// Defines an enum that can be converted to and from a string.
macro_rules! define_plain_enum {
    (pub enum $name: ident { $($variant: ident $value: expr),+ }) => {
        #[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
        pub enum $name {
            $($variant),+
        }

        impl From<&$name> for &'static str {
            fn from(value: &$name) -> Self {
                match value {
                    $($name::$variant => $value),+
                }
            }
        }

        impl<'a> TryFrom<&'a str> for $name {
            type Error = ();

            fn try_from(value: &str) -> Result<Self, Self::Error> {
                match value {
                    $($value => Ok(Self::$variant)),+,
                    _ => Err(())
                }
            }
        }

        impl Display for $name {
            fn fmt(&self, f: &mut Formatter) -> fmt::Result {
                let string: &'static str = self.into();
                write!(f, "{}", string)
            }
        }

        impl $name {
            pub const ALL: &'static [&'static str] =
                &[
                    $($value),+
                ];
        }
    };
}

define_plain_enum! { pub enum Keyword {
    Let "let",
    Prop "prop",
    Type "type"
} }

define_plain_enum! { pub enum Symbol {
    FatArrow "=>",
    ThinArrow "->"
} }

#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub enum NewLine {
    NewLine { indent: usize },
    EmptyLine,
}

#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug, Default)]
struct State {
    index: usize,
    line: usize,
    col: usize,
    token_start: usize,
    began: bool,
}

impl State {
    fn rest<'a>(&self, s: &'a str) -> &'a str {
        &s[std::cmp::min(self.index, s.len())..]
    }

    fn curr_char(&self, s: &str) -> Option<char> {
        self.rest(s).chars().next()
    }

    fn line_pop(&mut self, s: &str) -> Option<char> {
        let ret = self.curr_char(s);
        if !std::matches!(ret, Some('\n' | '\r') | None) {
            self.index += 1;
            self.col += 1;
        }
        ret
    }

    fn skip_space(&mut self, s: &str) -> usize {
        let mut spaces_skipped = 0;
        while std::matches!(self.curr_char(s), Some(' ' | '\t')) {
            // Count tabs as 4 spaces.
            spaces_skipped += match self.curr_char(s) {
                Some(' ') => 1,
                Some('\t') => 4,
                _ => unreachable!(),
            };
            // Skip the current characetr!
            self.line_pop(s);
        }
        spaces_skipped
    }

    fn pop_newline(&mut self, s: &str) -> bool {
        if self.rest(s).starts_with("\r\n") {
            self.index += 2;
            self.col = 0;
            self.line += 1;
            true
        } else if self.curr_char(s) == Some('\n') {
            self.index += 1;
            self.col = 0;
            self.line += 1;
            true
        } else {
            false
        }
    }

    fn identifier<'a>(&mut self, s: &'a str) -> Option<&'a str> {
        if identifier_start(self.curr_char(s)) {
            let start = self.index;
            while identifier_continue(self.curr_char(s)) {
                self.line_pop(s);
            }
            let end = self.index;
            Some(&s[start..end])
        } else {
            None
        }
    }

    fn range_start(&mut self) {
        self.token_start = self.index;
    }

    fn range(&mut self) -> Range {
        self.token_start..self.index
    }

    pub fn pop_token<'a>(&mut self, s: &'a str) -> Option<LToken<'a>> {
        self.skip_space(s);

        self.range_start();

        // Newlines.
        if !self.began || self.pop_newline(s) {
            self.began = true;
            let spaces_skipped_at_start = self.skip_space(s);
            // Are we at the end of the line??
            let newline = if std::matches!(self.curr_char(s), None | Some('\r' | '\n')) {
                NewLine::EmptyLine
            } else {
                NewLine::NewLine {
                    indent: spaces_skipped_at_start,
                }
            };
            return newline
                .pipe(Token::NewLine)
                .as_located(self.range())
                .pipe(Some);
        }

        // Parse symbols.
        if let Some(&symbol) = Symbol::ALL
            .iter()
            .find(|&&symbol| self.rest(s).starts_with(symbol))
        {
            for _ in 0..symbol.len() {
                self.line_pop(s);
            }
            return Symbol::try_from(symbol)
                .unwrap()
                .pipe(Token::Symbol)
                .as_located(self.range())
                .pipe(Some);
        }

        // Parse identifiers and keywords.
        if let Some(ident) = self.identifier(s) {
            // Check if this is actually a keyword.
            return if let Ok(keyword) = Keyword::try_from(ident) {
                Token::Keyword(keyword)
            } else {
                Token::Ident(ident)
            }
            .as_located(self.range())
            .pipe(Some);
        }

        if let Some(ch) = self.curr_char(s) {
            self.line_pop(s);
            return Token::InvalidChar(ch).as_located(self.range()).pipe(Some);
        }

        None
    }
}

pub fn lex(source: &str) -> Vec<LToken> {
    let mut state = State::default();
    let mut ret = Vec::new();
    while let Some(token) = state.pop_token(source) {
        ret.push(token);
    }
    ret
}

fn identifier_start(c: Option<char>) -> bool {
    if let Some(c) = c {
        c.is_ascii_alphabetic() || c == '_'
    } else {
        false
    }
}

fn identifier_continue(c: Option<char>) -> bool {
    if let Some(c) = c {
        c.is_ascii_alphanumeric() || c == '_' || c == '-'
    } else {
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lex_empty() {
        let source = "";
        assert_eq!(
            lex(source),
            vec![NewLine::EmptyLine.pipe(Token::NewLine).as_located(0..0)]
        );
    }

    #[test]
    fn test_newline_token() {
        let source = "\n";
        assert_eq!(
            lex(source),
            vec![
                NewLine::EmptyLine.pipe(Token::NewLine).as_located(0..0),
                NewLine::EmptyLine.pipe(Token::NewLine).as_located(0..1),
            ]
        );
    }

    #[test]
    fn test_lex() {
        let source = indoc! {"
            let x = 5
        "};

        assert_eq!(lex(source), vec![]);
    }
}
