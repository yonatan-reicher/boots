use std::fmt::{self, Display, Formatter};

use crate::global::*;
use crate::located::{IntoLocated, Located as L, Range};

#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub enum Token<'source> {
    Ident(&'source str),
    Keyword(Keyword),
    Symbol(Symbol),
    NewLine(NewLine),
    String(&'source str),
    Int(i32),            
    InvalidChar(char),
    UnteminatedString,
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
    Prop "prop",
    Type "type"
} }

define_plain_enum! { pub enum Symbol {
    FatArrow "=>",
    ThinArrow "->",
    Equal "=",
    Colon ":",
    OpenParen "(",
    CloseParen ")"
} }

#[derive(Copy, Clone, Eq, PartialEq, Ord, PartialOrd, Hash, Debug)]
pub enum NewLine {
    NewLine { indent: usize },
    EmptyLine,
}

impl<'a> From<NewLine> for Token<'a> {
    fn from(value: NewLine) -> Self {
        Self::NewLine(value)
    }
}

impl<'a> From<Keyword> for Token<'a> {
    fn from(value: Keyword) -> Self {
        Self::Keyword(value)
    }
}

impl<'a> From<Symbol> for Token<'a> {
    fn from(value: Symbol) -> Self {
        Self::Symbol(value)
    }
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

        // Do not advance or return a value if at the end of the line.
        if std::matches!(ret, Some('\n' | '\r') | None) {
            return None;
        }

        self.index += 1;
        self.col += 1;
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

    fn pop(&mut self, s: &str) -> Option<char> {
        self.line_pop(s).or_else(|| {
            if self.pop_newline(s) {
                Some('\n')
            } else {
                None
            }
        })
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

    fn string<'source>(&mut self, s: &'source str) -> Option<Result<&'source str, ()>> {
        if self.curr_char(s) != Some('"') {
            return None;
        }
        // Skip over the qoute.
        self.line_pop(s);

        let start = self.index;
        while !std::matches!(self.curr_char(s), Some('"') | None) {
            self.pop(s);
        }
        let is_terminated = self.curr_char(s) == Some('"');
        let end = self.index;

        // Skip over the end qoute.
        self.line_pop(s);

        let string = &s[start..end];
        is_terminated.then_some(string).ok_or(()).pipe(Some)
    }

    fn number(&mut self, s: &str) -> Option<i32> {
        if !self
            .curr_char(s)
            .as_ref()
            .map(char::is_ascii_digit)
            .unwrap_or(false)
        {
            return None;
        }

        let start = self.index;
        while self
            .curr_char(s)
            .as_ref()
            .map(char::is_ascii_digit)
            .unwrap_or(false)
        {
            self.line_pop(s);
        }
        let end = self.index;

        let number = s[start..end].parse().unwrap();

        Some(number)
    }

    fn comment<'a>(&mut self, s: &'a str) -> Option<&'a str> {
        if self.rest(s).starts_with("//") {
            // The start of the comment comes after the '//'.
            let start = self.index + 2;
            // Skip until the end of the line. Do not skip the line break.
            while self.line_pop(s).is_some() {}
            Some(s[start..self.index].trim())
        } else {
            None
        }
    }

    fn range_start(&mut self) {
        self.token_start = self.index;
    }

    fn range(&mut self) -> Range {
        (self.token_start..self.index).into()
    }

    pub fn pop_token<'a>(&mut self, s: &'a str) -> Option<LToken<'a>> {
        self.skip_space(s);

        // Skip comments.
        self.comment(s);

        self.range_start();

        // Newlines.
        if !self.began || self.pop_newline(s) {
            self.began = true;
            let spaces_skipped_at_start = self.skip_space(s);
            self.comment(s);
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
                .into_located(self.range())
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
                .into_located(self.range())
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
            .into_located(self.range())
            .pipe(Some);
        }

        // Parse numbers.
        if let Some(num) = self.number(s) {
            return Token::Int(num).into_located(self.range()).pipe(Some);
        }

        // Parse strings.
        if let Some(string) = self.string(s) {
            return match string {
                Ok(string) => Token::String(string),
                Err(()) => Token::UnteminatedString,
            }
            .into_located(self.range())
            .pipe(Some);
        }

        // Invalid char encountered.
        if let Some(ch) = self.curr_char(s) {
            self.line_pop(s);
            return Token::InvalidChar(ch).into_located(self.range()).pipe(Some);
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
    use indoc::indoc;

    #[test]
    fn lex_empty() {
        let source = "";
        assert_eq!(
            lex(source),
            vec![NewLine::EmptyLine.pipe(Token::NewLine).into_located(0..0)]
        );
    }

    #[test]
    fn test_newline_token() {
        let source = "\n";
        assert_eq!(
            lex(source),
            vec![
                NewLine::EmptyLine.pipe(Token::NewLine).into_located(0..0),
                NewLine::EmptyLine.pipe(Token::NewLine).into_located(0..1),
            ]
        );
    }

    #[test]
    fn test_lex() {
        let source = indoc! {r#"
            x: prop = 5

            y: type = x => "a"
        "#};

        assert_eq!(
            lex(source),
            vec![
                Token::NewLine(NewLine::NewLine { indent: 0 }).into_located(0..0),
                Token::Ident("x").into_located(0..1),
                Token::Symbol(Symbol::Colon).into_located(1..2),
                Token::Keyword(Keyword::Prop).into_located(3..7),
                Token::Symbol(Symbol::Equal).into_located(8..9),
                Token::Int(5).into_located(10..11),

                Token::NewLine(NewLine::EmptyLine).into_located(11..12),

                Token::NewLine(NewLine::NewLine { indent: 0 }).into_located(12..13),
                Token::Ident("y").into_located(13..14),
                Token::Symbol(Symbol::Colon).into_located(14..15),
                Token::Keyword(Keyword::Type).into_located(16..20),
                Token::Symbol(Symbol::Equal).into_located(21..22),
                Token::Ident("x").into_located(23..24),
                Token::Symbol(Symbol::FatArrow).into_located(25..27),
                Token::String("a").into_located(28..31),

                Token::NewLine(NewLine::EmptyLine).into_located(31..32),
            ]
        );
    }
}
