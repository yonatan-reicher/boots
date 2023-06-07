use crate::lex::{LToken, NewLine, Symbol, Token};
use crate::located::Range;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TokenReader<'source> {
    tokens: Vec<LToken<'source>>,
    index: usize,
    indent: usize,
    parens_depth: usize,
}

impl<'source> TokenReader<'source> {
    pub fn new(tokens: Vec<LToken<'source>>) -> Self {
        Self {
            tokens,
            index: 0,
            indent: 0,
            parens_depth: 0,
        }
    }

    pub fn indent(&self) -> usize {
        self.indent
    }

    pub fn index(&self) -> usize {
        self.index
    }

    pub fn current(&self) -> Option<LToken<'source>> {
        self.tokens.get(self.index).cloned()
    }

    pub fn pop(&mut self) -> Option<LToken<'source>> {
        let ret = self.current();
        self.index += 1;
        self.index = self.index.min(self.tokens.len());
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
        self.tokens.get(index).map(|t| t.1).unwrap_or((0..0).into())
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
                NewLine::EmptyLine => self.pop_indent_helper(predicate),
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

    #[allow(dead_code)]
    pub fn pop_indent(&mut self) -> bool {
        self.pop_indent_helper(|_, _| true)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lex::lex;
    use crate::located::IntoLocated;
    use indoc::indoc;
    use std::matches;

    fn new_reader(source: &str) -> TokenReader {
        TokenReader::new(lex(source))
    }

    #[test]
    pub fn test_pop() {
        let mut reader = new_reader("1 2 3");
        assert_eq!(
            reader.pop(),
            Some(Token::NewLine(NewLine::NewLine { indent: 0 }).into_located(0..0))
        );
        assert_eq!(reader.pop(), Some(Token::Int(1).into_located(0..1)));
        assert_eq!(reader.pop(), Some(Token::Int(2).into_located(2..3)));
        assert_eq!(reader.pop(), Some(Token::Int(3).into_located(4..5)));
        assert_eq!(reader.pop(), None);
    }

    #[test]
    pub fn test_pop_newline() {
        let mut reader = new_reader(indoc! {"
            1
            2
                3

            4
        "});
        assert_eq!(
            reader.pop(),
            Some(Token::NewLine(NewLine::NewLine { indent: 0 }).into_located(0..0))
        );
        assert_eq!(reader.pop(), Some(Token::Int(1).into_located(0..1)));
        assert_eq!(
            reader.pop(),
            Some(Token::NewLine(NewLine::NewLine { indent: 0 }).into_located(1..2))
        );
        assert_eq!(reader.pop(), Some(Token::Int(2).into_located(2..3)));
        assert_eq!(
            reader.pop(),
            Some(Token::NewLine(NewLine::NewLine { indent: 4 }).into_located(3..8))
        );
        assert_eq!(reader.pop(), Some(Token::Int(3).into_located(8..9)));
        assert_eq!(
            reader.pop(),
            Some(Token::NewLine(NewLine::EmptyLine).into_located(9..10))
        );
        assert_eq!(
            reader.pop(),
            Some(Token::NewLine(NewLine::NewLine { indent: 0 }).into_located(10..11))
        );
        assert_eq!(reader.pop(), Some(Token::Int(4).into_located(11..12)));
        assert_eq!(
            reader.pop(),
            Some(Token::NewLine(NewLine::EmptyLine).into_located(12..13))
        );
        assert_eq!(reader.pop(), None);
    }

    #[test]
    pub fn test_prev_range() {
        let mut reader = new_reader("123");
        assert_eq!(reader.prev_range(), (0..0).into());
        assert_eq!(
            reader.pop(),
            Some(Token::NewLine(NewLine::NewLine { indent: 0 }).into_located(0..0))
        );
        assert_eq!(reader.pop(), Some(Token::Int(123).into_located(0..3)));
        assert_eq!(reader.prev_range(), (0..3).into());
        assert_eq!(reader.pop(), None);
        assert_eq!(reader.prev_range(), (0..3).into());
    }

    #[test]
    pub fn test_pop_indent() {
        let mut reader = new_reader(indoc! {"
            hello
                world
                  whats
                down
        "});

        assert_eq!(
            reader.pop(),
            Some(Token::NewLine(NewLine::NewLine { indent: 0 }).into_located(0..0))
        );
        assert_eq!(reader.pop(), Some(Token::Ident("hello").into_located(0..5)));
        assert!(reader.pop_indent_in());
        let indent = reader.indent;
        assert_eq!(
            reader.pop(),
            Some(Token::Ident("world").into_located(10..15))
        );
        assert!(reader.pop_indent_in());
        assert_eq!(reader.pop_token(), Some(Token::Ident("whats")));
        assert!(!reader.pop_indent_in());
        // Make sure the token didn't get popped.
        assert!(matches!(
            reader.curr_token(),
            Some(Token::NewLine(NewLine::NewLine { .. }))
        ));
        assert!(reader.pop_indent_same(indent));
    }
}
