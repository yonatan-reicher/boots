use super::{ArrowKind, DeBruijn, Literal, Pattern, Term};
use std::cell::RefCell;
use std::fmt::{self, Display, Formatter};

pub struct DisplayDeBruijn(DeBruijn, usize);

impl Display for DisplayDeBruijn {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "_{}", self.1 as isize - self.0 .0 as isize)
    }
}

pub struct DisplayTuple<T: Display> {
    start: char,
    end: char,
    elems: Vec<T>,
}

impl<T: Display> Display for DisplayTuple<T> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        self.start.fmt(f)?;
        for (i, elem) in self.elems.iter().enumerate() {
            if i > 0 {
                write!(f, ", ")?;
            }
            elem.fmt(f)?;
        }
        self.end.fmt(f)
    }
}

struct DisplayPattern<'a, 'b> {
    pat: &'a Pattern,
    depth: &'b RefCell<usize>,
}

impl<'a, 'b> Display for DisplayPattern<'a, 'b> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self.pat {
            Pattern::String(s) => write!(f, "{:?}", s),
            Pattern::Var => {
                *self.depth.borrow_mut() += 1;
                DisplayDeBruijn(DeBruijn::TOP, *self.depth.borrow()).fmt(f)
            }
            Pattern::UnTuple(terms) => DisplayTuple {
                start: '(',
                end: ')',
                elems: terms
                    .iter()
                    .map(|t| DisplayPattern {
                        pat: t,
                        depth: self.depth,
                    })
                    .collect(),
            }
            .fmt(f),
        }
    }
}

struct DisplayAtom<'a> {
    term: &'a Term,
    depth: usize,
}

impl<'a> Display for DisplayAtom<'a> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        let display_term = DisplayTerm {
            term: self.term,
            depth: self.depth,
        };
        if self.term.is_atom() {
            write!(f, "{display_term}")
        } else {
            write!(f, "({display_term})")
        }
    }
}

struct DisplayTerm<'a> {
    term: &'a Term,
    depth: usize,
}

impl<'a> Display for DisplayTerm<'a> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self.term {
            Term::Appl(lhs, rhs) => write!(
                f,
                "{} {}",
                if let Term::Appl(..) = lhs.as_ref() {
                    Box::new(DisplayTerm {
                        term: lhs,
                        depth: self.depth,
                    }) as Box<dyn Display>
                } else {
                    Box::new(DisplayAtom {
                        term: lhs,
                        depth: self.depth,
                    }) as Box<dyn Display>
                },
                DisplayAtom {
                    term: rhs,
                    depth: self.depth
                }
            ),
            Term::Arrow {
                kind: ArrowKind::Type,
                ty,
                body,
            } if body.free_vars().into_iter().all(|x| x != DeBruijn::TOP) => {
                write!(
                    f,
                    "{} -> {}",
                    DisplayAtom {
                        term: ty,
                        depth: self.depth,
                    },
                    DisplayTerm {
                        term: body,
                        depth: self.depth + 1,
                    },
                )
            }
            Term::Arrow {
                kind: ArrowKind::Value,
                ty,
                body,
            } if body.free_vars().into_iter().all(|x| x != DeBruijn::TOP) => {
                write!(
                    f,
                    "(_: {}) => {}",
                    DisplayAtom {
                        term: ty,
                        depth: self.depth,
                    },
                    DisplayTerm {
                        term: body,
                        depth: self.depth + 1,
                    },
                )
            }
            Term::Arrow {
                kind: binder,
                ty,
                body,
            } => write!(
                f,
                "({display_var}: {}) {arrow} {}",
                DisplayTerm {
                    term: ty,
                    depth: self.depth
                },
                DisplayTerm {
                    term: body,
                    depth: self.depth + 1
                },
                display_var = DisplayDeBruijn(DeBruijn::TOP, self.depth + 1),
                arrow = match binder {
                    ArrowKind::Type => "->",
                    ArrowKind::Value => "=>",
                },
            ),
            Term::Literal(literal) => write!(f, "{literal}"),
            Term::TypeAnnotation(lhs, rhs) => write!(
                f,
                "{}: {}",
                DisplayAtom {
                    term: lhs,
                    depth: self.depth
                },
                DisplayAtom {
                    term: rhs,
                    depth: self.depth
                },
            ),
            Term::Var(var) => DisplayDeBruijn(*var, self.depth).fmt(f),
            Term::Let(None, bind, ret) => write!(
                f,
                "let {name} = {} in {}",
                DisplayAtom {
                    term: bind,
                    depth: self.depth
                },
                DisplayTerm {
                    term: ret,
                    depth: self.depth
                },
                name = DisplayDeBruijn(DeBruijn::TOP, self.depth + 1),
            ),
            Term::Let(Some(annot), bind, ret) => write!(
                f,
                "let {name} : {} = {} in {}",
                DisplayAtom {
                    term: annot,
                    depth: self.depth
                },
                DisplayTerm {
                    term: bind,
                    depth: self.depth
                },
                DisplayTerm {
                    term: ret,
                    depth: self.depth + 1
                },
                name = DisplayDeBruijn(DeBruijn::TOP, self.depth),
            ),
            Term::Tuple(elements) => DisplayTuple {
                start: '(',
                end: ')',
                elems: elements.iter().collect(),
            }
            .fmt(f),
            Term::TupleType(elements) => DisplayTuple {
                start: '{',
                end: '}',
                elems: elements.iter().collect(),
            }
            .fmt(f),
            Term::Match(term, cases) => {
                write!(
                    f,
                    "match {} with {{ ",
                    DisplayTerm {
                        term: term,
                        depth: self.depth
                    },
                )?;
                for (pattern, body) in cases {
                    let depth = RefCell::new(self.depth + 1);
                    write!(
                        f,
                        "{} => ",
                        DisplayPattern {
                            pat: pattern,
                            depth: &depth,
                        },
                    )?;
                    write!(
                        f,
                        "{} ",
                        DisplayTerm {
                            term: body,
                            depth: *depth.borrow(),
                        },
                    )?;
                }
                write!(f, "}}")?;
                Ok(())
            }
            Term::UnionType(elements) => elements
                .iter()
                .map(|x| format!("{x}"))
                .collect::<Vec<_>>()
                .join(" | ")
                .fmt(f),
        }
    }
}

impl Display for Term {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        DisplayTerm {
            term: self,
            depth: 0,
        }
        .fmt(f)
    }
}

impl Display for Literal {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        use Literal::*;
        match self {
            Prop => write!(f, "prop"),
            Type => write!(f, "type"),
            String(s) => write!(f, "\"{s}\""),
            Str => write!(f, "str"),
            StringAppend => write!(f, "<string-append>"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast_to_term::ast_to_term;
    use crate::parse::parse;
    use crate::term::PTerm;

    fn new_term(s: &str) -> PTerm {
        ast_to_term(&parse(s).unwrap(), []).unwrap().into()
    }

    #[test]
    fn display_arrow_term() {
        let term = new_term("(x: type) -> x");
        assert_eq!(term.to_string(), "(_1: type) -> _1");
    }

    #[test]
    fn display_free_arrow_term() {
        let term = new_term("(x: type) -> type");
        assert_eq!(term.to_string(), "type -> type");
    }

    #[test]
    fn display_nested_arrow_term1() {
        let term = new_term("(x: type) => (y: type) -> x");
        assert_eq!(term.to_string(), "(_1: type) => type -> _1");
    }

    #[test]
    fn display_nested_arrow_term2() {
        let term = new_term("(x: type) => (y: type) -> x y");
        assert_eq!(term.to_string(), "(_1: type) => (_2: type) -> _1 _2");
    }

    #[test]
    fn display_nested_arrow_term3() {
        let term = new_term("(x: type) => (y: type) => y");
        assert_eq!(term.to_string(), "(_: type) => (_2: type) => _2");
    }

    #[test]
    fn display_annotation_term() {
        let term = new_term("(x: type) -> x: type");
        assert_eq!(term.to_string(), "(_1: type) -> _1: type");
    }
}
