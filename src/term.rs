mod eval;
mod infer;

use std::cell::RefCell;
use std::collections::HashSet;
use std::fmt::{self, Display, Formatter};
use std::hash::Hash;
use std::rc::Rc;

use crate::global::*;
use crate::name::Name;

pub use eval::{eval, substitute, Context as EvalContext};
pub use infer::{infer, Context as TypeContext, Error as TypeError};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ArrowKind {
    Value,
    Type,
}

#[derive(Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Pattern {
    Var,
    UnTuple(Vec<Pattern>),
    String(Name),
}

/// A De Bruijn index (starting at 0) - a number representing the number of
/// binders between the variable and its binding site.
/// For example, in the term `λx.λy. x y`, the `x` has index 1 because it is
/// bound by the first binder, and `y` has index 0 because it is bound by the
/// inner binder.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct DeBruijn(usize);

impl From<usize> for DeBruijn {
    fn from(n: usize) -> Self {
        DeBruijn(n)
    }
}

impl DeBruijn {
    const TOP: DeBruijn = DeBruijn(0);

    fn to_index(self, len: usize) -> Option<usize> {
        len.checked_sub(1)?.checked_sub(self.0)
    }

    pub fn index<T>(self, vec: &[T]) -> Option<&T> {
        vec.get(self.to_index(vec.len())?)
    }

    pub fn index_mut<T>(self, vec: &mut [T]) -> Option<&mut T> {
        vec.get_mut(self.to_index(vec.len())?)
    }

    pub fn from_index(index: usize, len: usize) -> DeBruijn {
        assert!(index < len);
        DeBruijn(len - 1 - index)
    }

    // TODO: Return None if failed.
    fn dec(self) -> DeBruijn {
        DeBruijn(self.0 - 1)
    }

    fn inc(&self) -> DeBruijn {
        DeBruijn(self.0 + 1)
    }
}

struct DisplayDeBruijn(DeBruijn, usize);

impl Display for DisplayDeBruijn {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "_{}", self.1 as isize - self.0 .0 as isize)
    }
}

pub type PTerm = Rc<Term>;

// TODO: Is our PartialOrd valid? Because we have overriden partial eq.
// Aternatively, do not implement PartialOrd and PartialEq at all.
/**
 * The syntax of our calculus. Notice that types are represented in the same way
 * as terms, which is the essence of CoC.
 */
#[derive(Debug, PartialOrd, Ord, PartialEq, Eq, Hash)]
pub enum Term {
    Appl(PTerm, PTerm),
    Arrow {
        kind: ArrowKind,
        ty: PTerm,
        body: PTerm,
    },
    Literal(Literal),
    TypeAnnotation(PTerm, PTerm),
    Var(DeBruijn),
    Let(Option<PTerm>, PTerm, PTerm),
    Tuple(Vec<PTerm>),
    TupleType(Vec<PTerm>),
    Match(PTerm, Vec<(Rc<Pattern>, PTerm)>),
}

#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Literal {
    Prop,
    Str,
    StringAppend,
    String(Name),
    Type,
}

impl From<Literal> for Term {
    fn from(literal: Literal) -> Self {
        Term::Literal(literal)
    }
}

impl From<Literal> for PTerm {
    fn from(literal: Literal) -> Self {
        Rc::new(literal.into())
    }
}

impl Pattern {
    pub fn childern(&self) -> Vec<&Pattern> {
        match self {
            Pattern::Var | Pattern::String(..) => vec![],
            Pattern::UnTuple(ps) => ps.iter().collect(),
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = &Pattern> {
        let mut stack = vec![self];
        std::iter::from_fn(move || {
            if let Some(p) = stack.pop() {
                stack.extend(p.childern());
                Some(p)
            } else {
                None
            }
        })
    }

    pub fn vars(&self) -> usize {
        self.iter().filter(|p| matches!(p, Pattern::Var)).count()
    }
}

impl Term {
    pub fn into_pterm(self) -> PTerm {
        Rc::new(self)
    }

    pub fn is_atom(&self) -> bool {
        matches!(
            self,
            Term::Literal(_) | Term::Var(_) | Term::Tuple(_) | Term::TupleType(_)
        )
    }

    pub fn is_reduced(&self) -> bool {
        match self {
            Term::Literal(_) => true,
            Term::Tuple(elements) | Term::TupleType(elements) => {
                elements.iter().all(|e| e.is_reduced())
            }
            Term::Arrow { ty, .. } => ty.is_reduced(),
            Term::Appl(_, _) => false,
            Term::TypeAnnotation(_, _) => false,
            Term::Var(_) => false,
            Term::Let(_, _, _) => false,
            Term::Match(_, _) => false,
        }
    }

    pub fn declares_var(&self) -> bool {
        matches!(self, Term::Let(..) | Term::Arrow { .. })
    }

    pub fn childern(&self) -> Vec<PTerm> {
        match self {
            Term::Literal(_) | Term::Var(_) => vec![],
            Term::Tuple(elements) | Term::TupleType(elements) => elements.clone(),
            Term::Arrow { ty, body, .. } => vec![ty.clone(), body.clone()],
            Term::Appl(lhs, rhs) => vec![lhs.clone(), rhs.clone()],
            Term::TypeAnnotation(term, ty) => vec![term.clone(), ty.clone()],
            Term::Let(annot, term, body) => {
                vec![term.clone(), body.clone()].extend_pipe(annot.clone())
            }
            Term::Match(term, cases) => {
                vec![term.clone()].extend_pipe(cases.iter().map(|(_, c)| c.clone()))
            }
        }
    }

    pub fn iter_depth(this: &PTerm) -> impl Iterator<Item = (usize, PTerm)> {
        let mut stack = vec![(0, this.clone())];
        std::iter::from_fn(move || {
            // Pop a term.
            let (depth, term) = stack.pop()?;

            // Update the stack!
            let inner_depth = if term.declares_var() {
                depth + 1
            } else {
                depth
            };
            stack.extend(term.childern().into_iter().map(|t| (inner_depth, t)));

            Some((depth, term))
        })
    }

    pub fn free_vars(self: &PTerm) -> HashSet<DeBruijn> {
        Self::iter_depth(self)
            .filter_map(|(depth, term)| match term.as_ref() {
                Term::Var(DeBruijn(de_bruijn)) if *de_bruijn >= depth => {
                    Some(DeBruijn(de_bruijn - depth))
                }
                _ => None,
            })
            .collect()
    }
}

struct DisplayTuple<T: Display> {
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
                        depth: self.depth
                    },
                    DisplayTerm {
                        term: body,
                        depth: self.depth
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
                        "{} => {} ",
                        DisplayPattern {
                            pat: pattern,
                            depth: &depth,
                        },
                        DisplayTerm {
                            term: body,
                            depth: *depth.borrow(),
                        },
                    )?;
                }
                write!(f, "}}")?;
                Ok(())
            }
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
