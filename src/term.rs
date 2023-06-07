mod display;
mod eval;
mod infer;

use std::collections::HashSet;
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

    fn inc_by(&self, inc: usize) -> DeBruijn {
        DeBruijn(self.0 + inc)
    }

    fn inc(&self) -> DeBruijn {
        self.inc_by(1)
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
    UnionType(Vec<PTerm>),
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
            Term::UnionType(elements) => {
                elements.iter().all(|e| e.is_reduced()) && is_sorted(elements)
            }
        }
    }

    pub fn declares_var(&self) -> bool {
        matches!(self, Term::Let(..) | Term::Arrow { .. })
    }

    pub fn children(&self) -> Vec<PTerm> {
        match self {
            Term::Literal(_) | Term::Var(_) => vec![],
            Term::Tuple(elements) | Term::TupleType(elements) | Term::UnionType(elements) => {
                elements.clone()
            }
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
            stack.extend(term.children().into_iter().map(|t| (inner_depth, t)));

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

    pub fn increase_de_bruijns_not_bellow(self: &PTerm, inc: usize, not_bellow: usize) -> PTerm {
        match self.as_ref() {
            Term::Appl(left, right) => Term::Appl(
                left.increase_de_bruijns_not_bellow(inc, not_bellow),
                right.increase_de_bruijns_not_bellow(inc, not_bellow),
            )
            .into(),
            Term::TypeAnnotation(left, right) => Term::TypeAnnotation(
                left.increase_de_bruijns_not_bellow(inc, not_bellow),
                right.increase_de_bruijns_not_bellow(inc, not_bellow),
            )
            .into(),
            Term::Literal(_) => self.clone(),
            Term::Var(de_bruijn) if de_bruijn.0 < not_bellow => self.clone(),
            Term::Var(de_bruijn) => de_bruijn.inc_by(inc).pipe(Term::Var).into(),
            Term::Tuple(elements) => Term::Tuple(
                elements
                    .iter()
                    .map(|t| t.increase_de_bruijns_not_bellow(inc, not_bellow))
                    .collect(),
            )
            .into(),
            Term::TupleType(elements) => Term::TupleType(
                elements
                    .iter()
                    .map(|t| t.increase_de_bruijns_not_bellow(inc, not_bellow))
                    .collect(),
            )
            .into(),
            Term::UnionType(elements) => Term::UnionType(
                elements
                    .iter()
                    .map(|t| t.increase_de_bruijns_not_bellow(inc, not_bellow))
                    .collect(),
            )
            .into(),
            Term::Arrow { kind, ty, body } => Term::Arrow {
                kind: *kind,
                ty: ty.increase_de_bruijns_not_bellow(inc, not_bellow),
                body: body.increase_de_bruijns_not_bellow(inc, not_bellow + 1),
            }
            .into(),
            Term::Let(annot, right, ret) => Term::Let(
                annot
                    .as_ref()
                    .map(|annot| annot.increase_de_bruijns_not_bellow(inc, not_bellow)),
                right.increase_de_bruijns_not_bellow(inc, not_bellow),
                ret.increase_de_bruijns_not_bellow(inc, not_bellow + 1),
            )
            .into(),
            Term::Match(input, cases) => Term::Match(
                input.increase_de_bruijns_not_bellow(inc, not_bellow),
                cases
                    .iter()
                    .map(|(pat, body)| {
                        (
                            pat.clone(),
                            body.increase_de_bruijns_not_bellow(inc, not_bellow + pat.vars()),
                        )
                    })
                    .collect(),
            )
            .into(),
        }
    }

    pub fn increase_de_bruijns(self: &PTerm, inc: usize) -> PTerm {
        self.increase_de_bruijns_not_bellow(inc, 0)
    }

    /// Returns true only if this instance is a subtype of the other instance.
    /// Both terms must be evaluated.
    pub fn is_subtype(self: &Term, other: &Term) -> bool {
        self == other || {
            if let Term::UnionType(possible_types) = other {
                possible_types.iter().any(|t| self.is_subtype(t))
            } else {
                false
            }
        }
    }

    pub fn supertype(types: &[PTerm]) -> PTerm {
        assert!(!types.is_empty());

        // Construct a minimal union of all the types.
        eval(&Term::UnionType(types.to_vec()).into(), &mut Default::default())
    }
}
