mod eval;
mod infer;

use std::collections::HashSet;
use std::fmt::{self, Display, Formatter};
use std::hash::{Hash, Hasher};
use std::rc::Rc;

use crate::global::*;
use crate::name::Name;

pub use eval::{eval, normalize, substitute, Context as EvalContext};
pub use infer::{infer, Context as TypeContext, Error as TypeError};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ArrowKind {
    Value,
    Type,
}

#[derive(Debug, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Pattern {
    Var(Name),
    UnTuple(Vec<Pattern>),
    String(Name),
}

pub type PTerm = Rc<Term>;

// TODO: Is our PartialOrd valid? Because we have overriden partial eq.
// Aternatively, do not implement PartialOrd and PartialEq at all.
/**
 * The syntax of our calculus. Notice that types are represented in the same way
 * as terms, which is the essence of CoC.
 */
#[derive(Debug, PartialOrd, Ord)]
pub enum Term {
    Appl(PTerm, PTerm),
    Arrow {
        kind: ArrowKind,
        param_name: Name,
        ty: PTerm,
        body: PTerm,
    },
    Literal(Literal),
    TypeAnnotation(PTerm, PTerm),
    Var(Name),
    Let(Name, Option<PTerm>, PTerm, PTerm),
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

impl PartialEq for Term {
    fn eq(&self, other: &Self) -> bool {
        use Term::*;
        match (self, other) {
            (Var(name1), Var(name2)) => name1 == name2,
            (Var(_), _) => false,
            (Appl(left1, right1), Appl(left2, right2)) => left1 == left2 && right1 == right2,
            (Appl(_, _), _) => false,
            (
                Arrow {
                    kind: binder1,
                    param_name: param_name1,
                    ty: ty1,
                    body: body1,
                },
                Arrow {
                    kind: binder2,
                    param_name: param_name2,
                    ty: ty2,
                    body: body2,
                },
            ) => {
                binder1 == binder2
                    && ty1 == ty2
                    && substitute(body2, param_name2, &Var(param_name1.clone()).into()) == *body1
            }
            (Arrow { .. }, _) => false,
            (Let(name1, annotation1, rhs1, body1), Let(name2, annotation2, rhs2, body2)) => {
                name1 == name2
                    && annotation1 == annotation2
                    && rhs1 == rhs2
                    && substitute(body2, name2, &Var(name1.clone()).into()) == *body1
            }
            (Let(_, _, _, _), _) => false,
            (Literal(l), Literal(r)) => l == r,
            (Literal(_), _) => false,
            (TypeAnnotation(term1, type1), TypeAnnotation(term2, type2)) => {
                term1 == term2 && type1 == type2
            }
            (TypeAnnotation(_, _), _) => false,
            (Tuple(elements1), Tuple(elements2)) => elements1 == elements2,
            (Tuple(_), _) => false,
            (TupleType(elements1), TupleType(elements2)) => elements1 == elements2,
            (TupleType(_), _) => false,
            (Match(term1, cases1), Match(term2, cases2)) => term1 == term2 && cases1 == cases2,
            (Match(_, _), _) => false,
        }
    }
}

impl Eq for Term {}

impl Hash for Term {
    fn hash<H: Hasher>(&self, state: &mut H) {
        core::mem::discriminant(self).hash(state);
        match self {
            Term::Var(_) => {}
            Term::Arrow {
                kind: binder,
                param_name: _,
                ty,
                body,
            } => {
                binder.hash(state);
                ty.hash(state);
                body.hash(state);
            }
            Term::TypeAnnotation(term, ty) => {
                term.hash(state);
                ty.hash(state);
            }
            Term::Literal(l) => l.hash(state),
            Term::Appl(term1, term2) => {
                term1.hash(state);
                term2.hash(state);
            }
            Term::Let(name, _, rhs, body) => {
                name.hash(state);
                rhs.hash(state);
                body.hash(state);
            }
            Term::Tuple(elements) => {
                for element in elements {
                    element.hash(state);
                }
            }
            Term::TupleType(elements) => {
                for element in elements {
                    element.hash(state);
                }
            }
            Term::Match(inner, cases) => {
                inner.hash(state);
                cases.hash(state);
            }
        }
    }
}

impl Pattern {
    pub fn free_vars(&self) -> HashSet<Name> {
        match self {
            Pattern::Var(name) => [name.clone()].into(),
            Pattern::UnTuple(patterns) => patterns.iter().flat_map(|p| p.free_vars()).collect(),
            Pattern::String(_) => [].into(),
        }
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
            Term::Arrow { .. } => true, // TODO: Is this correct? Are all functions reduced?
            Term::Appl(_, _) => false,
            Term::TypeAnnotation(_, _) => false,
            Term::Var(_) => false,
            Term::Let(_, _, _, _) => false,
            Term::Match(_, _) => false,
        }
    }

    pub fn free_vars(&self) -> HashSet<Name> {
        use Term::*;
        match self {
            Var(var) => [var.clone()].into(),
            Appl(lhs, rhs) => lhs.free_vars().extend_pipe(rhs.free_vars()),
            Arrow {
                param_name: name,
                ty,
                body,
                ..
            } => extend(
                ty.free_vars(),
                body.free_vars()
                    .into_iter()
                    .filter(|var_ident| var_ident != name),
            ),
            TypeAnnotation(term, ty) => extend(term.free_vars(), ty.free_vars()),
            Literal(_) => HashSet::new(),
            Let(name, annotation, rhs, body) => annotation
                .as_ref()
                .map(|x| x.free_vars())
                .unwrap_or_default()
                .extend_pipe(rhs.free_vars())
                .extend_pipe(
                    body.free_vars()
                        .into_iter()
                        .filter(|var_ident| var_ident != name),
                ),
            Tuple(vec) => vec.iter().flat_map(|x| x.free_vars()).collect(),
            TupleType(vec) => vec.iter().flat_map(|x| x.free_vars()).collect(),
            Match(inner, cases) => inner.free_vars().extend_pipe(
                cases
                    .iter()
                    .flat_map(|(pat, case)| &case.free_vars() - &pat.free_vars()),
            ),
        }
    }
}

/*
fn generate_variable_name(variable_num: usize) -> String {
    let letter = (variable_num % 26) as u8 + b'a';
    let num = variable_num / 26;
    if num == 0 {
        format!("{}", letter as char)
    } else {
        format!("{}{}", num, letter as char)
    }
}

struct TermPrint<'a> {
    term: &'a Term,
    variable_depth: usize,
}

impl<'a> Display for TermPrint<'a> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        use Term::*;
        match self.term {
            Var(var) => {
                let var_name = generate_variable_name(self.variable_depth - 1 - *var);
                write!(f, "{}", var_name)
            }
            Appl(lhs, rhs) => write!(
                f,
                "({} {})",
                TermPrint { term: lhs, ..*self },
                TermPrint { term: rhs, ..*self },
            ),
            Binder { binder, ty, body } => write!(
                f,
                "({}{}: {}. {})",
                binder.to_string(),
                generate_variable_name(self.variable_depth),
                TermPrint { term: ty, ..*self },
                TermPrint {
                    term: body,
                    variable_depth: self.variable_depth + 1,
                    ..*self
                },
            ),
            Prop => write!(f, "Prop"),
            Type => write!(f, "Type"),
        }
    }
}
*/

fn fmt_tuple(f: &mut Formatter, terms: &[impl Display], start: char, end: char) -> fmt::Result {
    write!(f, "{start}")?;
    for (i, term) in terms.iter().enumerate() {
        write!(f, "{term}")?;
        let comma_needed = i < terms.len() - 1 || terms.len() == 1;
        if comma_needed {
            write!(f, ", ")?;
        }
    }
    write!(f, "{end}")
}

impl Display for Pattern {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Pattern::Var(var) => write!(f, "{}", var),
            Pattern::UnTuple(terms) => fmt_tuple(f, terms, '(', ')'),
            Pattern::String(s) => write!(f, "{:?}", s),
        }
    }
}

impl Display for Term {
    /*
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        TermPrint {
            term: self,
            variable_depth: 0,
        }
        .fmt(f)
    }
    */

    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        use Term::*;

        struct FmtParen<'a>(&'a Term);

        impl<'a> Display for FmtParen<'a> {
            fn fmt(&self, f: &mut Formatter) -> fmt::Result {
                if self.0.is_atom() {
                    write!(f, "{}", self.0)
                } else {
                    write!(f, "({})", self.0)
                }
            }
        }

        match self {
            Var(name) => name.fmt(f),
            Appl(lhs, rhs) => {
                if std::matches!(lhs.as_ref(), Appl(..)) {
                    write!(f, "{} {}", lhs, FmtParen(rhs))
                } else {
                    write!(f, "{} {}", FmtParen(lhs), FmtParen(rhs))
                }
            }
            Arrow {
                kind: ArrowKind::Type,
                param_name,
                ty,
                body,
            } if body.free_vars().iter().all(|x| x != param_name) => {
                write!(f, "{} -> {}", FmtParen(ty), body)
            }
            Arrow {
                kind: binder,
                param_name,
                ty,
                body,
            } => write!(
                f,
                "({param_name}: {ty}) {arrow} {body}",
                arrow = match binder {
                    ArrowKind::Type => "->",
                    ArrowKind::Value => "=>",
                },
            ),
            TypeAnnotation(term, typ) => write!(f, "{term} : {typ}"),
            Literal(literal) => write!(f, "{literal}"),
            Let(name, Some(annotation), rhs, body) => {
                write!(f, "let {name} : {annotation} = {rhs} in {body}",)
            }
            Let(name, None, rhs, body) => write!(f, "let {name} = {rhs} in {body}",),
            Tuple(vec) => fmt_tuple(f, vec, '(', ')'),
            TupleType(vec) => fmt_tuple(f, vec, '{', '}'),
            Match(term, cases) => {
                write!(f, "match {term} with {{ ")?;
                for (pattern, body) in cases {
                    write!(f, "{pattern} => {body} ",)?;
                }
                write!(f, "}}")?;
                Ok(())
            }
        }
    }
}

impl Display for Literal {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
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
