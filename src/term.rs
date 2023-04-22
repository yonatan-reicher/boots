mod eval;
mod infer;

use std::collections::HashSet;
use std::fmt::{self, Display, Formatter};
use std::hash::{Hash, Hasher};
use std::rc::Rc;

use crate::global::*;
use crate::name::Name;
use crate::yes_no::{No, Yes, YesNo};

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

pub type PTerm<Reduced = No> = Rc<Term<Reduced>>;
pub type PTermReduced = PTerm<Yes>;
pub type TermReduced = Term<Yes>;

// TODO: Is our PartialOrd valid? Because we have overriden partial eq.
// Aternatively, do not implement PartialOrd and PartialEq at all.
/**
 * The syntax of our calculus. Notice that types are represented in the same way
 * as terms, which is the essence of CoC.
 */
#[derive(Debug, PartialOrd, Ord)]
pub enum Term<Reduced: YesNo = No> {
    Appl(Reduced::Not, PTerm, PTerm),
    Arrow {
        kind: ArrowKind,
        param_name: Name,
        ty: PTerm<Reduced>,
        body: PTerm,
    },
    Literal(Literal),
    TypeAnnotation(Reduced::Not, PTerm, PTerm),
    Var(Reduced::Not, Name),
    Let(Reduced::Not, Name, Option<PTerm>, PTerm, PTerm),
    Tuple(Vec<PTerm<Reduced>>),
    TupleType(Vec<PTerm<Reduced>>),
    Match(Reduced::Not, PTerm, Vec<(Rc<Pattern>, PTerm)>),
}

#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub enum Literal {
    Prop,
    Str,
    StringAppend,
    String(Name),
    Type,
}

impl<Reduced: YesNo> From<Literal> for Term<Reduced> {
    fn from(literal: Literal) -> Self {
        Term::Literal(literal)
    }
}

impl<Reduced: YesNo> From<Literal> for PTerm<Reduced> {
    fn from(literal: Literal) -> Self {
        Rc::new(literal.into())
    }
}

impl<Reduced: YesNo> PartialEq for Term<Reduced> {
    fn eq(&self, other: &Self) -> bool {
        use Term::*;
        match (self, other) {
            (Var(_, name1), Var(_, name2)) => name1 == name2,
            (Var(_, _), _) => false,
            (Appl(_, left1, right1), Appl(_, left2, right2)) => left1 == left2 && right1 == right2,
            (Appl(_, _, _), _) => false,
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
                    && substitute(body2, param_name2, &Term::var(param_name1.clone()).into()) == *body1
            }
            (Arrow { .. }, _) => false,
            (Let(_, name1, annotation1, rhs1, body1), Let(_, name2, annotation2, rhs2, body2)) => {
                name1 == name2
                    && annotation1 == annotation2
                    && rhs1 == rhs2
                    && substitute(body2, name2, &Term::var(name1.clone()).into()) == *body1
            }
            (Let(..), _) => false,
            (Literal(l), Literal(r)) => l == r,
            (Literal(_), _) => false,
            (TypeAnnotation(_, term1, type1), TypeAnnotation(_, term2, type2)) => {
                term1 == term2 && type1 == type2
            }
            (TypeAnnotation(_, _, _), _) => false,
            (Tuple(elements1), Tuple(elements2)) => elements1 == elements2,
            (Tuple(_), _) => false,
            (TupleType(elements1), TupleType(elements2)) => elements1 == elements2,
            (TupleType(_), _) => false,
            (Match(_, term1, cases1), Match(_, term2, cases2)) => term1 == term2 && cases1 == cases2,
            (Match(..), _) => false,
        }
    }
}

impl<Reduced: YesNo> Eq for Term<Reduced> {}

impl<Reduced: YesNo> Hash for Term<Reduced> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        core::mem::discriminant(self).hash(state);
        match self {
            Term::Var(..) => {}
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
            Term::TypeAnnotation(_, term, ty) => {
                term.hash(state);
                ty.hash(state);
            }
            Term::Literal(l) => l.hash(state),
            Term::Appl(_, term1, term2) => {
                term1.hash(state);
                term2.hash(state);
            }
            Term::Let(_, name, _, rhs, body) => {
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
            Term::Match(_, inner, cases) => {
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

impl<Reduced: YesNo> Term<Reduced> {
    pub fn into_pterm(self) -> PTerm<Reduced> {
        Rc::new(self)
    }

    pub fn is_atom(&self) -> bool {
        matches!(
            self,
            Term::Literal(_) | Term::Var(_, _) | Term::Tuple(_) | Term::TupleType(_)
        )
    }

    pub fn free_vars(&self) -> HashSet<Name> {
        use Term::*;
        match self {
            Var(_, var) => [var.clone()].into(),
            Appl(_, lhs, rhs) => lhs.free_vars().extend_pipe(rhs.free_vars()),
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
            TypeAnnotation(_, term, ty) => extend(term.free_vars(), ty.free_vars()),
            Literal(_) => HashSet::new(),
            Let(_, name, annotation, rhs, body) => annotation
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
            Match(_, inner, cases) => inner.free_vars().extend_pipe(
                cases
                    .iter()
                    .flat_map(|(pat, case)| &case.free_vars() - &pat.free_vars()),
            ),
        }
    }
}

fn is_tuple_reduced(elements: &[PTerm]) -> Option<Vec<PTermReduced>> {
    elements
        .iter()
        .map(|e| e.is_reduced().map(Term::into_pterm))
        .collect()
}

impl Term {
    pub fn var(name: Name) -> Self {
        Term::Var(Yes, name)
    }

    pub fn appl(left: PTerm, right: PTerm) -> Self {
        Term::Appl(Yes, left, right)
    }

    pub fn match_(input: PTerm, cases: Vec<(Rc<Pattern>, PTerm)>) -> Self {
        Term::Match(Yes, input, cases)
    }

    pub fn type_annotation(left: PTerm, right: PTerm) -> Self {
        Term::TypeAnnotation(Yes, left, right)
    }

    pub fn let_(name: Name, annot: Option<PTerm>, bind: PTerm, ret: PTerm) -> Self {
        Term::Let(Yes, name, annot, bind, ret)
    }

    pub fn is_reduced(&self) -> Option<TermReduced> {
        match self {
            Term::Literal(lit) => Some(TermReduced::Literal(lit.clone())),
            Term::Tuple(elements) => is_tuple_reduced(elements).map(TermReduced::Tuple),
            Term::TupleType(elements) => is_tuple_reduced(elements).map(TermReduced::TupleType),
            Term::Arrow {
                kind,
                param_name,
                ty,
                body,
            } => {
                Some(TermReduced::Arrow {
                    kind: kind.clone(),
                    param_name: param_name.clone(),
                    ty: ty.is_reduced()?.into(),
                    body: body.clone(), // The body does not need to be reduced.
                })
            }
            Term::Appl(..) => None,
            Term::TypeAnnotation(..) => None,
            Term::Var(..) => None,
            Term::Let(..) => None,
            Term::Match(..) => None,
        }
    }
}

fn tuple_to_not_reduced(elements: &[PTermReduced]) -> Vec<PTerm> {
    elements
        .iter()
        .map(|e| e.to_not_reduced().into_pterm())
        .collect()
}

impl TermReduced {
    pub fn to_not_reduced(&self) -> Term {
        match self {
            Term::Var(not, _)
            | Term::Let(not, ..)
            | Term::Match(not, ..)
            | Term::Appl(not, ..)
            | Term::TypeAnnotation(not, ..) => not.into_anything(),
            Term::Arrow {
                kind,
                param_name,
                ty,
                body,
            } => Term::Arrow {
                kind: kind.clone(),
                param_name: param_name.clone(),
                ty: ty.to_not_reduced().into(),
                body: body.clone(),
            },
            Term::Literal(lit) => Term::Literal(lit.clone()),
            Term::Tuple(elements) => Term::Tuple(tuple_to_not_reduced(elements)),
            Term::TupleType(elements) => Term::TupleType(tuple_to_not_reduced(elements)),
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
            Var(_, name) => name.fmt(f),
            Appl(_, lhs, rhs) => {
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
            TypeAnnotation(_, term, typ) => write!(f, "{term} : {typ}"),
            Literal(literal) => write!(f, "{literal}"),
            Let(_, name, Some(annotation), rhs, body) => {
                write!(f, "let {name} : {annotation} = {rhs} in {body}",)
            }
            Let(_, name, None, rhs, body) => write!(f, "let {name} = {rhs} in {body}",),
            Tuple(vec) => fmt_tuple(f, vec, '(', ')'),
            TupleType(vec) => fmt_tuple(f, vec, '{', '}'),
            Match(_, term, cases) => {
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
