mod eval;
mod infer;

use std::fmt::{self, Display, Formatter};
use std::hash::{Hash, Hasher};
use std::rc::Rc;

use crate::global::*;
use crate::name::Name;

pub use eval::{eval, normalize, Context as EvalContext};
pub use infer::{infer, Context as TypeContext, Error as TypeError};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ArrowKind {
    Value,
    Type,
}

pub type PTerm = Rc<Term>;

// TODO: Is our PartialOrd valid? Because we have overriden partial eq.
// Aternatively, do not implement PartialOrd and PartialEq at all.
/**
 * The syntax of our calculus. Notice that types are represented in the same way
 * as terms, which is the essence of CoC.
 */
#[derive(Debug, Clone, PartialOrd, Ord)]
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
                    && Self::substitute_or(
                        body2.clone(),
                        param_name2,
                        Var(param_name1.clone()).into(),
                    ) == *body1
            }
            (Arrow { .. }, _) => false,
            (Let(name1, annotation1, rhs1, body1), Let(name2, annotation2, rhs2, body2)) => {
                name1 == name2
                    && annotation1 == annotation2
                    && rhs1 == rhs2
                    && Self::substitute_or(body2.clone(), name2, Var(name1.clone()).into())
                        == *body1
            }
            (Let(_, _, _, _), _) => false,
            (Literal(l), Literal(r)) => l == r,
            (Literal(_), _) => false,
            (TypeAnnotation(term1, type1), TypeAnnotation(term2, type2)) => {
                term1 == term2 && type1 == type2
            }
            (TypeAnnotation(_, _), _) => false,
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
        }
    }
}

impl Term {
    pub fn is_atom(&self) -> bool {
        matches!(self, Term::Literal(_) | Term::Var(_))
    }

    pub fn free_vars(&self) -> Vec<Name> {
        use Term::*;
        match self {
            Var(var) => vec![var.clone()],
            Appl(lhs, rhs) => extend(lhs.free_vars(), rhs.free_vars()),
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
            Literal(_) => vec![],
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
        }
    }

    /*
    fn offset_free_variables_indices_with_depth(&self, offset: usize, variable_depth: usize) -> Term {
        use Term::*;
        match self {
            Var(var) if *var >= variable_depth => Var(var + offset),
            Appl(lhs, rhs) => Appl(
                Rc::new(lhs.offset_free_variables_indices_with_depth(offset, variable_depth)),
                Rc::new(rhs.offset_free_variables_indices_with_depth(offset, variable_depth)),
            ),
            Binder { binder, ty, body, } => Binder {
                binder: binder.clone(),
                ty: Rc::new(ty.offset_free_variables_indices_with_depth(offset, variable_depth)),
                body: Rc::new(body.offset_free_variables_indices_with_depth(offset, variable_depth + 1)),
            },
            Prop | Type | Var(_) => self.clone(),
        }
    }

    fn offset_free_variable_indices(&self, offset: usize) -> Term {
        self.offset_free_variables_indices_with_depth(offset, 0)
    }

    fn substitute_with_depth(&self, variable: VarIdent, replacement: Term, variable_depth: usize) -> Term {
        use Term::*;
        match self {
            Var(var) if *var == variable => replacement.offset_free_variable_indices(variable_depth),
            Appl(lhs, rhs) => {
                let replacement = replacement.offset_free_variable_indices(variable_depth);
                Appl(
                    Rc::new(lhs.substitute(variable, replacement)),
                    Rc::new(rhs.substitute(variable, replacement)),
                )
            }
            Binder { binder, ty, body } => Binder {
                binder: binder.clone(),
                ty: Rc::new(ty.substitute(variable, replacement.offset_free_variable_indices(variable_depth))),
                body: Rc::new(body.substitute(variable + 1, replacement.offset_free_variable_indices(variable_depth + 1))),
            },
            Prop | Type | Var(_) => self.clone().into(),
        }
    }

    pub fn substitute(&self, variable: VarIdent, replacement: Term) -> Term {
        self.substitute_with_depth(variable, replacement, 0)
    }
    */

    pub fn substitute_or(this: PTerm, name: &Name, replacement: PTerm) -> PTerm {
        this.substitute(name, replacement).unwrap_or(this)
    }

    pub fn substitute(&self, name: &Name, replacement: PTerm) -> Option<PTerm> {
        use Term::*;
        match self {
            Var(other_name) if other_name == name => Some(replacement),
            Appl(lhs, rhs) => match (
                lhs.substitute(name, replacement.clone()),
                rhs.substitute(name, replacement),
            ) {
                (None, None) => None,
                (lhs_new, rhs_new) => Some(
                    Appl(
                        lhs_new.as_ref().unwrap_or(lhs).clone(),
                        rhs_new.as_ref().unwrap_or(rhs).clone(),
                    )
                    .into(),
                ),
            },
            Let(bind_name, annotation, rhs, body) if bind_name == name => {
                // Don't make a substitution in the body!
                let rhs = Self::substitute_or(rhs.clone(), name, replacement.clone());
                let annotation = annotation
                    .clone()
                    .map(|a| Self::substitute_or(a, name, replacement));
                Some(Let(bind_name.clone(), annotation, rhs, body.clone()).into())
            }
            Let(bind_name, annotation, rhs, body)
                if replacement.free_vars().contains(bind_name) =>
            {
                let rhs = Self::substitute_or(rhs.clone(), name, replacement.clone());
                let annotation = annotation
                    .clone()
                    .map(|a| Self::substitute_or(a, name, replacement.clone()));

                // First replace the name of the bound variable, then do the replacement on the
                // body.
                let new_bind_name = make_name_unique(bind_name);
                let new_body = Self::substitute_or(
                    body.clone(),
                    bind_name,
                    Term::Var(new_bind_name.clone()).into(),
                )
                .pipe(|body| Self::substitute_or(body, name, replacement));

                Some(Let(new_bind_name, annotation, rhs, new_body).into())
            }
            Let(bind_name, annotation, rhs, body) => {
                let rhs_new = Self::substitute_or(rhs.clone(), name, replacement.clone());
                let body_new = Self::substitute_or(body.clone(), name, replacement.clone());
                let annotation_new = annotation
                    .as_ref()
                    .map(|ty| Self::substitute_or(ty.clone(), name, replacement));
                Some(Let(bind_name.clone(), annotation_new, rhs_new, body_new).into())
            }
            Arrow {
                kind: binder,
                param_name,
                ty,
                body,
            } if name == param_name => ty.substitute(name, replacement).map(|ty| {
                Arrow {
                    kind: *binder,
                    param_name: param_name.clone(),
                    ty,
                    body: body.clone(),
                }
                .into()
            }),
            Arrow {
                kind: binder,
                param_name,
                ty,
                body,
            } if replacement.free_vars().contains(param_name) => {
                // Change the parameter name and recurse.
                let new_param_name = make_name_unique(param_name);
                let new_binder_term = Arrow {
                    kind: *binder,
                    param_name: new_param_name.clone(),
                    ty: ty.clone(),
                    body: Self::substitute_or(
                        body.clone(),
                        param_name,
                        Term::Var(new_param_name).into(),
                    ),
                };
                Some(Self::substitute_or(
                    new_binder_term.into(),
                    name,
                    replacement,
                ))
            }
            Arrow {
                kind: binder,
                param_name,
                ty,
                body,
            } => match (
                ty.substitute(name, replacement.clone()),
                body.substitute(name, replacement),
            ) {
                (None, None) => None,
                (ty_new, body_new) => Some(
                    Arrow {
                        kind: *binder,
                        param_name: param_name.clone(),
                        ty: ty_new.as_ref().unwrap_or(ty).clone(),
                        body: body_new.as_ref().unwrap_or(body).clone(),
                    }
                    .into(),
                ),
            },
            TypeAnnotation(term, typ) => match (
                term.substitute(name, replacement.clone()),
                typ.substitute(name, replacement),
            ) {
                (None, None) => None,
                (term_new, type_new) => Some(
                    TypeAnnotation(
                        term_new.as_ref().unwrap_or(term).clone(),
                        type_new.as_ref().unwrap_or(typ).clone(),
                    )
                    .into(),
                ),
            },
            Var(_) | Literal(_) => None,
        }
    }

    /*
    fn eval_with_stack(&self, stack: &mut Vec<Option<Term>>) -> Term {
        use Term::*;
        match self {
            Var(var) => stack[stack.len() - 1 - *var]
                .clone()
                .unwrap_or_else(|| self.clone()),
            Appl(lhs, rhs) => {
                let lhs = lhs.eval_with_stack(stack);
                let rhs = rhs.eval_with_stack(stack);
                if let Binder { body, .. } = lhs {
                    stack.push(Some(rhs));
                    let result = body.eval_with_stack(stack);
                    stack.pop();
                    result
                } else {
                    Appl(Rc::new(lhs), Rc::new(rhs))
                }
            }
            Binder { binder, ty, body } => Binder {
                binder: binder.clone(),
                ty: Rc::new(ty.eval_with_stack(stack)),
                body: {
                    stack.push(None);
                    let body = body.eval_with_stack(stack);
                    stack.pop();
                    Rc::new(body)
                },
            },
            Prop | Type => self.clone(),
        }
    }

    pub fn eval(&self) -> Term {
        let mut stack = Vec::new();
        self.eval_with_stack(&mut stack)
    }
    */
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
                write!(f, "(let {name} : {annotation} = {rhs} in {body})",)
            }
            Let(name, None, rhs, body) => write!(f, "(let {name} = {rhs} in {body})",),
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

fn make_name_unique(name: &str) -> Name {
    Name::from(format!("{name}^"))
}
