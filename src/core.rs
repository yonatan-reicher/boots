use std::fmt::{self, Display, Formatter};
use std::rc::Rc;

use crate::global::*;
use crate::name::Name;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum BinderKind {
    Lam,
    Pi,
}

/*
impl Display for BinderKind {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            BinderKind::Lam => write!(f, "λ"),
            BinderKind::Pi => write!(f, "Π"),
        }
    }
}
*/

pub type PTerm = Rc<Term>;

pub type TypeContext = std::collections::HashMap<Name, PTerm>;

/**
 * The syntax of our calculus. Notice that types are represented in the same way
 * as terms, which is the essence of CoC.
 */
#[derive(Debug, Clone, PartialOrd, Ord)]
pub enum Term {
    Appl(PTerm, PTerm),
    Binder {
        binder: BinderKind,
        param_name: Name,
        ty: PTerm,
        body: PTerm,
    },
    Prop,
    Str,
    StringAppend,
    StringLiteral(String),
    Type,
    TypeAnnotation(PTerm, PTerm),
    Var(Name),
    Let(Name, Option<PTerm>, PTerm, PTerm),
}

fn result_combine<T, U, E>(
    left: Result<T, Vec<E>>,
    right: Result<U, Vec<E>>,
) -> Result<(T, U), Vec<E>> {
    match (left, right) {
        (Ok(l), Ok(r)) => Ok((l, r)),
        (Err(l), Err(r)) => Err(extend(l, r)),
        (Err(l), _) => Err(l),
        (_, Err(r)) => Err(r),
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
                Binder {
                    binder: binder1,
                    param_name: param_name1,
                    ty: ty1,
                    body: body1,
                },
                Binder {
                    binder: binder2,
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
            (Binder { .. }, _) => false,
            (Let(name1, annotation1, rhs1, body1), Let(name2, annotation2, rhs2, body2)) => {
                name1 == name2
                    && annotation1 == annotation2
                    && rhs1 == rhs2
                    && Self::substitute_or(body2.clone(), name2, Var(name1.clone()).into())
                        == *body1
            }
            (Let(_, _, _, _), _) => false,
            (Prop, Prop) => true,
            (Prop, _) => false,
            (Type, Type) => true,
            (Type, _) => false,
            (TypeAnnotation(term1, type1), TypeAnnotation(term2, type2)) => {
                term1 == term2 && type1 == type2
            }
            (TypeAnnotation(_, _), _) => false,
            (StringLiteral(s1), StringLiteral(s2)) => s1 == s2,
            (StringLiteral(_), _) => false,
            (Str, Str) => true,
            (Str, _) => false,
            (StringAppend, StringAppend) => true,
            (StringAppend, _) => false,
        }
    }
}

impl Eq for Term {}

impl std::hash::Hash for Term {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        core::mem::discriminant(self).hash(state);
        match self {
            Term::Var(_) => {}
            Term::Binder {
                binder,
                param_name: _,
                ty,
                body,
            } => {
                binder.hash(state);
                ty.hash(state);
                body.hash(state);
            }
            Term::Prop => (),
            Term::Type => (),
            Term::TypeAnnotation(term, ty) => {
                term.hash(state);
                ty.hash(state);
            }
            Term::StringLiteral(s) => s.hash(state),
            Term::Str => (),
            Term::StringAppend => (),
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
        std::matches!(
            self,
            Term::Var(_)
                | Term::Prop
                | Term::Type
                | Term::StringAppend
                | Term::StringLiteral(_)
                | Term::Str
        )
    }

    pub fn free_vars(&self) -> Vec<Name> {
        use Term::*;
        match self {
            Var(var) => vec![var.clone()],
            Appl(lhs, rhs) => extend(lhs.free_vars(), rhs.free_vars()),
            Binder {
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
            Prop | Type | StringLiteral(_) | Str | StringAppend => vec![],
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
                let rhs_new = Self::substitute_or(rhs.clone(), name, replacement);
                todo!()
            }
            Let(bind_name, annotation, rhs, body)
                if replacement.free_vars().contains(bind_name) =>
            {
                todo!()
            }
            Let(bind_name, annotation, rhs, body) => {
                let rhs_new = Self::substitute_or(rhs.clone(), name, replacement.clone());
                let body_new = Self::substitute_or(body.clone(), name, replacement.clone());
                let annotation_new = annotation
                    .as_ref()
                    .map(|ty| Self::substitute_or(ty.clone(), name, replacement));
                Some(Let(bind_name.clone(), annotation_new, rhs_new, body_new).into())
            }
            Binder {
                binder,
                param_name,
                ty,
                body,
            } if name == param_name => ty.substitute(name, replacement).map(|ty| {
                Binder {
                    binder: *binder,
                    param_name: param_name.clone(),
                    ty,
                    body: body.clone(),
                }
                .into()
            }),
            Binder {
                binder,
                param_name,
                ty,
                body,
            } if replacement.free_vars().contains(param_name) => {
                // Change the parameter name and recurse.
                let new_param_name: Name = format!("{param_name}_").into();
                let new_binder_term = Binder {
                    binder: *binder,
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
            Binder {
                binder,
                param_name,
                ty,
                body,
            } => match (
                ty.substitute(name, replacement.clone()),
                body.substitute(name, replacement),
            ) {
                (None, None) => None,
                (ty_new, body_new) => Some(
                    Binder {
                        binder: *binder,
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
            Prop | Type | Var(_) | StringLiteral(_) | Str | StringAppend => None,
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

    pub fn eval_or(this: PTerm) -> PTerm {
        this.eval().unwrap_or(this)
    }

    pub fn eval(&self) -> Option<PTerm> {
        use Term::*;
        match self {
            Appl(lhs, rhs) => {
                let lhs_new = lhs.eval();
                let rhs_new = rhs.eval();
                let lhs = lhs_new.as_ref().unwrap_or(lhs);
                let rhs = rhs_new.as_ref().unwrap_or(rhs);

                if let Binder {
                    body, param_name, ..
                } = lhs.as_ref()
                {
                    // Substitute the parameter inside the body and then eval again.
                    let ret = Self::substitute_or(body.clone(), param_name, rhs.clone());
                    let ret = Self::eval_or(ret);
                    return Some(ret);
                }

                if let Appl(func, arg1) = lhs.as_ref() {
                    if let (StringAppend, StringLiteral(s1), StringLiteral(s2)) =
                        (func.as_ref(), arg1.as_ref(), rhs.as_ref())
                    {
                        return Some(StringLiteral(format!("{s1}{s2}")).into());
                    }
                }

                if lhs_new.is_none() && rhs_new.is_none() {
                    return None;
                }

                Some(Appl(lhs.clone(), rhs.clone()).into())
            }
            Binder {
                binder,
                param_name,
                ty,
                body,
            } => {
                let ty_new = ty.eval();
                let body_new = body.eval();
                let ty = ty_new.as_ref().unwrap_or(ty);
                let body = body_new.as_ref().unwrap_or(body);

                if ty_new.is_none() && body_new.is_none() {
                    return None;
                }

                Some(
                    Binder {
                        binder: *binder,
                        param_name: param_name.clone(),
                        ty: ty.clone(),
                        body: body.clone(),
                    }
                    .into(),
                )
            }
            Let(name, _, rhs, body) => Self::substitute_or(body.clone(), name, rhs.clone())
                .pipe(|x| Self::eval_or(x))
                .pipe(Some),
            TypeAnnotation(term, _) => term.eval(),
            Prop | Type | Var(_) | StringLiteral(_) | Str | StringAppend => None,
        }
    }

    pub fn infer_type_with_ctx(
        &self,
        variable_types: &mut TypeContext,
    ) -> Result<PTerm, Vec<String>> {
        use Term::*;
        match self {
            Var(var) => variable_types.get(var.as_ref()).cloned().ok_or_else(|| {
                vec![format!(
                    "You refered to a variable '{var}' which does not exist \
                    in this context!",
                )]
            }),
            Appl(lhs, rhs) => {
                let (lhs_type, rhs_type) = result_combine(
                    lhs.infer_type_with_ctx(variable_types),
                    rhs.infer_type_with_ctx(variable_types),
                )?;
                if let Binder {
                    binder: BinderKind::Pi,
                    param_name,
                    ty,
                    body,
                } = lhs_type.as_ref()
                {
                    // Check the type of the argument matches the type of the
                    // parameter.
                    if ty != &rhs_type {
                        return Err(vec![format!(
                            "Argument type mismatch in {self}: \
                             expected {ty}, found {rhs_type}",
                        )]);
                    }

                    Ok(Self::substitute_or(body.clone(), param_name, rhs_type))
                } else {
                    Err(vec![format!(
                        "Application of argument {rhs} (type {rhs_type}) \
                         to non-lambda {lhs} (type {lhs_type})",
                    )])
                }
            }
            Binder {
                binder: BinderKind::Lam,
                param_name,
                ty,
                body,
            } => {
                // Get the type of the body.
                let body_type = with_variable!(variable_types, (param_name, Rc::clone(ty)), {
                    body.infer_type_with_ctx(variable_types)?
                });
                // The lambda's type is a pi type.
                let lam_type = Binder {
                    binder: BinderKind::Pi,
                    param_name: param_name.clone(),
                    ty: Rc::clone(ty),
                    body: body_type,
                };
                // Make sure this binder type checks.
                lam_type.infer_type_with_ctx(variable_types)?;
                Ok(Self::eval_or(lam_type.into()))
            }
            Binder {
                binder: BinderKind::Pi,
                param_name,
                ty,
                body,
            } => {
                // Check that `ty`'s type could be infered.
                ty.infer_type_with_ctx(variable_types)?;
                // Get the type of the body.
                let body_type = with_variable!(variable_types, (param_name, ty.clone()), {
                    body.infer_type_with_ctx(variable_types)?
                });
                // The pi binder's type is the type of the body.
                Ok(body_type)
            }
            TypeAnnotation(term, typ) => {
                // Check that the type of term matches the type annotation.
                let term_type = term.infer_type_with_ctx(variable_types)?;
                if term_type != *typ {
                    Err(vec![format!(
                        "Type annotation mismatch: {term_type} != {typ}",
                    )])
                } else {
                    Ok(term_type)
                }
            }
            Prop => Ok(Type.into()),
            Type => Ok(Type.into()),
            StringLiteral(_) => Ok(Str.into()),
            Str => Ok(Type.into()),
            StringAppend => Ok(Binder {
                binder: BinderKind::Pi,
                param_name: "s1".into(),
                ty: Str.into(),
                body: Binder {
                    binder: BinderKind::Pi,
                    param_name: "s2".into(),
                    ty: Str.into(),
                    body: Str.into(),
                }
                .into(),
            }
            .into()),
            Let(name, annotation, rhs, body) => {
                let rhs_type = rhs.infer_type_with_ctx(variable_types)?;
                if let Some(annotation) = annotation {
                    if rhs_type != *annotation {
                        return Err(vec![format!(
                            "Type annotation mismatch: {rhs_type} != {annotation}",
                        )]);
                    }
                }
                with_variable!(variable_types, (name, rhs_type), {
                    body.infer_type_with_ctx(variable_types)
                })
            } // Type => Err(vec![format!("Type's type cannot be inferred")]),
        }
    }

    pub fn infer_type(&self) -> Result<PTerm, Vec<String>> {
        let mut variable_types = TypeContext::new();
        let res = self.infer_type_with_ctx(&mut variable_types);
        assert!(variable_types.is_empty());
        res
    }
}

/*
(* A list of variable declarations for type inference. *)
type context = (string * term) list

(* Infers a type, in beta normal form, of a term in a given (well-formed)
   context; throws an exception otherwise. *)
let rec infer_type_with_ctx (ctx : context) (t : term) =
  let infer = infer_type_with_ctx in
  match t with
  | Var x -> eval (List.assoc x ctx)
  | Appl (m, n) -> (
      match (infer ctx m, infer ctx n) with
      | Binder (Pi, x, ty, m), arg_ty ->
          if alpha_eq ty arg_ty then eval (subst m x n)
          else
            failwith
              (Printf.sprintf
                 "Argument type mismatch in %s: expected %s, found %s" (print t)
                 (print ty) (print arg_ty))
      | m_ty, n_ty ->
          failwith
            (Printf.sprintf
               "Application of argument %s (type %s) to non-lambda %s (type %s)"
               (print n) (print n_ty) (print m) (print m_ty)))
  | Binder (Lam, x, ty, m) ->
      let m_ty = infer ((x, ty) :: ctx) m in
      let lam_ty = Binder (Pi, x, ty, m_ty) in
      let _ = infer ctx lam_ty in
      eval lam_ty
  | Binder (Pi, x, ty, m) ->
      let _s1 = infer ctx ty in
      let s2 = infer ((x, ty) :: ctx) m in
      s2
  | Star -> Box
  | Box -> failwith "☐ has no type"

let infer_type t = infer_type_with_ctx [] t

let type_check_with_ctx ctx t expected =
  assert (alpha_eq (infer_type_with_ctx ctx t) (eval expected))

let type_check t expected = type_check_with_ctx [] t expected
*/

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
            Binder {
                binder: BinderKind::Pi,
                param_name,
                ty,
                body,
            } if body.free_vars().iter().all(|x| x != param_name) => {
                write!(f, "{} -> {}", FmtParen(ty), body)
            }
            Binder {
                binder,
                param_name,
                ty,
                body,
            } => write!(
                f,
                "({param_name}: {ty}) {arrow} {body}",
                arrow = match binder {
                    BinderKind::Pi => "->",
                    BinderKind::Lam => "=>",
                },
            ),
            TypeAnnotation(term, typ) => write!(f, "{term} : {typ}"),
            Prop => write!(f, "prop"),
            Type => write!(f, "type"),
            StringLiteral(s) => write!(f, "\"{s}\""),
            Str => write!(f, "str"),
            StringAppend => write!(f, "<string-append>"),
            Let(name, Some(annotation), rhs, body) => {
                write!(f, "(let {name} : {annotation} = {rhs} in {body})",)
            }
            Let(name, None, rhs, body) => write!(f, "(let {name} = {rhs} in {body})",),
        }
    }
}