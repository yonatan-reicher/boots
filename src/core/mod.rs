use std::fmt::{self, Display, Formatter};
use std::rc::Rc;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum BinderKind {
    Lam,
    Pi,
}

impl Display for BinderKind {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            BinderKind::Lam => write!(f, "λ"),
            BinderKind::Pi => write!(f, "Π"),
        }
    }
}

pub type VarIdent = usize;

/**
 * The syntax of our calculus. Notice that types are represented in the same way
 * as terms, which is the essence of CoC.
 */
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Term {
    Var(VarIdent),
    Appl(Rc<Term>, Rc<Term>),
    Binder {
        binder: BinderKind,
        ty: Rc<Term>,
        body: Rc<Term>,
    },
    Prop,
    Type,
}

fn extend<T, I: IntoIterator<Item = T>>(mut left: Vec<T>, right: I) -> Vec<T> {
    left.extend(right);
    left
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

impl Term {
    pub fn free_vars(&self) -> Vec<VarIdent> {
        use Term::*;
        match self {
            Var(var) => vec![var.clone()],
            Appl(lhs, rhs) => extend(lhs.free_vars(), rhs.free_vars()),
            Binder { ty, body, .. } => {
                extend(
                    ty.free_vars(),
                    body.free_vars().iter().filter_map(|&index| {
                        if index > 0 {
                            Some(index - 1)
                        } else {
                            None
                        }
                    }),
                )
            }
            Prop => vec![],
            Type => vec![],
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

    pub fn infer_type_with_ctx(
        &self,
        variable_types: &mut Vec<Rc<Term>>,
    ) -> Result<Term, Vec<String>> {
        use Term::*;
        match self {
            Var(var) => Ok(variable_types[variable_types.len() - 1 - *var].eval()),
            Appl(lhs, rhs) => {
                let (lhs_type, rhs_type) = result_combine(
                    lhs.infer_type_with_ctx(variable_types),
                    rhs.infer_type_with_ctx(variable_types),
                )?;
                if let Binder {
                    binder: BinderKind::Pi,
                    ty,
                    body,
                } = lhs_type
                {
                    // Check the type of the argument matches the type of the
                    // parameter.
                    if *ty != rhs_type {
                        return Err(vec![format!(
                            "Argument type mismatch in {}: expected {}, found {}",
                            self, ty, rhs_type
                        )]);
                    }
                    Ok(Appl(
                        Rc::new(Binder {
                            binder: BinderKind::Lam,
                            ty: Rc::new(Type),
                            body,
                        }),
                        Rc::clone(rhs),
                    )
                    .eval())
                } else {
                    Err(vec![format!(
                        "Application of argument {} (type {}) to non-lambda {} (type {})",
                        rhs, rhs_type, lhs, lhs_type,
                    )])
                }
            }
            Binder {
                binder: BinderKind::Lam,
                ty,
                body,
            } => {
                // Get the type of the body.
                variable_types.push(Rc::clone(ty));
                let body_type = body.infer_type_with_ctx(variable_types)?;
                variable_types.pop();
                // The lambda's type is a pi type.
                let lam_type = Binder {
                    binder: BinderKind::Pi,
                    ty: Rc::clone(ty),
                    body: Rc::new(body_type),
                };
                // Make sure this binder type checks.
                lam_type.infer_type_with_ctx(variable_types)?;
                Ok(lam_type.eval())
            }
            Binder {
                binder: BinderKind::Pi,
                ty,
                body,
            } => {
                // Check that `ty`'s type could be infered.
                ty.infer_type_with_ctx(variable_types)?;
                // Get the type of the body.
                variable_types.push(Rc::clone(ty));
                let body_type = body.infer_type_with_ctx(variable_types)?;
                variable_types.pop();
                // The pi binder's type is the type of the body.
                Ok(body_type)
            }
            Prop => Ok(Type),
            Type => Ok(Type),
            // Type => Err(vec![format!("Type's type cannot be inferred")]),
        }
    }

    pub fn infer_type(&self) -> Result<Term, Vec<String>> {
        let mut variable_types = Vec::new();
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

impl Display for Term {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        TermPrint {
            term: self,
            variable_depth: 0,
        }
        .fmt(f)
    }
}
