use crate::term::{PTerm, Term};
use crate::global::with_variable;
use crate::name::Name;
use std::collections::HashMap;

pub type Context = HashMap<Name, PTerm>;

/// Reduce the term to a cannonical form.
pub fn normalize(term: &PTerm) -> PTerm {
    eval(term, &mut Context::default())
}

pub fn eval(term: &PTerm, vars: &mut Context) -> PTerm {
    use Term::*;
    match term.as_ref() {
        Var(var) => vars.get(var).cloned().unwrap_or(term.clone()),
        Appl(lhs, rhs) => {
            let lhs = eval(lhs, vars);
            let rhs = eval(rhs, vars);

            if let Arrow {
                body, param_name, ..
            } = lhs.as_ref()
            {
                // Substitute the parameter inside the body and then eval again.
                return with_variable!(vars, (param_name, rhs), { eval(body, vars) });
            }

            if let Appl(func, arg1) = lhs.as_ref() {
                use crate::term::Literal as L;
                if let (Literal(L::StringAppend), Literal(L::String(s1)), Literal(L::String(s2))) =
                    (func.as_ref(), arg1.as_ref(), rhs.as_ref())
                {
                    return Literal(L::String(format!("{s1}{s2}").into())).into();
                }
            }

            Appl(lhs, rhs).into()
        }
        Arrow {
            kind: binder,
            param_name,
            ty,
            body,
        } => {
            let ty = eval(ty, vars);
            let body = eval(body, vars);

            // meu-reduction
            // (x => f x) = f
            if let Appl(func, arg) = body.as_ref() {
                if let Var(arg_var) = arg.as_ref() {
                    if arg_var == param_name {
                        return func.clone();
                    }
                }
            }

            Arrow {
                kind: *binder,
                param_name: param_name.clone(),
                ty,
                body,
            }
            .into()
        }
        Let(name, _, rhs, body) => {
            let rhs = eval(rhs, vars);

            with_variable!(vars, (name, rhs), {
                eval(body, vars)
            })
        }
        TypeAnnotation(term, _) => eval(term, vars),
        Literal(_) => term.clone(),
    }
}

/*
/// Reduce the term to a cannonical form.
pub fn eval(term: &Term) -> Option<PTerm> {
    use Term::*;
    match term {
        Appl(lhs, rhs) => {
            let lhs_new = lhs.eval();
            let rhs_new = rhs.eval();
            let lhs = lhs_new.as_ref().unwrap_or(lhs);
            let rhs = rhs_new.as_ref().unwrap_or(rhs);

            if let Arrow {
                body, param_name, ..
            } = lhs.as_ref()
            {
                // Substitute the parameter inside the body and then eval again.
                let ret = Self::substitute_or(body.clone(), param_name, rhs.clone());
                let ret = Self::eval_or(ret);
                return Some(ret);
            }

            if let Appl(func, arg1) = lhs.as_ref() {
                use self::Literal as L;
                if let (Literal(L::StringAppend), Literal(L::String(s1)), Literal(L::String(s2))) =
                    (func.as_ref(), arg1.as_ref(), rhs.as_ref())
                {
                    return Some(Literal(L::String(format!("{s1}{s2}").into())).into());
                }
            }

            if lhs_new.is_none() && rhs_new.is_none() {
                return None;
            }

            Some(Appl(lhs.clone(), rhs.clone()).into())
        }
        Arrow {
            kind: binder,
            param_name,
            ty,
            body,
        } => {
            let ty_new = ty.eval();
            let body_new = body.eval();
            let ty = ty_new.as_ref().unwrap_or(ty);
            let body = body_new.as_ref().unwrap_or(body);

            // meu-reduction
            // (x => f x) = f
            if let Appl(func, arg) = body.as_ref() {
                if let Var(arg_var) = arg.as_ref() {
                    if arg_var == param_name {
                        return func.clone().pipe(Some);
                    }
                }
            }

            if ty_new.is_none() && body_new.is_none() {
                return None;
            }

            Some(
                Arrow {
                    kind: *binder,
                    param_name: param_name.clone(),
                    ty: ty.clone(),
                    body: body.clone(),
                }
                .into(),
            )
        }
        Let(name, _, rhs, body) => Self::substitute_or(body.clone(), name, rhs.clone())
            .pipe(Self::eval_or)
            .pipe(Some),
        TypeAnnotation(term, _) => term.eval(),
        Literal(_) | Var(_) => None,
    }
}
*/
