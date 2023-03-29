use crate::global::with_variable;
use crate::name::Name;
use crate::term::{PTerm, Term};
use std::collections::HashMap;
use std::rc::Rc;

pub type Context = HashMap<Name, PTerm>;

/// Reduce the term to a cannonical form.
pub fn normalize(term: &PTerm) -> PTerm {
    eval(term, &mut Context::default())
}

/// Check if the given name is a free variable in a bound variable.
pub fn name_is_bound(name: &Name, vars: &Context) -> bool {
    for value in vars.values() {
        if value.free_vars().contains(name) {
            return true;
        }
    }
    return false;
}

pub fn make_name_unique(name: &Name, vars: &Context) -> Name {
    let mut name = name.clone();
    while vars.contains_key(&name) || name_is_bound(&name, vars) {
        name = format!("{}_", name).into();
    }
    name
}

pub fn substitute(term: &PTerm, to_substitute: &Name, replacement: &PTerm) -> PTerm {
    let recurse = |x| substitute(x, to_substitute, replacement);

    match term.as_ref() {
        // Replace name.
        Term::Var(name) if name == to_substitute => replacement.clone(),
        // Things that don't change.
        Term::Var(_) | Term::Literal(_) => term.clone(),
        Term::Arrow { param_name, .. } if param_name == to_substitute => term.clone(),
        Term::Let(name, _, _, _) if name == to_substitute => term.clone(),
        // Recurse.
        Term::Arrow {
            kind,
            param_name,
            ty,
            body,
        } => Term::Arrow {
            kind: *kind,
            param_name: param_name.clone(),
            ty: recurse(ty),
            body: recurse(body),
        }
        .into(),
        Term::Let(name, annotation, rhs, body) => Term::Let(
            name.clone(),
            annotation.as_ref().map(|annotation| recurse(annotation)),
            recurse(rhs),
            recurse(body),
        )
        .into(),
        Term::Appl(left, right) => Term::Appl(recurse(left), recurse(right)).into(),
        Term::TypeAnnotation(left, right) => {
            Term::TypeAnnotation(recurse(left), recurse(right)).into()
        }
    }
}

pub fn eval(term: &PTerm, vars: &mut Context) -> PTerm {
    use Term::*;
    match term.as_ref() {
        // Bound name bug:
        // We don't want (y => x => y) x to reduce to (x => x), but to
        // something along the lines of (z => x)
        Arrow {
            kind,
            param_name,
            ty,
            body,
        } if name_is_bound(param_name, vars) => {
            let new_param_name = make_name_unique(param_name, vars);
            let new_body = substitute(body, param_name, &Term::Var(new_param_name.clone()).into());

            let new_term = Rc::new(Arrow {
                kind: *kind,
                param_name: new_param_name,
                ty: ty.clone(),
                body: new_body,
            });

            eval(&new_term, vars)
        }
        Let(name, annotation, rhs, body) if name_is_bound(name, vars) => {
            let new_name = make_name_unique(name, vars);
            let new_body = substitute(body, name, &Term::Var(new_name.clone()).into());

            let new_term = Let(new_name, annotation.clone(), rhs.clone(), new_body).into();
            eval(&new_term, vars)
        }
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

            with_variable!(vars, (name, rhs), { eval(body, vars) })
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
