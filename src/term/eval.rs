use crate::global::{with_variable, with_variables, ExtendPipe, Withable};
use crate::term::{DeBruijn, Literal, PTerm, Pattern, Term};

pub type Context = Vec<Option<PTerm>>;

/*
/// Reduce the term to a cannonical form.
pub fn normalize(term: &PTerm) -> PTerm {
    eval(term, &mut Context::default())
}
*/

pub fn children(term: &Term) -> Vec<PTerm> {
    match term {
        Term::Appl(lhs, rhs) | Term::TypeAnnotation(lhs, rhs) => vec![lhs.clone(), rhs.clone()],
        Term::Arrow { ty, body, .. } => vec![ty.clone(), body.clone()],
        Term::Var(_) | Term::Literal(_) => vec![],
        Term::Let(annot, rhs, ret) => vec![rhs.clone(), ret.clone()].extend_pipe(annot.clone()),
        Term::Tuple(elements) | Term::TupleType(elements) => elements.clone(),
        Term::Match(input, cases) => {
            vec![input.clone()].extend_pipe(cases.iter().map(|x| x.1.clone()))
        }
    }
}

pub fn children_mut(term: &mut Term) -> Vec<&mut PTerm> {
    match term {
        Term::Appl(lhs, rhs) | Term::TypeAnnotation(lhs, rhs) => vec![lhs, rhs],
        Term::Arrow { ty, body, .. } => vec![ty, body],
        Term::Var(_) | Term::Literal(_) => vec![],
        Term::Let(annot, rhs, ret) => vec![rhs, ret].extend_pipe(annot.as_mut()),
        Term::Tuple(elements) | Term::TupleType(elements) => elements.iter_mut().collect(),
        Term::Match(input, cases) => vec![input].extend_pipe(cases.iter_mut().map(|x| &mut x.1)),
    }
}

pub fn substitute(term: &PTerm, de_bruijn: DeBruijn, arg: &PTerm) -> PTerm {
    match term.as_ref() {
        // If the variable is the one we are looking for, switch it. If it is
        // a variable defined before, push it up the stack. If it is an inner
        // variable leave it be.
        Term::Var(var_de_bruijn) => {
            use std::cmp::Ordering::*;
            match var_de_bruijn.cmp(&de_bruijn) {
                Equal => arg.clone(),
                Less => term.clone(),
                Greater => Term::Var(var_de_bruijn.dec()).into(),
            }
        }
        // We are defining a variable, so the variable to substitute gets pushed
        // down.
        Term::Arrow { kind, ty, body } => Term::Arrow {
            kind: kind.clone(),
            ty: substitute(ty, de_bruijn, arg),
            body: substitute(body, de_bruijn.inc(), arg),
        }
        .into(),
        Term::Let(annot, rhs, ret) => Term::Let(
            annot
                .as_ref()
                .map(|annot| substitute(annot, de_bruijn, arg)),
            substitute(rhs, de_bruijn, arg),
            substitute(ret, de_bruijn.inc(), arg),
        )
        .into(),
        Term::Appl(left, right) => Term::Appl(
            substitute(left, de_bruijn, arg),
            substitute(right, de_bruijn, arg),
        )
        .into(),
        Term::TypeAnnotation(left, right) => Term::TypeAnnotation(
            substitute(left, de_bruijn, arg),
            substitute(right, de_bruijn, arg),
        )
        .into(),
        Term::Tuple(elements) => Term::Tuple(
            elements
                .iter()
                .map(|x| substitute(x, de_bruijn, arg))
                .collect(),
        )
        .into(),
        Term::TupleType(elements) => Term::TupleType(
            elements
                .iter()
                .map(|x| substitute(x, de_bruijn, arg))
                .collect(),
        )
        .into(),
        Term::Match(_, _) => todo!(),
        Term::Literal(_) => term.clone(),
    }
}

pub fn match_pattern(pattern: &Pattern, term: &PTerm) -> Option<Vec<PTerm>> {
    // Don't even try to match if the term is not reduced.
    if !term.is_reduced() {
        return None;
    }

    match (pattern, term.as_ref()) {
        (Pattern::Var, _) => Some(vec![term.clone()]),
        (Pattern::UnTuple(element_patterns), Term::Tuple(elements)) => {
            if element_patterns.len() != elements.len() {
                return None;
            }

            let mut result = vec![];
            for (pattern, element) in element_patterns.iter().zip(elements) {
                result.extend(match_pattern(pattern, element)?);
            }
            Some(result)
        }
        (Pattern::UnTuple(_), _) => None,
        (Pattern::String(s), Term::Literal(Literal::String(s2))) => {
            if s == s2 {
                Some(vec![])
            } else {
                None
            }
        }
        (Pattern::String(_), _) => None,
    }
}

pub fn eval(term: &PTerm, vars: &mut Context) -> PTerm {
    use Term::*;
    match term.as_ref() {
        Var(de_bruijn) => de_bruijn
            .index(vars)
            .cloned()
            .unwrap()
            .unwrap_or(term.clone()),
        Appl(lhs, rhs) => {
            let lhs = eval(lhs, vars);
            let rhs = eval(rhs, vars);

            // Function application.
            if let Arrow { body, .. } = lhs.as_ref() {
                return with_variable!(vars, Some(rhs), { eval(body, vars) });
            }

            // `string-append` function.
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
            ty,
            body,
        } => {
            let ty = eval(ty, vars);
            let body = with_variable!(vars, None, { eval(body, vars) });

            // meu-reduction
            // (x => f x) = f       (when x is not free in f)
            if let Appl(func, arg) = body.as_ref() {
                if let Var(de_bruijn) = arg.as_ref() {
                    if !func.free_vars().contains(&DeBruijn::TOP) && *de_bruijn == DeBruijn::TOP {
                        // Use substitute to get rid of the top-most variable.
                        // The third argument will be ignored because the variable is not free.
                        return substitute(func, DeBruijn::TOP, &ty);
                    }
                }
            }

            Arrow {
                kind: *binder,
                ty,
                body,
            }
            .into()
        }
        Let(_, rhs, body) => {
            let rhs = eval(rhs, vars);

            with_variable!(vars, Some(rhs), { eval(body, vars) })
        }
        TypeAnnotation(term, _) => eval(term, vars),
        Literal(_) => term.clone(),
        Tuple(elements) => Tuple(elements.iter().map(|e| eval(e, vars)).collect()).into(),
        TupleType(elements) => TupleType(elements.iter().map(|e| eval(e, vars)).collect()).into(),
        Match(input, cases) => {
            let input = eval(input, vars);
            cases
                .iter()
                .find_map(|(pattern, case)| {
                    // TODO: Reduce cases that are not matched.
                    match_pattern(pattern, &input).map(|bound_names| {
                        with_variables!(vars, bound_names.into_iter().map(Some), {
                            eval(case, vars)
                        })
                    })
                })
                .unwrap_or_else(|| Match(input, cases.clone()).into())
        }
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
