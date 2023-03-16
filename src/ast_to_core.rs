use crate::ast::{ArrowType, Ast, Literal};
use crate::core::{BinderKind, PTerm, Term};
use crate::global::*;
use crate::name::Name;

#[derive(Clone, Debug)]
pub enum Error {
    ExpectedNameAndTypeBeforeArrow,
    ExpectedBindingsBeforeArrow,
}

fn get_name_lam(ast: &Ast) -> Result<(Name, Option<&Ast>), ()> {
    match ast {
        Ast::TypeAnnotation(val, typ) => match val.as_ref() {
            Ast::Var(name, _) => Ok((name.clone(), Some(typ))),
            _ => Err(()),
        },
        Ast::Var(name, _) => Ok((name.clone(), None)),
        _ => Err(()),
    }
}

fn get_name_pi(ast: &Ast) -> Result<(Option<Name>, &Ast), ()> {
    match ast {
        Ast::TypeAnnotation(val, typ) => match val.as_ref() {
            Ast::Var(name, _) => Ok((name.clone().pipe(Some), typ)),
            _ => Err(()),
        },
        ast => Ok((None, ast)),
    }
}

struct State {
    errors: Vec<Error>,
}

impl State {
    fn new() -> Self {
        Self { errors: vec![] }
    }

    pub fn ast_to_core(&mut self, ast: &Ast) -> Result<PTerm, ()> {
        match ast {
            Ast::Var(name, _) => Term::Var(name.clone()),
            Ast::Appl(func, arg1, args_rest) => {
                // Visit the function and all the arguments.
                let func = self.ast_to_core(func);
                let args = [arg1.as_ref()]
                    .into_iter()
                    .chain(args_rest.iter())
                    .map(|arg| self.ast_to_core(arg))
                    .pipe(collect_results);

                if let (Ok(func), Ok(args)) = (func, args) {
                    args.into_iter()
                        .fold(func, |func, arg| Term::Appl(func, arg).into())
                        .as_ref()
                        .clone()
                } else {
                    return Err(());
                }
            }
            Ast::Arrow(ArrowType::Value, bind, right) => {
                let right = self.ast_to_core(right);
                let (param_name, typ) = match get_name_lam(bind) {
                    Ok((param_name, Some(typ))) => (param_name, typ),
                    _ => {
                        self.errors.push(Error::ExpectedNameAndTypeBeforeArrow);
                        return Err(());
                    }
                };
                let typ = self.ast_to_core(typ);

                Term::Binder {
                    binder: BinderKind::Value,
                    param_name,
                    ty: typ?,
                    body: right?,
                }
            }
            Ast::Arrow(ArrowType::Type, bind, right) => {
                let right = self.ast_to_core(right);
                let (param_name, typ) = match get_name_pi(bind) {
                    Ok((param, typ)) => (param.unwrap_or("_".into()), typ),
                    Err(()) => {
                        self.errors.push(Error::ExpectedBindingsBeforeArrow);
                        return Err(());
                    }
                };
                let typ = self.ast_to_core(typ);

                Term::Binder {
                    binder: BinderKind::Type,
                    param_name,
                    ty: typ?,
                    body: right?,
                }
            }
            Ast::TypeAnnotation(val, typ) => {
                let val = self.ast_to_core(val);
                let typ = self.ast_to_core(typ);
                Term::TypeAnnotation(val?, typ?)
            }
            Ast::Literal(Literal::String(s), _) => Term::StringLiteral(s.clone()),
            Ast::Literal(Literal::Int(_), _) => todo!(),
            Ast::Literal(Literal::Type, _) => Term::Type,
            Ast::Literal(Literal::Prop, _) => Term::Prop,
            Ast::Let(bind, value, body) => {
                let (name, typ) = destruct(get_name_lam(bind));
                let typ = typ
                    .map(|typ| typ.map(|typ| self.ast_to_core(typ)))
                    .transpose()
                    .map(|x| x.and_then(|y| y))
                    .transpose();
                let value = self.ast_to_core(value);
                let body = self.ast_to_core(body);
                Term::Let(
                    name?,
                    typ?,
                    value?,
                    body?,
                )
            }
            Ast::Error => todo!(),
        }
        .pipe(PTerm::from)
        .pipe(Ok)
    }
}

pub fn ast_to_core(ast: &Ast) -> Result<PTerm, Vec<Error>> {
    let mut state = State::new();
    let ret = state.ast_to_core(ast);

    if let Ok(ret) = ret {
        Ok(ret)
    } else {
        Err(state.errors)
    }
}
