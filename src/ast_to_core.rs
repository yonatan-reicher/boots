use crate::ast::{ArrowKind as AstArrowKind, Ast, Literal};
use crate::global::*;
use crate::name::Name;
use crate::term::{ArrowKind, Literal as CoreLiteral, PTerm, Term, Pattern};
use std::rc::Rc;

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

    fn ast_slice_to_core(&mut self, asts: &[Ast]) -> Result<Vec<PTerm>, ()> {
        asts.iter().map(|x| self.ast_to_core(x)).collect()
    }

    pub fn ast_to_pattern(&mut self, ast: &Ast) -> Result<Pattern, ()> {
        match ast {
            Ast::Var(name, _) => Pattern::Var(name.clone()).pipe(Ok),
            Ast::Tuple(vec) => vec
                .iter()
                .map(|x| self.ast_to_pattern(x))
                .collect::<Result<Vec<_>, _>>()
                .map(Pattern::UnTuple),
            Ast::Literal(Literal::String(s), _) => Pattern::String(s.clone()).pipe(Ok),
            // Emit errors for these cases.
            Ast::Appl(_, _, _) => todo!(),
            Ast::TypeAnnotation(_, _) => todo!(),
            Ast::Literal(_, _) => todo!(),
            Ast::Let(_, _, _) => todo!(),
            Ast::TupleType(_) => todo!(),
            Ast::Match(_, _) => todo!(),
            Ast::Arrow(_, _, _) => todo!(),
            Ast::Error => todo!(),
        }
    }

    pub fn ast_to_core(&mut self, ast: &Ast) -> Result<PTerm, ()> {
        match ast {
            Ast::Var(name, _) => Term::var(name.clone()).into(),
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
                        .fold(func, |func, arg| Term::appl(func, arg).into())
                } else {
                    return Err(());
                }
            }
            Ast::Arrow(AstArrowKind::Value, bind, right) => {
                let right = self.ast_to_core(right);
                let (param_name, typ) = match get_name_lam(bind) {
                    Ok((param_name, Some(typ))) => (param_name, typ),
                    _ => {
                        self.errors.push(Error::ExpectedNameAndTypeBeforeArrow);
                        return Err(());
                    }
                };
                let typ = self.ast_to_core(typ);

                Term::Arrow {
                    kind: ArrowKind::Value,
                    param_name,
                    ty: typ?,
                    body: right?,
                }.into()
            }
            Ast::Arrow(AstArrowKind::Type, bind, right) => {
                let right = self.ast_to_core(right);
                let (param_name, typ) = match get_name_pi(bind) {
                    Ok((param, typ)) => (param.unwrap_or("_".into()), typ),
                    Err(()) => {
                        self.errors.push(Error::ExpectedBindingsBeforeArrow);
                        return Err(());
                    }
                };
                let typ = self.ast_to_core(typ);

                Term::Arrow {
                    kind: ArrowKind::Type,
                    param_name,
                    ty: typ?,
                    body: right?,
                }.into()
            }
            Ast::TypeAnnotation(val, typ) => {
                let val = self.ast_to_core(val);
                let typ = self.ast_to_core(typ);
                Term::type_annotation(val?, typ?).into()
            }
            Ast::Literal(literal, _) => self.literal_to_core(literal).pipe(Term::Literal).into(),
            Ast::Let(bind, value, body) => {
                let (name, typ) = destruct(get_name_lam(bind));
                let typ = typ
                    .map(|typ| typ.map(|typ| self.ast_to_core(typ)))
                    .transpose()
                    .map(|x| x.and_then(|y| y))
                    .transpose();
                let value = self.ast_to_core(value);
                let body = self.ast_to_core(body);
                Term::let_(name?, typ?, value?, body?).into()
            }
            Ast::Tuple(terms) => Term::Tuple(self.ast_slice_to_core(terms)?).into(),
            Ast::TupleType(terms) => Term::TupleType(self.ast_slice_to_core(terms)?).into(),
            Ast::Error => todo!(),
            Ast::Match(input, cases) => {
                let input_term = self.ast_to_core(input)?;
                cases
                    .iter()
                    .map(|(pat, term)| {
                        let pat = self.ast_to_pattern(pat).map(Rc::new);
                        let term = self.ast_to_core(term);
                        Ok((pat?, term?))
                    })
                    .collect::<Result<Vec<_>, _>>()?
                    .pipe(|cases| Term::match_(input_term, cases))
                    .pipe(Term::into_pterm)
            },
        }
        .pipe(Ok)
    }

    fn literal_to_core(&mut self, literal: &Literal) -> CoreLiteral {
        match literal {
            Literal::String(s) => CoreLiteral::String(s.clone()),
            Literal::Int(_) => todo!(),
            Literal::Type => CoreLiteral::Type,
            Literal::Prop => CoreLiteral::Prop,
        }
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
