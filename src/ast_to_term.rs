use crate::ast::{ArrowKind as AstArrowKind, Ast, Literal};
use crate::global::*;
use crate::name::Name;
use crate::term::{ArrowKind, DeBruijn, Literal as TermLiteral, PTerm, Pattern, Term};
use std::collections::HashMap;
use std::rc::Rc;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Error {
    ExpectedNameAndTypeBeforeArrow,
    ExpectedBindingsBeforeArrow,
    UndefinedVariable(Name),
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

#[derive(Debug, Clone, Default)]
struct VarDepths {
    name_depths: HashMap<Name, usize>,
    depth: usize,
}

impl VarDepths {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn insert(&mut self, name: Name) -> Option<usize> {
        let ret = self.name_depths.insert(name, self.depth);
        self.depth += 1;
        ret
    }

    pub fn get(&self, name: &Name) -> Option<DeBruijn> {
        let &index = self.name_depths.get(name)?;
        Some(DeBruijn::from_index(index, self.depth))
    }
}

impl Withable<Name> for &mut VarDepths {
    type Hid = (Name, Option<usize>);

    fn begin(self, x: Name) -> Self::Hid {
        (x.clone(), self.insert(x))
    }

    fn end(self, hid: Self::Hid) {
        self.depth -= 1;
        self.name_depths.end(hid)
    }
}

#[derive(Debug, Clone)]
struct State {
    errors: Vec<Error>,
    var_depths: VarDepths,
}

impl State {
    fn new<'a>(globals: impl IntoIterator<Item = &'a Name>) -> Self {
        let mut variable_depths = VarDepths::new();
        for name in globals {
            variable_depths.insert(name.clone());
        }
        Self {
            errors: Vec::new(),
            var_depths: variable_depths,
        }
    }

    fn ast_iter_to_core<'a>(&mut self, asts: impl IntoIterator<Item=&'a Ast>) -> Result<Vec<PTerm>, ()> {
        asts.into_iter().map(|x| self.ast_to_term(x)).collect()
    }

    pub fn ast_to_pattern(&mut self, ast: &Ast) -> Result<(Pattern, Vec<Name>), ()> {
        match ast {
            Ast::Literal(Literal::String(s), _) => Ok((Pattern::String(s.clone()), vec![])),
            Ast::Var(name, _) => Ok((Pattern::Var, vec![name.clone()])),
            Ast::Tuple(vec) => {
                let (patterns, name_vecs): (Vec<_>, Vec<_>) = vec
                    .iter()
                    .map(|x| self.ast_to_pattern(x))
                    .collect::<Result<Vec<_>, _>>()?
                    .into_iter()
                    .unzip();
                Ok((
                    Pattern::UnTuple(patterns),
                    name_vecs.into_iter().flatten().collect(),
                ))
            }
            // Emit errors for these cases.
            Ast::Appl(_, _, _) => todo!(),
            Ast::TypeAnnotation(_, _) => todo!(),
            Ast::Literal(_, _) => todo!(),
            Ast::Let(_, _, _) => todo!(),
            Ast::TupleType(_) => todo!(),
            Ast::Match(_, _) => todo!(),
            Ast::Arrow(_, _, _) => todo!(),
            Ast::Error => todo!(),
            Ast::UnionType(..) => todo!(),
        }
    }

    /*
    fn with_local<T>(&mut self, name: &Name, f: impl FnOnce(&mut Self) -> T) -> T {
        let old = self.var_depths.insert(name.clone());
        let ret = f(self);
        self.var_depths.set(name, old);
        ret
    }

    fn with_locals<'a, T>(
        &mut self,
        mut names: impl Iterator<Item = &'a Name>,
        f: impl FnOnce(&mut Self) -> T,
    ) -> T {
        match names.next() {
            None => f(self),
            Some(ref name) => self.with_local(name, |this| this.with_locals(names, f)),
        }
    }
    */

    pub fn ast_to_term(&mut self, ast: &Ast) -> Result<PTerm, ()> {
        match ast {
            Ast::Var(name, _) => {
                let Some(de_bruijn) = self.var_depths.get(name) else {
                    self.errors.push(Error::UndefinedVariable(name.clone()));
                    return Err(());
                };

                Ok(Term::Var(de_bruijn).into())
            }
            Ast::Appl(func, arg1, args_rest) => {
                // Visit the function and all the arguments.
                let func = self.ast_to_term(func);
                let args = [arg1.as_ref()]
                    .into_iter()
                    .chain(args_rest.iter())
                    .map(|arg| self.ast_to_term(arg))
                    .pipe(collect_results);

                let (Ok(func), Ok(args)) = (func, args) else {
                    todo!();
                };

                args.into_iter()
                    .fold(func, |func, arg| Term::Appl(func, arg).into())
                    .pipe(Ok)
            }
            Ast::Arrow(AstArrowKind::Value, bind, right) => {
                let (param_name, typ) = match get_name_lam(bind) {
                    Ok((param_name, Some(typ))) => (param_name, typ),
                    _ => {
                        self.errors.push(Error::ExpectedNameAndTypeBeforeArrow);
                        return Err(());
                    }
                };
                let typ = self.ast_to_term(typ);

                let right =
                    with_variable!(self.var_depths, param_name, { self.ast_to_term(right) });

                Term::Arrow {
                    kind: ArrowKind::Value,
                    ty: typ?,
                    body: right?,
                }
                .into_pterm()
                .pipe(Ok)
            }
            Ast::Arrow(AstArrowKind::Type, bind, right) => {
                let (param_name, typ) = match get_name_pi(bind) {
                    Ok((param, typ)) => (param.unwrap_or("_".into()), typ),
                    Err(()) => {
                        self.errors.push(Error::ExpectedBindingsBeforeArrow);
                        return Err(());
                    }
                };
                let typ = self.ast_to_term(typ);
                let right = with_variable!(self.var_depths, param_name, { self.ast_to_term(right) });

                Term::Arrow {
                    kind: ArrowKind::Type,
                    ty: typ?,
                    body: right?,
                }
                .into_pterm()
                .pipe(Ok)
            }
            Ast::TypeAnnotation(val, typ) => {
                let val = self.ast_to_term(val);
                let typ = self.ast_to_term(typ);
                Term::TypeAnnotation(val?, typ?).into_pterm().pipe(Ok)
            }
            Ast::Literal(literal, _) => self
                .literal_to_core(literal)
                .pipe(Term::Literal)
                .into_pterm()
                .pipe(Ok),
            Ast::Let(lhs, rhs, ret) => {
                let (name, typ) = destruct(get_name_lam(lhs));
                let typ = typ
                    .map(|typ| typ.map(|typ| self.ast_to_term(typ)))
                    .transpose()
                    .map(|x| x.and_then(|y| y))
                    .transpose();
                let rhs = self.ast_to_term(rhs);
                let ret = with_variables!(self.var_depths, name.ok().into_iter(), {
                    self.ast_to_term(ret)
                });
                Term::Let(typ?, rhs?, ret?).into_pterm().pipe(Ok)
            }
            Ast::Tuple(terms) => Term::Tuple(self.ast_iter_to_core(terms)?)
                .into_pterm()
                .pipe(Ok),
            Ast::TupleType(terms) => Term::TupleType(self.ast_iter_to_core(terms)?)
                .into_pterm()
                .pipe(Ok),
            Ast::UnionType(first, second, rest) => {
                let iter = [first.as_ref(), second.as_ref()].into_iter().chain(rest);
                let terms = self.ast_iter_to_core(iter)?;
                Ok(Term::UnionType(terms).into_pterm())
            }
            Ast::Error => todo!(),
            Ast::Match(input, cases) => {
                let input_term = self.ast_to_term(input)?;
                cases
                    .iter()
                    .map(|(pat, term)| {
                        let (pat, names) = self.ast_to_pattern(pat).pipe(destruct);
                        let term = with_variables!(self.var_depths, names.into_iter().flatten(), {
                            self.ast_to_term(term)
                        });
                        Ok((pat.map(Rc::new)?, term?))
                    })
                    .collect::<Result<Vec<_>, _>>()?
                    .pipe(|cases| Term::Match(input_term, cases))
                    .into_pterm()
                    .pipe(Ok)
            }
        }
    }

    fn literal_to_core(&mut self, literal: &Literal) -> TermLiteral {
        match literal {
            Literal::String(s) => TermLiteral::String(s.clone()),
            Literal::Int(_) => todo!(),
            Literal::Type => TermLiteral::Type,
            Literal::Prop => TermLiteral::Prop,
        }
    }
}

pub fn ast_to_term<'a>(
    ast: &Ast,
    globals: impl IntoIterator<Item = &'a Name>,
) -> Result<PTerm, Vec<Error>> {
    let mut state = State::new(globals);
    let ret = state.ast_to_term(ast);

    if let Ok(ret) = ret {
        Ok(ret)
    } else {
        Err(state.errors)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse::parse;
    use crate::term::{Pattern as P, Term as T};
    use indoc::indoc;

    #[test]
    fn it_works() {
        let globals = [&Name::from("x")];

        let ast = parse(indoc! {"
            match x with {
                (a, b) => a
            }
        "})
        .unwrap();

        let term = T::Match(
            T::Var(0.into()).into(),
            vec![(
                P::UnTuple(vec![P::Var, P::Var]).into(),
                T::Var(1.into()).into(),
            )],
        )
        .into_pterm();

        assert_eq!(ast_to_term(&ast, globals.into_iter()), Ok(term));
    }
}
