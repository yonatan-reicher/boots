use crate::global::{with_variable, with_variables, Pipe, Withable};
use crate::term::{substitute, ArrowKind, Literal, PTerm, Pattern, Term};

use super::DeBruijn;

pub type Context = Vec<PTerm>;

#[derive(Debug)]
pub enum Error {
    VariableNotFound,
    NotApplicable,
    ArgumentTypeDoesntMatch,
    WrongTypeAnnotation,
    CantUnTupleNonTuple,
    UnTuplePatternCountMismatch,
    EmptyMatch,
    MatchArmsTypeMismatch,
    StringPatternWrongType(PTerm),
}

pub fn infer(term: &PTerm, context: &mut Context) -> Result<PTerm, Vec<Error>> {
    let mut errors = Vec::new();
    let mut state = State {
        errors: &mut errors,
        context,
    };

    let res = state.infer(term);

    if errors.is_empty() {
        res.map_err(|_| errors)
    } else {
        Err(errors)
    }
}

struct State<'a> {
    errors: &'a mut Vec<Error>,
    context: &'a mut Context,
}

impl<'a> State<'a> {
    pub fn infer_pattern(&mut self, pat: &Pattern, input_type: &PTerm) -> Result<Vec<PTerm>, ()> {
        match pat {
            Pattern::Var => Ok(vec![input_type.clone()]),
            Pattern::UnTuple(pats) => {
                let element_types = match input_type.as_ref() {
                    Term::TupleType(element_types) => element_types,
                    _ => {
                        self.errors.push(Error::CantUnTupleNonTuple);
                        return Err(());
                    }
                };

                if element_types.len() != pats.len() {
                    self.errors.push(Error::UnTuplePatternCountMismatch);
                    return Err(());
                }

                element_types
                    .iter()
                    .zip(pats)
                    .map(|(element_type, pat)| self.infer_pattern(pat, element_type))
                    .collect::<Result<Vec<_>, _>>()?
                    .into_iter()
                    .flatten()
                    .collect::<Vec<_>>()
                    .pipe(Ok)
            }
            Pattern::String(_) => {
                if !matches!(input_type.as_ref(), Term::Literal(Literal::Str)) {
                    self.errors
                        .push(Error::StringPatternWrongType(input_type.clone()));
                    return Err(());
                }

                Ok(vec![])
            }
        }
    }

    pub fn infer(&mut self, term: &PTerm) -> Result<PTerm, ()> {
        match term.as_ref() {
            Term::Var(de_bruijn) => de_bruijn
                .index(&self.context)
                .cloned()
                .ok_or_else(|| self.errors.push(Error::VariableNotFound)),
            Term::Appl(lhs, rhs) => {
                let lhs_type = self.infer(lhs);
                let rhs_type = self.infer(rhs);
                let lhs_type = lhs_type?;
                let rhs_type = rhs_type?;

                // Destruct the left hand side.
                let Term::Arrow { kind: ArrowKind::Type, ty: param_ty, body } = lhs_type.as_ref() else {
                    self.errors.push(Error::NotApplicable);
                    return Err(());
                };

                if param_ty != &rhs_type {
                    self.errors.push(Error::ArgumentTypeDoesntMatch);
                }

                Ok(substitute(body, DeBruijn::TOP, rhs))
            }
            Term::Arrow {
                kind: ArrowKind::Value,
                ty,
                body,
            } => {
                // Get the type of the body.
                let body_type = with_variable!(self.context, ty.clone(), { self.infer(body) })?;

                // The lambda's type is a pi type.
                let lam_type = Term::Arrow {
                    kind: ArrowKind::Type,
                    ty: ty.clone(),
                    body: body_type,
                }
                .into();
                // Make sure this binder type checks.
                self.infer(&lam_type)?;
                Ok(lam_type)
            }
            Term::Arrow {
                kind: ArrowKind::Type,
                ty,
                body,
            } => {
                // Check that `ty`'s type could be infered.
                self.infer(ty)?;
                // Get the type of the body.
                let body_type = with_variable!(self.context, ty.clone(), { self.infer(body) })?;
                // The pi binder's type is the type of the body.
                Ok(body_type)
            }
            Term::TypeAnnotation(term, typ) => {
                let term_type = self.infer(term)?;
                //
                // Check that the type of term matches the type annotation.
                if term_type != *typ {
                    self.errors.push(Error::WrongTypeAnnotation);
                }

                Ok(term_type)
            }
            Term::Literal(l) => Self::literal_type(l).pipe(Ok),
            Term::Let(annotation, rhs, body) => {
                let rhs_type = self.infer(rhs);

                // Check the type annotation.
                if let Some(annotation) = annotation {
                    if rhs_type.as_ref() != Ok(annotation) {
                        self.errors.push(Error::WrongTypeAnnotation);
                    }
                }

                let rhs_type = annotation.clone().map(Ok).unwrap_or(rhs_type)?;
                with_variable!(self.context, rhs_type, { self.infer(body) })
            }
            Term::Tuple(elements) => {
                let element_types = elements
                    .iter()
                    .map(|e| self.infer(e))
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(Term::TupleType(element_types).into())
            }
            Term::TupleType(_) => Ok(Literal::Type.pipe(Term::Literal).into()),
            Term::Match(input, cases) => {
                let input_type = self.infer(input)?;
                let case_types: Vec<PTerm> = cases
                    .iter()
                    .map(|(pattern, case)| {
                        let pattern_variable_types = self.infer_pattern(pattern, &input_type)?;
                        let case_type = with_variables!(self.context, pattern_variable_types, {
                            self.infer(case)?
                        });
                        Ok(case_type)
                    })
                    .collect::<Result<Vec<PTerm>, _>>()?;

                if case_types.is_empty() {
                    self.errors.push(Error::EmptyMatch);
                    return Err(());
                }

                if case_types[1..].iter().any(|t| t != &case_types[0]) {
                    self.errors.push(Error::MatchArmsTypeMismatch);
                }

                Ok(case_types[0].clone())
            }
        }
    }

    fn literal_type(literal: &Literal) -> PTerm {
        match literal {
            Literal::Prop | Literal::Type | Literal::Str => {
                Literal::Type.pipe(Term::Literal).into()
            }
            Literal::String(_) => Literal::Str.pipe(Term::Literal).into(),
            Literal::StringAppend => Term::Arrow {
                kind: ArrowKind::Type,
                ty: Literal::Str.into(),
                body: Term::Arrow {
                    kind: ArrowKind::Type,
                    ty: Literal::Str.into(),
                    body: Literal::Str.into(),
                }
                .into(),
            }
            .into(),
        }
    }
}
