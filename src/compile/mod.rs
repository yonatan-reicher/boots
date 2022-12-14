use crate::c;
use crate::core::{BinderKind, Term};
use crate::name::Name;
use std::rc::Rc;

// Stores information related to a scope of variables.
struct Vars(Vec<Var>);

struct Var(Name, c::TypeExpr);

impl Vars {
    pub fn new() -> Self {
        Self(Vec::new())
    }

    fn next_name(&self) -> Name {
        let string = format!("var{}", self.0.len() + 1);
        Name::Rc(Rc::from(string))
    }

    pub fn add(&mut self, var_type: c::TypeExpr) -> &Var {
        self.0.push(Var(self.next_name(), var_type));
        &self.0.last().unwrap()
    }

    pub fn get(&self, index_from_end: usize) -> &Var {
        &self.0[self.0.len() - index_from_end - 1]
    }

    pub fn remove_last(&mut self) {
        self.0.pop();
    }
}

struct Funcs(Vec<Func>);

struct Func {
    name: Name,
    params: Vec<Var>,
    ret: c::TypeExpr,
    c: Option<c::Function>,
}

impl Funcs {
    pub fn new() -> Self {
        Self(Vec::new())
    }

    fn next_name(&self) -> Name {
        let string = format!("func{}", self.0.len() + 1);
        Name::Rc(Rc::from(string))
    }

    fn param_name(index: usize) -> Name {
        let string = format!("arg{}", index + 1);
        Name::Rc(Rc::from(string))
    }

    pub fn add(&mut self, params: Vec<c::TypeExpr>, ret: c::TypeExpr) -> &mut Func {
        self.0.push(Func {
            name: self.next_name(),
            params: params
                .into_iter()
                .enumerate()
                .map(|(i, t)| Var(Self::param_name(i), t))
                .collect(),
            ret,
            c: None,
        });
        self.0.last_mut().unwrap()
    }
}

pub fn compile(term: &Term) -> c::Program {
    let term_type = term.infer_type().expect("Still no error handling...");

    let mut vars = Vars::new();
    let mut funcs = Funcs::new();

    let term_type_expr = compile_type_expr(&term_type, &mut vars, &mut funcs)
        .expect("Also not error handling for compilation...");

    let expr = compile_expr(term, &mut vars, &mut funcs);

    let body = vec![c::Statement::Declaration {
        type_expression: term_type_expr,
        name: "output".into(),
        initializer: expr,
    }];

    let main = c::Function {
        return_type: c::TypeExpr::Var("int".into()),
        name: "main".into(),
        parameters: vec![],
        body: Some(body),
    };

    let declarations = vec![c::TopLevelDeclaration::Function(main)];

    c::Program {
        includes: vec![
            c::Include::Arrow("stdlib.h".into()),
            c::Include::Quote("nessie.h".into()),
        ],
        declarations,
    }
}

fn compile_expr(term: &Term, vars: &mut Vars, funcs: &mut Funcs) -> c::Expr {
    match term {
        Term::Var(i) => c::Expr::Var(vars.get(*i).0.clone()),
        Term::Appl(t1, t2) => c::Expr::Call(
            Box::new(compile_expr(t1, vars, funcs)),
            vec![compile_expr(t2, vars, funcs)],
        ),
        Term::Binder {
            binder: _,
            ty,
            body,
        } => {
            // Get a type expression for the parameter's type.
            let param_ty = compile_type_expr(ty, vars, funcs).unwrap();

            // Infer the type of the body and get a type expression for it.
            let body_type = body.infer_type().unwrap();
            let body_type_expr = compile_type_expr(&body_type, vars, funcs).unwrap();

            // Compile the body to an expression.
            let param_name = vars.add(param_ty.clone()).0.clone();
            let body_expr = compile_expr(body, vars, funcs);
            vars.remove_last();

            // Define a function.
            let func = funcs.add(vec![param_ty.clone()], body_type_expr.clone());

            let function = c::Function {
                name: func.name.clone(),
                parameters: vec![c::Parameter {
                    name: param_name.clone(),
                    type_expression: param_ty,
                }],
                return_type: body_type_expr,
                body: Some(vec![c::Statement::Return(body_expr)]),
            };
            func.c = Some(function);

            // Return a variable referencing the function.
            c::Expr::Var(func.name.clone())
        }
        Term::Prop => c::Expr::Var("prop".into()),
        Term::Type => c::Expr::Var("type".into()),
    }
}

fn compile_type_expr(term: &Term, vars: &mut Vars, funcs: &mut Funcs) -> Result<c::TypeExpr, ()> {
    let term = term.eval();
    match term {
        Term::Prop => Ok(c::TypeExpr::Var("prop_t".into())),
        Term::Type => Ok(c::TypeExpr::Var("type_t".into())),
        /*Term::Binder {
            binder: BinderKind::Lam,
            ty: (),
            body: (),
        } => {}*/
        _ => Err(()),
    }
}
