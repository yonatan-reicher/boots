use std::rc::Rc;
use crate::c;
use crate::core::{Term, VarIdent};

type Name = Rc<str>;

struct Vars(Vec<Var>);

struct Var(Name, c::TypeExpr);

impl Vars {
    pub fn new() -> Self {
        Self(Vec::new())
    }

    fn next_name(&self) -> Name {
        let string = format!("var{}", self.symbols.len() + 1);
        Rc::from(string)
    }

    pub fn add(&mut self, var_type: c::TypeExpr) -> &Var {
        self.symbols.push((self.next_name(), var_type));
        &self.symbols.last().unwrap()
    }

    pub fn get(&self, index_from_end: usize) -> &Var {
        &self.symbols[self.symbols.len() - index_from_end - 1]
    }

    pub fn remove_last(&mut self) {
        self.symbols.pop();
    }
}

struct Funcs(Vec<Func>);

struct Func {
    name: Name,
    args: Vec<Var>,
    ret: c::TypeExpr,
}

impl Symbol for Var {
    fn prefix() -> &'static str {
        "var"
    }
}

impl Symbol for Func {
    fn prefix() -> &'static str {
        "func"
    }
}

const PROP_EXPR: c::Expr = c::Expr::Var("prop".into());
const TYPE_EXPR: c::Expr = c::Expr::Var("type".into());

pub fn compile(term: &Term) -> c::Program {
    todo!();
}

fn compile_expr(term: &Term, vars: &mut Symbols<Var>, funcs: &mut Symbols<Func>) -> c::Expr {
    match term {
        Term::Var(i) => c::Expr::Var(vars.get(*i).0.as_ref().into()),
        Term::Appl(t1, t2) => c::Expr::Call(
            Box::new(compile_expr(t1, vars, funcs)),
            vec![compile_expr(t2, vars, funcs)],
        ),
        Term::Binder { binder, ty, body } => {
            // Get a type expression for the parameter's type.
            let param_ty = compile_type_expr(ty, vars, funcs).unwrap();

            // Infer the type of the body and get a type expression for it.
            let body_type = body.infer_type().unwrap();
            let body_type_expr = compile_type_expr(&body_type, vars, funcs);

            // Compile the body to an expression.
            vars.add(Var { ty: param_ty });
            let param_name = vars.last();
            let body_expr = compile_expr(body, vars, funcs);
            vars.remove_last();

            // Define a function.
            funcs.add(Func {
                args: vec![Var { ty: param_ty }],
                ret: body_type_expr.unwrap(),
            });
            let func_name = funcs.last();

            let function = c::Function {
                name: func_name.into(),
                parameters: vec![ c::Parameter {
                    name: param_name.into(),
                    type_expression: param_ty,
                } ],
                return_type: body_type_expr,
                body: body_expr,
            };
            // Return a variable referencing the function.
            c::Expr::Var(func_name)
        }
        Term::Prop => PROP_EXPR.clone(),
        Term::Type => TYPE_EXPR.clone(),
    }
}

fn compile_type_expr(term: &Term, vars: &mut Symbols<Var>, funcs: &mut Symbols<Func>) -> Result<c::TypeExpr, ()> {
    let term = term.eval();
    match term {
        Term::Prop => Ok(c::TypeExpr::Prop),
        Term::Type => Ok(c::TypeExpr::Type),
        _ => Err(())
    }
}
