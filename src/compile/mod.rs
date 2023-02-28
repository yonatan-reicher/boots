use crate::c::{self, Expr::Var};
use crate::core::{BinderKind, PTerm, Term};
use crate::global::*;
use crate::name::Name;
use std::collections::HashMap;
use std::rc::Rc;

/*
 * In this module we will refer to N-vars as native variables or symbols, defined in the original program,
 * and we will refer to C-vars as c language symbols.
 */

#[derive(Debug, Default)]
struct NameGen(usize);

#[derive(Debug, Default, Clone)]
enum NameOptions {
    /// For variable names.
    #[default]
    Var,
    /// For struct types of closures.
    ClosureStruct,
    /// For call functions that call closures.
    Call,
    /// For make functions that make closures.
    Make,
    /// For implementation functions in closures.
    Impl,
    /// For variables pointing to a generic closure.
    ClosurePtrType,
}

impl NameGen {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn next(&mut self, options: NameOptions) -> Name {
        self.0 += 1;
        Name::Rc(Rc::from(format!("{}{}", options.prefix(), self.0 - 1)))
    }
}

impl NameOptions {
    pub fn prefix(&self) -> &'static str {
        use NameOptions::*;
        match self {
            Var => "var",
            ClosureStruct => "closure",
            Call => "call",
            Make => "make",
            Impl => "impl",
            ClosurePtrType => "closurePtr",
        }
    }
}

type CVars = HashMap<Name, (c::PTypeExpr, Name)>;

type NVars = HashMap<Name, PTerm>;

type Closures = Vec<Closure>;

#[derive(Debug)]
struct Closure {
    struct_name: Name,
    call_name: Name,
    make_name: Name,
    body: c::Function,
}

type FunctionCTypes = HashMap<(PTerm, PTerm), Name>;

#[derive(Debug, Default)]
struct Context {
    c_vars: CVars,
    n_vars: NVars,
    closures: Closures,
    function_c_types: FunctionCTypes,
    name_gen: NameGen,
}

impl Context {
    pub fn new() -> Self {
        Self::default()
    }
}

fn compile_closure_declarations(closure: &Closure) -> [c::TopLevelDeclaration; 4] {
    let struct_ptr_type: c::PTypeExpr = closure_type(closure).into();
    let struct_ptr_type_with_struct_var: c::PTypeExpr =
        closure_type_with_struct_var(closure).into();

    [
        // Struct.
        c::TopLevelDeclaration::Typedef(
            compile_closure_struct(closure, struct_ptr_type_with_struct_var),
            closure.struct_name.clone(),
        ),
        // Impl.
        c::TopLevelDeclaration::Function(compile_closure_impl_function(closure)),
        // Call.
        c::TopLevelDeclaration::Function(compile_closure_call_function(
            closure,
            struct_ptr_type.clone(),
        )),
        // Make.
        c::TopLevelDeclaration::Function(compile_closure_make_function(closure, struct_ptr_type)),
    ]
}

// TODO: Rename
fn closure_type(closure: &Closure) -> c::TypeExpr {
    c::TypeExpr::Ptr(c::TypeExpr::Var(closure.struct_name.clone()).into())
}

// TODO: Rename
fn closure_type_with_struct_var(closure: &Closure) -> c::TypeExpr {
    c::TypeExpr::Ptr(c::TypeExpr::StructVar(closure.struct_name.clone()).into())
}

fn compile_closure_struct(closure: &Closure, struct_ptr_type: c::PTypeExpr) -> c::TypeExpr {
    c::TypeExpr::Struct({
        // Create a vector of fields to put in the struct type.
        // Reminder: The struct has the call function ptr as the first fields and all the captured values as the rest.

        let closure_parameter = &closure.body.parameters[0];
        let captured_values_parameters = &closure.body.parameters[1..];

        // The type of the call field.
        let call_type: c::PTypeExpr = c::TypeExpr::FunctionPtr(
            closure.body.return_type.clone(),
            vec![struct_ptr_type.clone(), closure_parameter.0.clone()],
        )
        .into();

        let mut fields = vec![(call_type, "call".into())];
        fields.extend(captured_values_parameters.iter().cloned());
        fields
    })
}

fn compile_closure_impl_function(closure: &Closure) -> c::Function {
    closure.body.clone()
}

fn compile_closure_call_function(closure: &Closure, struct_ptr_type: c::PTypeExpr) -> c::Function {
    // Make the body of the call function.
    // We want to take the implementation function of the closure, and apply it
    // the correct parameters, as they are stored in closure.body.parameters
    let this_var = Var("self".into());
    let impl_function = Var(closure.body.name.clone());

    let call_the_impl = c::Expr::Call(
        impl_function.into(),
        closure
            .body
            .parameters
            .iter()
            .enumerate()
            .map(|(i, (_, name))| {
                if i == 0 {
                    Var(name.clone())
                } else {
                    c::Expr::Dot(this_var.clone().into(), name.clone())
                }
            })
            .collect(),
    );

    let body = vec![c::Statement::Return(call_the_impl)];

    c::Function {
        return_type: closure.body.return_type.clone(),
        name: closure.call_name.clone(),
        parameters: vec![
            (struct_ptr_type.clone(), "self".into()),
            closure.body.parameters[0].clone(),
        ],
        body: Some(body), // TODO: Give a body.
    }
}

fn compile_closure_make_function(closure: &Closure, struct_ptr_type: c::PTypeExpr) -> c::Function {
    let ret_name: Name = "ret".into();
    let ret_var = Var(ret_name.clone());

    // Make some statements to put in the body.
    // closureX* ret = (closureX*)malloc(sizeof(closureX));
    let declare_ret = c::Statement::Declaration {
        type_expression: struct_ptr_type.clone(),
        name: ret_name.clone(),
        initializer: c::Expr::Cast(
            struct_ptr_type.clone(),
            c::Expr::Call(
                Var("malloc".into()).into(),
                vec![c::Expr::SizeOf(
                    c::TypeExpr::Var(closure.struct_name.clone()).into(),
                )],
            )
            .into(),
        ),
    };
    // ret.call = callX;
    let assign_call = c::Statement::Assign(
        c::Expr::Dot(ret_var.clone().into(), "call".into()),
        Var(closure.call_name.clone()).into(),
    );
    // ret.fieldX = parameterX;
    let assign_fields = closure.body.parameters[1..].iter().map(|(_, name)| {
        c::Statement::Assign(
            c::Expr::Dot(ret_var.clone().into(), name.clone()).into(),
            Var(name.clone()).into(),
        )
    });

    // Combine the statemets into a block.
    let body: c::Block = [declare_ret, assign_call]
        .into_iter()
        .chain(assign_fields)
        .chain([c::Statement::Return(ret_var.clone())])
        .collect();

    c::Function {
        return_type: struct_ptr_type.clone(),
        name: closure.make_name.clone(),
        parameters: closure.body.parameters[1..].iter().cloned().collect(),
        body: Some(body),
    }
}

pub fn compile(term: PTerm) -> c::Program {
    let term_type = term.infer_type().expect("Still no error handling...");

    let mut context = Context::default();

    let term_type_expr = compile_type_expr(&term_type, &mut context)
        .expect("Also not error handling for compilation...");

    let expr = compile_expr(term, &mut context);

    let body = vec![c::Statement::Declaration {
        type_expression: term_type_expr.into(),
        name: "output".into(),
        initializer: expr,
    }];

    let main = c::Function {
        return_type: c::TypeExpr::Var("int".into()).into(),
        name: "main".into(),
        parameters: vec![],
        body: Some(body),
    };

    let mut declarations = Vec::<c::TopLevelDeclaration>::new();

    for closure in &context.closures {
        declarations.extend(compile_closure_declarations(closure));
    }

    // TODO: Also declare context.function_c_types.
    for ((left, right), name) in &context.function_c_types {
        // declaration.extend(c::TopLevelDeclaration::Typedef(todo!(), todo!()))
    }

    // Add the main function.
    declarations.push(c::TopLevelDeclaration::Function(main));

    println!("{:?}", context);

    c::Program {
        includes: vec![
            c::Include::Arrow("stdlib.h".into()),
            c::Include::Quote("nessie.h".into()),
        ],
        declarations,
    }
}

fn compile_expr(term: PTerm, con: &mut Context) -> c::Expr {
    let term = Term::eval_or(term);
    let term_type = term.infer_type_with_ctx(&mut con.n_vars).unwrap();
    match term.as_ref() {
        Term::Var(name) => Var(con.c_vars[name].1.clone()),
        Term::Appl(t1, t2) =>
        // TODO: This is incorrect!
        // Should first save the closure pointer (lhs) in a variable,
        // then pass it to it's .call field along with the argument (rhs!).
        {
            c::Expr::Call(
                Box::new(compile_expr(t1.clone(), con)),
                vec![compile_expr(t2.clone(), con)],
            )
        }
        Term::Binder {
            binder: BinderKind::Lam,
            param_name,
            ty,
            body,
        } => {
            // Get a type expression for the parameter's type.
            let param_c_ty: c::PTypeExpr = compile_type_expr(ty, con).unwrap().into();

            // Infer the type of the body and get a type expression for it.
            let body_type = match term_type.as_ref() {
                Term::Binder { body, .. } => body,
                _ => unreachable!(),
            };
            let body_c_type: c::PTypeExpr = compile_type_expr(&body_type, con).unwrap().into();

            // Compile the body to an expression.
            let param_c_name = con.name_gen.next(NameOptions::Var);
            let body_c_expr = with_variable!(con.n_vars, (param_name, ty.clone()), {
                with_variable!(
                    con.c_vars,
                    (param_name, (param_c_ty.clone(), param_c_name.clone())),
                    { compile_expr(body.clone(), con) }
                )
            });

            // Get the captured variables.
            let parameters: Vec<_> = [(param_c_ty, param_c_name)]
                .into_iter()
                .chain(
                    term.free_vars()
                        .iter()
                        .map(|var| (con.c_vars.get(var).unwrap().clone())),
                )
                .collect();

            let captured_variable_calls: Vec<_> = parameters
                .iter()
                .skip(1) // Remove the closure parameter
                .map(|p| Var(p.1.clone()))
                .collect();

            // Define a closure.
            let closure = Closure {
                struct_name: con.name_gen.next(NameOptions::ClosureStruct),
                call_name: con.name_gen.next(NameOptions::Call),
                make_name: con.name_gen.next(NameOptions::Make),
                body: c::Function {
                    name: con.name_gen.next(NameOptions::Impl),
                    return_type: body_c_type.clone(),
                    parameters,
                    body: Some(vec![c::Statement::Return(body_c_expr)]),
                },
            };
            let closure_make_name = closure.make_name.clone();
            con.closures.push(closure);

            // Return a variable referencing the function.
            c::Expr::Call(Var(closure_make_name).into(), captured_variable_calls)
        }
        Term::Prop => Var("prop".into()),
        Term::Type => Var("type".into()),
        _ => todo!(),
    }
}

fn compile_type_expr(term: &Term, con: &mut Context) -> Result<c::TypeExpr, ()> {
    let term = Term::eval_or(term.clone().into());
    match term.as_ref() {
        Term::Prop => Ok(c::TypeExpr::Var("prop_t".into())),
        Term::Type => Ok(c::TypeExpr::Var("type_t".into())),
        Term::Binder {
            binder: BinderKind::Pi,
            param_name,
            ty,
            body,
        } => {
            let name = con
                .function_c_types
                .get(&(ty.clone(), body.clone()))
                .cloned()
                .unwrap_or_else(|| {
                    let name = con.name_gen.next(NameOptions::ClosurePtrType);
                    con.function_c_types
                        .insert((ty.clone(), body.clone()), name.clone());
                    name
                });
            Ok(c::TypeExpr::Var(name))
        }
        _ => Err(()),
    }
}
/*
            let body_type = body.infer_type_with_ctx(var_types).unwrap();
            let free_vars = body.free_vars();
            let ret_c_type = compile_type_expr() body.
            funcs.add(free_vars, )
*/
