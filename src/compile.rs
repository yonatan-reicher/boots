use crate::c;
use crate::c::combine_traits::*;
use crate::global::*;
use crate::name::Name;
use crate::term::{infer, normalize, ArrowKind, Literal, PTerm, Term, TypeContext};
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
    /// For closure drop function names (functions that free the closure).
    Drop,
    /// For variables pointing to a generic closure.
    ClosureHeadType,
    TupleType,
}

impl NameGen {
    #[allow(dead_code)]
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
            Drop => "drop",
            ClosureHeadType => "closureHead",
            TupleType => "tuple",
        }
    }
}

/// A mapping from a C-Var name to a C-Var type and it's N-Var name.
type CVars = HashMap<Name, (c::PTypeExpr, Name)>;

type Closures = Vec<Closure>;

#[derive(Debug)]
struct Closure {
    struct_name: Name,
    call_name: Name,
    make_name: Name,
    drop_name: Name,
    body: c::Function,
    captured_variables_types: Vec<(Name, PTerm, c::PTypeExpr)>,
}

type FunctionCTypes = HashMap<(PTerm, PTerm), Name>;

type TupleCTypes = HashMap<PTerm, Tuple>;

#[derive(Debug, Clone)]
struct Tuple {
    c_type_name: Name,
    make_name: Name,
    types: Vec<c::PTypeExpr>,
}

#[derive(Debug, Default)]
struct Context {
    c_vars: CVars,
    n_vars: TypeContext,
    closures: Closures,
    function_c_types: FunctionCTypes,
    tuple_c_types: TupleCTypes,
    name_gen: NameGen,
}

impl Context {
    #[allow(dead_code)]
    pub fn new() -> Self {
        Self::default()
    }
}

/// Returns declarations that code anything the closure needs.
///
/// Returns a tuple with names to forward declare (currently only the struct
/// name) and the declarations.
fn compile_closure_declarations(
    closure: &Closure,
    name_gen: &mut NameGen,
) -> (Name, [c::TopLevelDeclaration; 5]) {
    use c::TopLevelDeclaration::Function;

    let struct_ptr_type: c::PTypeExpr = closure.struct_name.clone().type_var().ptr().into();

    (
        closure.struct_name.clone(), // Currently, only forward declare the struct name.
        [
            // Struct.
            closure_struct(closure, struct_ptr_type.clone()),
            // Function.
            Function(closure_impl_function(closure)),
            Function(closure_call_function(closure, struct_ptr_type.clone())),
            Function(closure_drop_function(
                closure,
                struct_ptr_type.clone(),
                name_gen,
            )),
            Function(closure_make_function(closure, struct_ptr_type)),
        ],
    )
}

// TODO: Get rid of `closure_ptr_type` parameter, and this function as a whole.
fn closure_call_type(
    closure_ptr_type: c::PTypeExpr,
    ret_type: c::PTypeExpr,
    arg_type: c::PTypeExpr,
) -> c::TypeExpr {
    ret_type.function_ptr([closure_ptr_type, arg_type])
}

fn closure_drop_type() -> c::TypeExpr {
    "void"
        .type_var()
        .function_ptr(["void".type_var().ptr().into()])
}

fn closure_struct(closure: &Closure, struct_ptr_type: c::PTypeExpr) -> c::TopLevelDeclaration {
    // Create a vector of fields to put in the struct type.
    // Reminder: The struct has the reference counter and call function ptr
    // as the first fields and all the captured values as the rest.

    let closure_parameter = &closure.body.parameters[0];
    let captured_values_parameters = &closure.body.parameters[1..];

    // The type of the call field.
    let call_type: c::PTypeExpr = closure_call_type(
        struct_ptr_type,
        closure.body.return_type.clone(),
        closure_parameter.0.clone(),
    )
    .into();

    let mut fields = vec![
        ("int".type_var().into(), "rc".into()),
        (call_type, "call".into()),
        (closure_drop_type().into(), "drop".into()),
    ];
    fields.extend(captured_values_parameters.iter().cloned());
    c::TopLevelDeclaration::Struct(closure.struct_name.clone(), fields)
}

fn closure_impl_function(closure: &Closure) -> c::Function {
    closure.body.clone()
}

fn closure_call_function(closure: &Closure, struct_ptr_type: c::PTypeExpr) -> c::Function {
    // Make the body of the call function.
    // We want to take the implementation function of the closure, and apply it
    // the correct parameters, as they are stored in closure.body.parameters
    let this_var = "self".var();
    let impl_function = closure.body.name.clone().var();

    let call_the_impl = c::Expr::Call(
        impl_function.into(),
        closure
            .body
            .parameters
            .iter()
            .enumerate()
            .map(|(i, (_, name))| {
                if i == 0 {
                    name.clone().var()
                } else {
                    c::Expr::Arrow(this_var.clone().into(), name.clone())
                }
            })
            .collect(),
    );

    let body = vec![c::Statement::Return(call_the_impl)];

    c::Function {
        return_type: closure.body.return_type.clone(),
        name: closure.call_name.clone(),
        parameters: vec![
            (struct_ptr_type, "self".into()),
            closure.body.parameters[0].clone(),
        ],
        body: Some(body),
    }
}

fn closure_make_function(closure: &Closure, struct_ptr_type: c::PTypeExpr) -> c::Function {
    let ret_name: Name = "ret".into();
    let ret_var = ret_name.clone().var();

    // Make some statements to put in the body.
    // closureX* ret = (closureX*)malloc(sizeof(closureX));
    let declare_ret = "malloc"
        .var()
        .call([closure.struct_name.clone().type_var().sizeof()])
        .cast(struct_ptr_type.clone())
        .variable(ret_name, struct_ptr_type.clone());
    // ret.rc = 0;
    let assign_rc = ret_var.clone().arrow("rc").assign(0.literal());
    // ret.call = callX;
    let assign_call = ret_var
        .clone()
        .arrow("call")
        .assign(closure.call_name.clone().var());
    // ret.drop = dropX;
    let assign_drop = ret_var
        .clone()
        .arrow("drop")
        .assign(closure.drop_name.clone().var());
    // ret.fieldX = parameterX;
    let assign_fields = closure.body.parameters[1..].iter().map(|(_, name)| {
        ret_var
            .clone()
            .arrow(name.clone())
            .assign(name.clone().var())
    });

    // Combine the statemets into a block.
    let body: c::Block = [declare_ret, assign_rc, assign_call, assign_drop]
        .into_iter()
        .chain(assign_fields)
        .chain([ret_var.clone().ret()])
        .collect();

    c::Function {
        return_type: struct_ptr_type,
        name: closure.make_name.clone(),
        parameters: closure.body.parameters[1..].to_vec(),
        body: Some(body),
    }
}

fn closure_drop_function(
    closure: &Closure,
    ptr_type: c::PTypeExpr,
    name_gen: &mut NameGen,
) -> c::Function {
    let void_self = "void_self";
    let self_ = "self";
    let void: c::PTypeExpr = "void".type_var().into();
    let rc = self_.var().arrow("rc");

    c::Function {
        return_type: void.clone(),
        name: closure.drop_name.clone(),
        parameters: vec![(void.ptr().into(), void_self.into())],
        body: Some(vec![
            // Cast the void pointer to the correct type.
            void_self
                .var()
                .cast(ptr_type.clone())
                .variable(self_, ptr_type),
            // Check if the reference count reaches zero
            rc.clone().eq(0.literal()).if_then_else(
                // Clean up the arguments.
                closure
                    .captured_variables_types
                    .iter()
                    .flat_map(|(field_name, field_type, field_type_expr)| {
                        let temp_name = name_gen.next(NameOptions::Var);
                        vec![self_
                            .var()
                            .arrow(field_name.clone())
                            .variable(temp_name.clone(), field_type_expr.clone())]
                        .extend_pipe(compile_drop(temp_name, field_type))
                    })
                    // And clean up the memory holding the closure's struct!
                    .chain(["free".var().call([self_.var()]).stmt()])
                    .collect::<Vec<_>>(),
                [rc.dec().stmt()],
            ),
        ]),
    }
}

fn compile_clone(var_c_name: Name, var_n_type: &Term) -> (c::Block, Name) {
    (
        match var_n_type {
            Term::Arrow {
                kind: ArrowKind::Type,
                ..
            } => vec![var_c_name.clone().var().arrow("rc").inc().stmt()],
            Term::Literal(Literal::Str) => {
                vec!["cloneStr".var().call([var_c_name.clone().var()]).stmt()]
            }
            _ => vec![],
        },
        var_c_name,
    )
}

fn compile_drop(var_name: Name, var_type: &Term) -> c::Block {
    let var = var_name.var();
    let drop = var.clone().arrow("drop");
    match var_type {
        Term::Arrow {
            kind: ArrowKind::Type,
            ..
        } => vec![drop.call([var]).stmt()],
        Term::Literal(Literal::Str) => vec!["dropStr".var().call([var]).stmt()],
        _ => vec![],
    }
}

/*
fn compile_let(name: Name, term: PTerm, body: PTerm, context: &mut Context) -> (c::Block, c::Expr, c::Block) {
    let term_type = term.infer_type_with_ctx(&mut context.n_vars).expect(&format!("Cannot infer type of {term}!"));
    let type_expression = compile_type_expr(&term_type, context).expect(&format!("Cannot compile {term_type}!")).into();
    let expression = compile_expr(term, context);
    let name = context.name_gen.next(NameOptions::Var);

    let declare = c::Statement::Declaration { type_expression, name, initializer: expression };
    let dispose = compile_destructor(name, &term_type);

    with_variable!(
        context.n_vars,
    );

    block.insert(0, declare);
    // Dispose of the variable at the end of the scope.
    block.extend(compile_distructor_of_type(term_type));

    todo!()
}
*/

fn function_c_type_declaration(
    arg_type: &PTerm,
    ret_type: &PTerm,
    name: Name,
    context: &mut Context,
) -> c::TopLevelDeclaration {
    let arg_type_expr = compile_type_expr(arg_type, context).unwrap();
    let ret_type_expr = compile_type_expr(ret_type, context).unwrap();

    let closure_ptr_type = name.clone().type_var().ptr();
    let call_type_expr = closure_call_type(
        closure_ptr_type.into(),
        ret_type_expr.into(),
        arg_type_expr.into(),
    );
    let drop_type_expr = closure_drop_type();

    c::TopLevelDeclaration::Struct(
        name,
        vec![
            ("int".type_var().into(), "rc".into()),
            (call_type_expr.into(), "call".into()),
            (drop_type_expr.into(), "drop".into()),
        ],
    )
}

fn tuple_field_name(i: usize) -> Name {
    Name::from(format!("field_{i}"))
}

fn compile_tuple_declaration(c: &Tuple) -> (Name, c::TopLevelDeclaration) {
    (
        c.c_type_name.clone(),
        c::TopLevelDeclaration::Struct(
            c.c_type_name.clone(),
            c.types
                .iter()
                .enumerate()
                .map(|(i, c_type)| (c_type.clone(), tuple_field_name(i)))
                .collect(),
        ),
    )
}

pub fn compile(term: PTerm) -> c::Program {
    let term_type = infer(&term, &mut Default::default()).expect("Still no error handling...");

    let mut context = Context::default();

    // This variable might be used in the future, to decide what to do with the
    // return value of the program.
    let _term_type_expr = compile_type_expr(&term_type, &mut context)
        .expect("Also not error handling for compilation...");

    let (expr_prelude, _expr_result_name) = compile_expr(term, &mut context);

    let main = c::Function {
        return_type: c::TypeExpr::Var("int".into()).into(),
        name: "main".into(),
        parameters: vec![],
        body: Some(expr_prelude),
    };

    let mut forward_declarations = Vec::<Name>::new();
    let mut declarations = Vec::<c::TopLevelDeclaration>::new();

    // Declare context.function_c_types.
    let function_c_types = context.function_c_types.clone();
    for ((arg_type, ret_type), name) in function_c_types {
        forward_declarations.push(name.clone());
        declarations.push(function_c_type_declaration(
            &arg_type,
            &ret_type,
            name,
            &mut context,
        ));
    }

    // Declare the closures.
    for closure in &context.closures {
        let (forward_declaration, declaration) =
            compile_closure_declarations(closure, &mut context.name_gen);
        forward_declarations.push(forward_declaration);
        declarations.extend(declaration);
    }

    // Declare the tuples.
    for tuple in context.tuple_c_types.values() {
        let (forward_declaration, declaration) = compile_tuple_declaration(tuple);
        forward_declarations.push(forward_declaration);
        declarations.push(declaration);
    }

    // Add the main function.
    declarations.push(c::TopLevelDeclaration::Function(main));

    // Combine the forward declarations and declarations.
    let all_declarations = forward_declarations
        .into_iter()
        .map(|name| c::TopLevelDeclaration::Typedef(name.clone().struct_type_var(), name))
        .chain(declarations.into_iter())
        .collect();

    c::Program {
        includes: vec![c::Include::Quote("nessie.h".into())],
        declarations: all_declarations,
    }
}

// TODO: Add `compile_clone` calls where appropriate. Where should they be added?
//       - When a name returned from a `compile_expr` call is used more than once.
fn compile_expr(term: PTerm, con: &mut Context) -> (c::Block, Name) {
    let term = normalize(&term);
    let term_type = infer(&term, &mut con.n_vars).unwrap();
    let term_type_expr = compile_type_expr(&term_type, con).unwrap();

    match term.as_ref() {
        Term::Var(name) => {
            let (_, var_c_name) = con.c_vars[name].clone();
            let var_type = con.n_vars[name].clone();
            compile_clone(var_c_name, &var_type)
        }
        Term::Appl(func, arg) =>
        // Should first save the closure pointer (lhs) in a variable,
        // then pass it to it's .call field along with the argument (rhs!).
        {
            let (func_perlude, func_var_name) = compile_expr(func.clone(), con);
            let func_type = infer(func, &mut con.n_vars).unwrap();
            let (arg_prelude, arg_var_name) = compile_expr(arg.clone(), con);

            // Call the function object with the argument.
            let output_var_name = con.name_gen.next(NameOptions::Var);
            let set_output = func_var_name
                .clone()
                .var()
                .arrow("call")
                .call([func_var_name.clone().var(), arg_var_name.var()])
                .variable(output_var_name.clone(), term_type_expr);
            // Dispose of the function. Don't dispose of the argument - the
            // function is responsible for that.
            let drop_func_and_arg = compile_drop(func_var_name, &func_type);

            (
                func_perlude
                    .extend_pipe(arg_prelude)
                    .extend_pipe_one(set_output)
                    .extend_pipe(drop_func_and_arg),
                output_var_name,
            )
        }
        Term::Arrow {
            kind: ArrowKind::Value,
            param_name,
            ty,
            body,
        } => {
            // Get a type expression for the parameter's type.
            let param_c_ty: c::PTypeExpr = compile_type_expr(ty, con).unwrap().into();

            // Infer the type of the body and get a type expression for it.
            let body_type = match term_type.as_ref() {
                Term::Arrow { body, .. } => body,
                _ => unreachable!(),
            };
            let body_c_type: c::PTypeExpr = compile_type_expr(body_type, con).unwrap().into();

            // Compile the body to an expression.
            let param_c_name = con.name_gen.next(NameOptions::Var);
            let (body_prelude, body_ret_name) =
                with_variable!(con.n_vars, (param_name, ty.clone()), {
                    with_variable!(
                        con.c_vars,
                        (param_name, (param_c_ty.clone(), param_c_name.clone())),
                        { compile_expr(body.clone(), con) }
                    )
                });

            // Get the captured variables.
            let captured_variables_types: Vec<(Name, PTerm, c::PTypeExpr)> =
                (term.free_vars().iter().map(|var_name| {
                    let (var_c_type, var_c_name) = con.c_vars.get(var_name).unwrap();
                    let var_n_type = con.n_vars.get(var_name).unwrap();
                    (var_c_name.clone(), var_n_type.clone(), var_c_type.clone())
                }))
                .collect();
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
                .map(|p| p.1.clone().var())
                .collect();

            let temp_var_name = con.name_gen.next(NameOptions::Var);
            let body = body_prelude
                .extend_pipe_one(body_ret_name.variable(temp_var_name.clone(), body_c_type.clone()))
                .extend_pipe_one(temp_var_name.var().ret());

            // Define a closure.
            let closure = Closure {
                struct_name: con.name_gen.next(NameOptions::ClosureStruct),
                call_name: con.name_gen.next(NameOptions::Call),
                make_name: con.name_gen.next(NameOptions::Make),
                drop_name: con.name_gen.next(NameOptions::Drop),
                body: c::Function {
                    name: con.name_gen.next(NameOptions::Impl),
                    return_type: body_c_type,
                    parameters,
                    body: Some(body),
                },
                captured_variables_types,
            };
            let closure_make_name = closure.make_name.clone();
            con.closures.push(closure);

            let output_var_name = con.name_gen.next(NameOptions::Var);
            let set_output = closure_make_name
                .var()
                .call(captured_variable_calls)
                .variable(output_var_name.clone(), term_type_expr);
            // Return a variable referencing the function.
            (vec![set_output], output_var_name)
        }
        Term::Arrow {
            kind: ArrowKind::Type,
            ..
        } => panic!(),
        Term::Literal(literal) => compile_literal_expr(literal, con),
        Term::TypeAnnotation(x, _) => compile_expr(x.clone(), con),
        Term::Let(name, _, rhs, body) => {
            let (rhs_prelude, var_name) = compile_expr(rhs.clone(), con);

            let typ = infer(rhs, &mut con.n_vars).unwrap();

            let (body_prelude, body_ret_name) = with_variable!(con.n_vars, (name, typ.clone()), {
                compile_expr(body.clone(), con)
            });

            let var_drop = compile_drop(var_name, &typ);

            let prelude = rhs_prelude.extend_pipe(body_prelude).extend_pipe(var_drop);

            (prelude, body_ret_name)
        }
        Term::Tuple(elements) => {
            let mut prelude = Vec::new();
            let name = con.name_gen.next(NameOptions::Var);

            // Add element preludes and collect names.
            let compiled_elements = elements
                .iter()
                .map(|x| {
                    let (x_prelude, x_name) = compile_expr(x.clone(), con);
                    prelude.extend(x_prelude);
                    x_name.var()
                })
                .collect::<Vec<_>>();

            // We can safely index this because we know the tuple type has been
            // added to the context when compiling the type expression.
            let tuple = con.tuple_c_types.get(&term_type).unwrap();

            // Add tuple creation.
            prelude.push(
                tuple
                    .make_name
                    .clone()
                    .var()
                    .call(compiled_elements)
                    .variable(name.clone(), term_type_expr),
            );

            (prelude, name)
        }
        Term::TupleType(_) => todo!(),
    }
}

fn compile_literal_expr(literal: &Literal, con: &mut Context) -> (c::Block, Name) {
    match literal {
        Literal::Prop => (vec![], "prop".into()),
        Literal::Type => (vec![], "type".into()),
        Literal::String(string) => {
            let name = con.name_gen.next(NameOptions::Var);
            (
                vec!["makeStr"
                    .var()
                    .call([string.clone().literal()])
                    .variable(name.clone(), "str".type_var())],
                name,
            )
        }
        Literal::StringAppend => (
            vec!["appendStrClosure".var().arrow("rc").inc().stmt()],
            "appendStrClosure".into(),
        ),
        Literal::Str => todo!(),
    }
}

fn compile_type_expr(term: &PTerm, con: &mut Context) -> Result<c::TypeExpr, ()> {
    let term = normalize(term);
    match term.as_ref() {
        Term::Literal(literal) => match literal {
            Literal::Prop => "prop".pipe(Ok),
            Literal::Type => "type".pipe(Ok),
            Literal::Str => "str".pipe(Ok),
            Literal::StringAppend | Literal::String(..) => Err(()),
        }
        .map(|var_name| var_name.type_var()),
        Term::Arrow {
            kind: ArrowKind::Type,
            param_name: _,
            ty,
            body,
        } => {
            let name = con
                .function_c_types
                .get(&(ty.clone(), body.clone()))
                .cloned()
                .unwrap_or_else(|| {
                    let name = con.name_gen.next(NameOptions::ClosureHeadType);
                    con.function_c_types
                        .insert((ty.clone(), body.clone()), name.clone());
                    name
                });
            Ok(name.type_var().ptr())
        }
        Term::TupleType(elements) => {
            let c_elements = elements
                .iter()
                .map(|e| compile_type_expr(e, con).map(Rc::new))
                .collect::<Result<Vec<_>, _>>()?;

            let name = con.name_gen.next(NameOptions::TupleType);
            let make_name = con.name_gen.next(NameOptions::Make);

            let tuple = Tuple {
                make_name,
                c_type_name: name.clone(),
                types: c_elements,
            };

            con.tuple_c_types.insert(term.clone(), tuple);

            Ok(name.type_var())
        }
        Term::TypeAnnotation(_, _) => Err(()),
        Term::Appl(_, _) => Err(()),
        Term::Var(_) => Err(()),
        Term::Let(_, _, _, _) => Err(()),
        Term::Tuple(_) => Err(()),
        Term::Arrow {
            kind: ArrowKind::Value,
            ..
        } => Err(()),
    }
}
