use crate::c;
use crate::c::combine_traits::*;
use crate::global::*;
use crate::name::Name;
use crate::term::{infer, normalize, ArrowKind, Literal, PTerm, Pattern, Term, TypeContext};
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

#[derive(Debug, Clone)]
struct ExprRet {
    c_name: Name,
    c_type: c::PTypeExpr,
    n_type: PTerm,
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
    drop_name: Name,
    types: Vec<(PTerm, c::PTypeExpr)>,
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
    con: &mut Context,
) -> [c::TopLevelDeclaration; 5] {
    use c::TopLevelDeclaration::Function;

    let struct_ptr_type: c::PTypeExpr = closure.struct_name.clone().type_var().ptr().into();

    [
        // Struct.
        closure_struct(closure, struct_ptr_type.clone()),
        // Function.
        Function(closure_impl_function(closure)),
        Function(closure_call_function(closure, struct_ptr_type.clone())),
        Function(closure_drop_function(closure, struct_ptr_type.clone(), con)),
        Function(closure_make_function(closure, struct_ptr_type)),
    ]
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
    c::TopLevelDeclaration::Struct(closure.struct_name.clone(), Some(fields))
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
    con: &mut Context,
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
                        let temp_name = con.name_gen.next(NameOptions::Var);
                        vec![self_
                            .var()
                            .arrow(field_name.clone())
                            .variable(temp_name.clone(), field_type_expr.clone())]
                        .extend_pipe(compile_drop(temp_name, field_type, con))
                    })
                    // And clean up the memory holding the closure's struct!
                    .chain(["free".var().call([self_.var()]).stmt()])
                    .collect::<Vec<_>>(),
                [rc.dec().stmt()],
            ),
        ]),
    }
}

fn compile_clone(var_c_name: Name, var_n_type: &Term) -> c::Block {
    match var_n_type {
        Term::Arrow {
            kind: ArrowKind::Type,
            ..
        } => vec![var_c_name.clone().var().arrow("rc").inc().stmt()],
        Term::Literal(Literal::Str) => {
            vec!["cloneStr".var().call([var_c_name.clone().var()]).stmt()]
        }
        _ => vec![],
    }
}

fn compile_drop(var_c_name: Name, var_type: &Term, con: &Context) -> c::Block {
    let var = var_c_name.var();
    let drop = var.clone().arrow("drop");
    match var_type {
        Term::Arrow {
            kind: ArrowKind::Type,
            ..
        } => vec![drop.call([var]).stmt()],
        Term::Literal(Literal::Str) => vec!["dropStr".var().call([var]).stmt()],
        Term::TupleType(_) => {
            let tuple = &con.tuple_c_types[var_type];

            vec![tuple.drop_name.clone().var().call([var]).stmt()]
        }
        _ => todo!(),
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
        ]
        .pipe(Some),
    )
}

fn tuple_field_name(i: usize) -> Name {
    Name::from(format!("field_{i}"))
}

fn compile_tuple_drop(tuple: &Tuple, con: &mut Context) -> c::Function {
    let self_name: Name = "self".into();
    c::Function {
        name: tuple.drop_name.clone(),
        parameters: vec![(
            tuple.c_type_name.clone().type_var().into(),
            self_name.clone(),
        )],
        return_type: "void".type_var().into(),
        body: tuple
            .types
            .iter()
            .enumerate()
            .flat_map(|(i, (n_type, c_type))| {
                let field_name = tuple_field_name(i);
                let temp = con.name_gen.next(NameOptions::Var);

                let decl_temp = self_name
                    .clone()
                    .var()
                    .dot(field_name)
                    .variable(temp.clone(), c_type.clone());

                vec![decl_temp].extend_pipe(compile_drop(temp, n_type, con))
            })
            .collect::<Vec<_>>()
            .pipe(Some),
    }
}

fn compile_tuple_declaration(c: &Tuple, con: &mut Context) -> [c::TopLevelDeclaration; 2] {
    [
        c::TopLevelDeclaration::Struct(
            c.c_type_name.clone(),
            c.types
                .iter()
                .enumerate()
                .map(|(i, (_, c_type))| (c_type.clone(), tuple_field_name(i)))
                .collect::<Vec<_>>()
                .pipe(Some),
        ),
        c::TopLevelDeclaration::Function(compile_tuple_drop(c, con)),
    ]
}

pub fn compile(term: &PTerm) -> c::Program {
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

    let mut declarations = Vec::<c::TopLevelDeclaration>::new();

    // Declare context.function_c_types.
    let function_c_types = context.function_c_types.clone();
    for ((arg_type, ret_type), name) in function_c_types {
        declarations.push(function_c_type_declaration(
            &arg_type,
            &ret_type,
            name,
            &mut context,
        ));
    }

    // Declare the closures.
    let closures = context.closures;
    context.closures = Vec::new();
    for closure in closures {
        let declaration = compile_closure_declarations(&closure, &mut context);
        declarations.extend(declaration);
    }

    // Declare the tuples.
    let tuples = context.tuple_c_types.values().cloned().collect::<Vec<_>>();
    for tuple in tuples {
        let struct_declarations = compile_tuple_declaration(&tuple, &mut context);
        declarations.extend(struct_declarations);
    }

    // Add the main function.
    declarations.push(c::TopLevelDeclaration::Function(main));

    c::Program {
        includes: vec![c::Include::Quote("nessie.h".into())],
        declarations,
    }
}

fn flatten<T>(iter: impl IntoIterator<Item = impl IntoIterator<Item = T>>) -> Vec<T> {
    iter.into_iter().flatten().collect()
}

fn and_all(iter: impl IntoIterator<Item = c::Expr>) -> c::Expr {
    iter.into_iter()
        .reduce(|a, b| c::Expr::Binary(c::BinaryOp::And, Box::new(a), Box::new(b)))
        .unwrap()
}

fn unzip3<T, U, V>(i: impl IntoIterator<Item = (T, U, V)>) -> (Vec<T>, Vec<U>, Vec<V>) {
    let mut a = Vec::new();
    let mut b = Vec::new();
    let mut c = Vec::new();
    for (x, y, z) in i {
        a.push(x);
        b.push(y);
        c.push(z);
    }
    (a, b, c)
}

struct CompiledPattern {
    prelude: c::Block,
    cond: c::Expr,
    bindings: Vec<(Name, ExprRet)>,
}

fn compile_pattern(pattern: &Pattern, input_var: &ExprRet, con: &mut Context) -> CompiledPattern {
    match pattern {
        Pattern::Var(name) => CompiledPattern {
            prelude: vec![],
            bindings: vec![(name.clone(), input_var.clone())],
            cond: "true".var().into(),
        },
        Pattern::UnTuple(patterns) => {
            let element_types = match input_var.n_type.as_ref() {
                Term::TupleType(element_types) => element_types,
                _ => panic!(),
            };

            // We know this tuple type has been compiled before so it must be in the map.
            let tuple_c_type = con.tuple_c_types.get(&input_var.n_type).unwrap();

            let mut prelude = Vec::new();

            // Create a variable for each element type of the tuple type by
            // creating a statement that access the input of the pattern.
            let field_vars = element_types
                .iter()
                .enumerate()
                .map(|(i, field_n_type)| {
                    let field_name = tuple_field_name(i);
                    let field_c_type = tuple_c_type.types[i].1.clone();
                    let field_var_name = con.name_gen.next(NameOptions::Var);
                    let field_var_decl = input_var
                        .c_name
                        .clone()
                        .var()
                        .dot(field_name)
                        .variable(field_var_name.clone(), field_c_type.clone());
                    let clone_field = compile_clone(field_var_name.clone(), field_n_type);

                    prelude.push(field_var_decl);
                    prelude.extend(clone_field);
                    ExprRet {
                        c_name: field_var_name,
                        c_type: field_c_type,
                        n_type: field_n_type.clone(),
                    }
                })
                .collect::<Vec<_>>();

            let (preludes, conds, bindings) = patterns
                .iter()
                .zip(field_vars)
                .map(|(pat, field_var)| compile_pattern(pat, &field_var, con))
                .map(
                    |CompiledPattern {
                         prelude,
                         cond,
                         bindings,
                     }| (prelude, cond, bindings),
                )
                .pipe(unzip3);

            CompiledPattern {
                prelude: prelude.extend_pipe(flatten(preludes)),
                cond: and_all(conds),
                bindings: flatten(bindings),
            }
        }
    }
}

// TODO: Add `compile_clone` calls where appropriate. Where should they be added?
//       - When a name returned from a `compile_expr` call is used more than once.
fn compile_expr(term: &PTerm, con: &mut Context) -> (c::Block, ExprRet) {
    let term = normalize(&term);
    let term_type = infer(&term, &mut con.n_vars).unwrap();
    let term_type_expr: c::PTypeExpr = compile_type_expr(&term_type, con).unwrap().into();

    let (prelude, out_name) = match term.as_ref() {
        Term::Var(name) => {
            let (_, var_c_name) = con.c_vars[name].clone();
            let var_type = con.n_vars[name].clone();
            (compile_clone(var_c_name.clone(), &var_type), var_c_name)
        }
        Term::Appl(func, arg) =>
        // Should first save the closure pointer (lhs) in a variable,
        // then pass it to it's .call field along with the argument (rhs!).
        {
            let (func_perlude, func_var) = compile_expr(func, con);
            let (arg_prelude, arg_var) = compile_expr(arg, con);

            // Call the function object with the argument.
            let output_var_name = con.name_gen.next(NameOptions::Var);
            let set_output = func_var
                .c_name
                .clone()
                .var()
                .arrow("call")
                .call([func_var.c_name.clone().var(), arg_var.c_name.var()])
                .variable(output_var_name.clone(), term_type_expr.clone());
            // Dispose of the function. Don't dispose of the argument - the
            // function is responsible for that.
            let drop_func_and_arg = compile_drop(func_var.c_name, &func_var.n_type, con);

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
            let (body_prelude, body_ret) = with_variable!(con.n_vars, (param_name, ty.clone()), {
                with_variable!(
                    con.c_vars,
                    (param_name, (param_c_ty.clone(), param_c_name.clone())),
                    { compile_expr(body, con) }
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
                .extend_pipe_one(
                    body_ret
                        .c_name
                        .variable(temp_var_name.clone(), body_c_type.clone()),
                )
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
                .variable(output_var_name.clone(), term_type_expr.clone());
            // Return a variable referencing the function.
            (vec![set_output], output_var_name)
        }
        Term::Arrow {
            kind: ArrowKind::Type,
            ..
        } => panic!(),
        Term::Literal(literal) => compile_literal_expr(literal, con),
        Term::TypeAnnotation(x, _) => {
            compile_expr(x, con).pipe(|(prelude, var)| (prelude, var.c_name))
        }
        Term::Let(name, _, rhs, body) => {
            let (rhs_prelude, var) = compile_expr(rhs, con);

            let typ = infer(rhs, &mut con.n_vars).unwrap();

            let (body_prelude, body_ret) =
                with_variable!(con.n_vars, (name, typ.clone()), { compile_expr(body, con) });

            let var_drop = compile_drop(var.c_name, &typ, con);

            let prelude = rhs_prelude.extend_pipe(body_prelude).extend_pipe(var_drop);

            (prelude, body_ret.c_name)
        }
        Term::Tuple(elements) => {
            let mut prelude = Vec::new();
            let name = con.name_gen.next(NameOptions::Var);

            // Add element preludes and collect names.
            let compiled_elements = elements
                .iter()
                .map(|x| {
                    let (x_prelude, x_var) = compile_expr(x, con);
                    prelude.extend(x_prelude);
                    x_var.c_name.var()
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
                    .variable(name.clone(), term_type_expr.clone()),
            );

            (prelude, name)
        }
        Term::Match(input, cases) => {
            let (input_prelude, input_var) = compile_expr(input, con);
            let output_name = con.name_gen.next(NameOptions::Var);

            let prelude = input_prelude
                .extend_pipe_one(term_type_expr.clone().declare(output_name.clone(), None));

            // Compile the match to a series of ifs nested in each other's else.
            let match_block = cases
                .iter()
                .rev()
                .fold(None, |next_case_compiled, (pattern, case)| {
                    let compiled_pattern = compile_pattern(pattern, &input_var, con);
                    let n_vars: Vec<_> = compiled_pattern
                        .bindings
                        .iter()
                        .map(|(n, var)| (n, var.n_type.clone()))
                        .collect();
                    let c_vars: Vec<_> = compiled_pattern
                        .bindings
                        .iter()
                        .map(|(n, var)| (n, (var.c_type.clone(), var.c_name.clone())))
                        .collect();

                    let (case_prelude, case_var) = with_variables!(con.n_vars, n_vars, {
                        with_variables!(con.c_vars, c_vars, { compile_expr(case, con) })
                    });

                    let if_statement = c::Statement::If(
                        compiled_pattern.cond.clone(),
                        case_prelude.extend_pipe_one(c::Statement::Assign(
                            output_name.clone().var(),
                            case_var.c_name.var(),
                        )),
                        next_case_compiled,
                    );

                    let drop_vars: Vec<_> = compiled_pattern
                        .bindings
                        .iter()
                        .flat_map(|(_, var)| compile_drop(var.c_name.clone(), &var.n_type, con))
                        .collect();

                    compiled_pattern
                        .prelude
                        .extend_pipe_one(if_statement)
                        .extend_pipe(drop_vars)
                        .pipe(Some)
                })
                .unwrap_or_else(Vec::new);

            let drop_input = compile_drop(input_var.c_name.clone(), &input_var.n_type, con);

            (
                prelude.extend_pipe(match_block).extend_pipe(drop_input),
                output_name,
            )
        }
        Term::TupleType(_) => todo!(),
    };

    (
        prelude,
        ExprRet {
            c_name: out_name.clone(),
            c_type: term_type_expr,
            n_type: term_type,
        },
    )
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
        Term::TupleType(elements) => con
            .tuple_c_types
            .get(&term)
            .map(|tuple| Ok(tuple.c_type_name.clone()))
            .unwrap_or_else(|| {
                let c_elements = elements
                    .iter()
                    .map(|n_type| {
                        compile_type_expr(n_type, con)
                            .map(Rc::new)
                            .map(|c_type| (n_type.clone(), c_type))
                    })
                    .collect::<Result<Vec<_>, _>>()?;

                let name = con.name_gen.next(NameOptions::TupleType);
                let make_name = con.name_gen.next(NameOptions::Make);

                let tuple = Tuple {
                    make_name,
                    drop_name: con.name_gen.next(NameOptions::Drop),
                    c_type_name: name.clone(),
                    types: c_elements,
                };

                con.tuple_c_types.insert(term.clone(), tuple);

                Ok(name)
            })
            .map(c::TypeExpr::Var),
        Term::TypeAnnotation(_, _) => Err(()),
        Term::Appl(_, _) => Err(()),
        Term::Var(_) => Err(()),
        Term::Let(_, _, _, _) => Err(()),
        Term::Tuple(_) => Err(()),
        Term::Arrow {
            kind: ArrowKind::Value,
            ..
        } => Err(()),
        Term::Match(_, _) => Err(()),
    }
}
