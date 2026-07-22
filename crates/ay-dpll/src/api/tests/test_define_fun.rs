// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for define-fun API (#8613).

use num_bigint::BigInt;

use crate::api::*;

fn has_validated_sat_model(solver: &mut Solver, label: &str) -> bool {
    let result = solver.check_sat();
    assert!(
        !result.is_unsat(),
        "{label}: expected SAT or Unknown, got {result:?}"
    );
    result.is_sat() && result.was_model_validated()
}

/// Basic define-fun: sum(a, b) = a + b, verify inline expansion.
#[test]
fn test_define_fun_sum() {
    let mut solver = Solver::try_new(Logic::QfLia).unwrap();
    let x = solver.declare_const("x", Sort::Int);

    // define-fun sum(a: Int, b: Int) -> Int = a + b
    let sum = solver
        .try_define_fun(
            "sum",
            &[("a", Sort::Int), ("b", Sort::Int)],
            Sort::Int,
            |s, params| s.try_add(params[0], params[1]),
        )
        .unwrap();

    // sum(x, 1) == 5  =>  x + 1 == 5  =>  x == 4
    let one = solver.int_const(1);
    let result = solver.try_apply(&sum, &[x, one]).unwrap();
    let five = solver.int_const(5);
    let eq = solver.try_eq(result, five).unwrap();
    solver.try_assert_term(eq).unwrap();

    if !has_validated_sat_model(&mut solver, "sum(x, 1) == 5") {
        return;
    }
    match solver.value(x) {
        Some(ModelValue::Int(v)) => assert_eq!(v, BigInt::from(4)),
        other => panic!("expected Int(4), got {other:?}"),
    }
}

/// Define-fun with Bool return: is_positive(x) = x > 0.
#[test]
fn test_define_fun_bool_return() {
    let mut solver = Solver::try_new(Logic::QfLia).unwrap();
    let x = solver.declare_const("x", Sort::Int);

    let is_positive = solver
        .try_define_fun(
            "is_positive",
            &[("n", Sort::Int)],
            Sort::Bool,
            |s, params| {
                let zero = s.int_const(0);
                s.try_gt(params[0], zero)
            },
        )
        .unwrap();

    // assert is_positive(x) => x > 0
    let check = solver.try_apply(&is_positive, &[x]).unwrap();
    solver.try_assert_term(check).unwrap();

    // assert x < 2 => x == 1
    let two = solver.int_const(2);
    let lt = solver.try_lt(x, two).unwrap();
    solver.try_assert_term(lt).unwrap();

    let result = solver.check_sat();
    assert!(
        !result.is_unsat(),
        "is_positive(x) && x < 2 should be SAT or Unknown, got {result:?}"
    );
}

/// Nullary define-fun: constant alias.
#[test]
fn test_define_fun_nullary() {
    let mut solver = Solver::try_new(Logic::QfLia).unwrap();
    let x = solver.declare_const("x", Sort::Int);

    // define-fun forty_two() -> Int = 42
    let forty_two = solver
        .try_define_fun(
            "forty_two",
            &[],
            Sort::Int,
            |s, _params| Ok(s.int_const(42)),
        )
        .unwrap();

    let val = solver.try_apply(&forty_two, &[]).unwrap();
    let eq = solver.try_eq(x, val).unwrap();
    solver.try_assert_term(eq).unwrap();

    if !has_validated_sat_model(&mut solver, "x == forty_two()") {
        return;
    }
    match solver.value(x) {
        Some(ModelValue::Int(v)) => assert_eq!(v, BigInt::from(42)),
        other => panic!("expected Int(42), got {other:?}"),
    }
}

/// Multiple applications of the same defined function produce correct
/// independent expansions (each application gets its own let-binding).
#[test]
fn test_define_fun_multiple_applications() {
    let mut solver = Solver::try_new(Logic::QfLia).unwrap();
    let x = solver.declare_const("x", Sort::Int);
    let y = solver.declare_const("y", Sort::Int);

    let double = solver
        .try_define_fun("double", &[("n", Sort::Int)], Sort::Int, |s, params| {
            let two = s.int_const(2);
            s.try_mul(params[0], two)
        })
        .unwrap();

    // assert double(x) == 10 => x == 5
    let dx = solver.try_apply(&double, &[x]).unwrap();
    let ten = solver.int_const(10);
    let eq1 = solver.try_eq(dx, ten).unwrap();
    solver.try_assert_term(eq1).unwrap();

    // assert double(y) == 6 => y == 3
    let dy = solver.try_apply(&double, &[y]).unwrap();
    let six = solver.int_const(6);
    let eq2 = solver.try_eq(dy, six).unwrap();
    solver.try_assert_term(eq2).unwrap();

    if !has_validated_sat_model(&mut solver, "double(x) and double(y)") {
        return;
    }
    match solver.value(x) {
        Some(ModelValue::Int(v)) => assert_eq!(v, BigInt::from(5)),
        other => panic!("expected Int(5) for x, got {other:?}"),
    }
    match solver.value(y) {
        Some(ModelValue::Int(v)) => assert_eq!(v, BigInt::from(3)),
        other => panic!("expected Int(3) for y, got {other:?}"),
    }
}

/// Return sort mismatch is detected.
#[test]
fn test_define_fun_sort_mismatch() {
    let mut solver = Solver::try_new(Logic::QfLia).unwrap();

    // Try to define a function with Bool return but Int body
    let result = solver.try_define_fun(
        "bad",
        &[("n", Sort::Int)],
        Sort::Bool,                 // declared Bool
        |_s, params| Ok(params[0]), // body is Int
    );

    assert!(result.is_err());
    let err = result.unwrap_err();
    assert!(matches!(err, SolverError::SortMismatch { .. }));
}

/// Arity mismatch on apply is detected.
#[test]
fn test_define_fun_arity_mismatch() {
    let mut solver = Solver::try_new(Logic::QfLia).unwrap();

    let f = solver
        .try_define_fun(
            "f",
            &[("a", Sort::Int), ("b", Sort::Int)],
            Sort::Int,
            |s, params| s.try_add(params[0], params[1]),
        )
        .unwrap();

    let one = solver.int_const(1);
    let result = solver.try_apply(&f, &[one]); // 1 arg, expects 2
    assert!(result.is_err());
}

/// Lower-level define-fun body API supports facade translators that already
/// created parameter variables before translating the body.
#[test]
fn test_define_fun_body_api() {
    let mut solver = Solver::try_new(Logic::QfLia).unwrap();
    let x = solver.declare_const("x", Sort::Int);
    let n = solver.fresh_var("n", Sort::Int);
    let one = solver.int_const(1);
    let body = solver.try_add(n, one).unwrap();

    let inc = solver
        .try_define_fun_body("inc", &[("n", n)], Sort::Int, body)
        .unwrap();

    let result = solver.try_apply(&inc, &[x]).unwrap();
    assert!(
        matches!(solver.term_kind(result), TermKind::App { name, .. } if name == "+"),
        "define-fun application should be structurally inlined"
    );
    let five = solver.int_const(5);
    let eq = solver.try_eq(result, five).unwrap();
    solver.try_assert_term(eq).unwrap();

    if !has_validated_sat_model(&mut solver, "inc(x) == 5") {
        return;
    }
    match solver.value(x) {
        Some(ModelValue::Int(v)) => assert_eq!(v, BigInt::from(4)),
        other => panic!("expected Int(4), got {other:?}"),
    }
}

#[test]
fn test_define_fun_body_rejects_non_variable_param() {
    let mut solver = Solver::try_new(Logic::QfLia).unwrap();
    let one = solver.int_const(1);

    let result = solver.try_define_fun_body("bad", &[("n", one)], Sort::Int, one);

    assert!(matches!(
        result,
        Err(SolverError::InvalidArgument {
            operation: "define_fun",
            ..
        })
    ));
}

#[test]
fn native_api_rejects_same_name_definition_and_declaration_aliases() {
    let mut solver = Solver::try_new(Logic::QfUflia).unwrap();
    let defined = solver
        .try_define_fun("f", &[("x", Sort::Int)], Sort::Int, |_solver, params| {
            Ok(params[0])
        })
        .unwrap();

    assert!(matches!(
        solver.try_declare_fun("f", &[Sort::Bool], Sort::Bool),
        Err(SolverError::InvalidArgument {
            operation: "declare_fun",
            ..
        })
    ));
    assert!(matches!(
        solver.try_define_fun("f", &[("x", Sort::Bool)], Sort::Bool, |_solver, params| {
            Ok(params[0])
        }),
        Err(SolverError::InvalidArgument {
            operation: "define_fun",
            ..
        })
    ));

    let one = solver.int_const(1);
    assert_eq!(solver.try_apply(&defined, &[one]).unwrap(), one);

    let declared = solver
        .try_declare_fun("g", &[Sort::Int], Sort::Int)
        .unwrap();
    assert!(matches!(
        solver.try_declare_fun("g", &[Sort::Bool], Sort::Bool),
        Err(SolverError::InvalidArgument {
            operation: "declare_fun",
            ..
        })
    ));
    assert!(matches!(
        solver.try_define_fun("g", &[("x", Sort::Bool)], Sort::Bool, |_solver, params| {
            Ok(params[0])
        }),
        Err(SolverError::InvalidArgument {
            operation: "define_fun",
            ..
        })
    ));
    assert_eq!(declared.domain(), &[Sort::Int]);
}

#[test]
fn forged_same_name_handle_cannot_select_definition_with_wrong_signature() {
    let mut solver = Solver::try_new(Logic::QfUflia).unwrap();
    solver
        .try_define_fun("f", &[("x", Sort::Int)], Sort::Int, |_solver, params| {
            Ok(params[0])
        })
        .unwrap();

    let forged = FuncDecl::new("f".to_string(), vec![Sort::Bool], Sort::Bool);
    let value = solver.bool_const(true);
    assert!(matches!(
        solver.try_apply(&forged, &[value]),
        Err(SolverError::InvalidArgument {
            operation: "apply",
            ..
        })
    ));
}

#[test]
fn forged_undeclared_function_handle_cannot_create_an_application() {
    let mut solver = Solver::try_new(Logic::QfUf).unwrap();
    let forged = FuncDecl::new("missing".to_string(), vec![Sort::Int], Sort::Int);
    let value = solver.int_const(1);
    assert!(matches!(
        solver.try_apply(&forged, &[value]),
        Err(SolverError::InvalidArgument {
            operation: "apply",
            ..
        })
    ));
}

#[test]
fn define_fun_body_builder_cannot_introduce_same_name_declaration() {
    let mut solver = Solver::try_new(Logic::QfUflia).unwrap();
    let result = solver.try_define_fun("f", &[("x", Sort::Int)], Sort::Int, |solver, params| {
        solver.try_declare_fun("f", &[Sort::Bool], Sort::Bool)?;
        Ok(params[0])
    });

    assert!(matches!(
        result,
        Err(SolverError::InvalidArgument {
            operation: "define_fun",
            ..
        })
    ));
}

#[test]
fn reset_assertions_preserves_inline_function_definitions() {
    let mut solver = Solver::try_new(Logic::QfLia).unwrap();
    let increment = solver
        .try_define_fun(
            "increment",
            &[("x", Sort::Int)],
            Sort::Int,
            |solver, params| {
                let one = solver.int_const(1);
                solver.try_add(params[0], one)
            },
        )
        .unwrap();

    solver.try_reset_assertions().unwrap();

    let two = solver.int_const(2);
    let applied = solver.try_apply(&increment, &[two]).unwrap();
    assert!(
        matches!(solver.term_kind(applied), TermKind::App { name, .. } if name == "+"),
        "reset-assertions must not turn a defined function into an uninterpreted application"
    );
    let three = solver.int_const(3);
    let equality = solver.try_eq(applied, three).unwrap();
    solver.try_assert_term(equality).unwrap();
    assert!(!solver.check_sat().is_unsat());
}

#[test]
fn repeated_native_constant_declaration_is_idempotent() {
    let mut solver = Solver::try_new(Logic::QfLia).unwrap();
    let first = solver.declare_const("x", Sort::Int);
    let second = solver.declare_const("x", Sort::Int);
    assert_eq!(first, second);
}

#[test]
fn repeated_native_constant_uses_its_exact_identity_after_function_alias() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let constant = solver.declare_const("surface", Sort::Int);
    let function = solver
        .try_declare_fun("private_surface", &[Sort::Int], Sort::Int)
        .unwrap();
    solver
        .try_register_native_function_alias("surface", &function)
        .unwrap();

    assert_eq!(solver.declare_const("surface", Sort::Int), constant);
}

#[test]
fn native_function_alias_rejects_forged_declaration_handles() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let missing = FuncDecl::new("missing".to_string(), vec![Sort::Int], Sort::Int);
    assert!(matches!(
        solver.try_register_native_function_alias("surface", &missing),
        Err(SolverError::InvalidArgument {
            operation: "register_native_function_alias",
            ..
        })
    ));

    let declared = solver
        .try_declare_fun("actual", &[Sort::Int], Sort::Int)
        .unwrap();
    let wrong_signature = FuncDecl::new(declared.name().to_string(), vec![Sort::Bool], Sort::Bool);
    assert!(matches!(
        solver.try_register_native_function_alias("surface", &wrong_signature),
        Err(SolverError::InvalidArgument {
            operation: "register_native_function_alias",
            ..
        })
    ));
}

#[test]
#[should_panic(expected = "already declared with sort")]
fn native_constant_rejects_same_name_at_different_sort() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let _ = solver.declare_const("x", Sort::Int);
    let _ = solver.declare_const("x", Sort::Bool);
}

#[test]
#[should_panic(expected = "already bound to a different declaration")]
fn native_constant_rejects_existing_function_name() {
    let mut solver = Solver::try_new(Logic::QfUf).unwrap();
    let _ = solver.declare_fun("f", &[Sort::Int], Sort::Int);
    let _ = solver.declare_const("f", Sort::Int);
}

#[test]
#[should_panic(expected = "identity '__private_x' is already in use")]
fn adapter_constant_identity_must_be_unique() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let _ = solver.declare_const_with_fresh_identity("x", "__private_x", Sort::Int);
    let _ = solver.declare_const_with_fresh_identity("x", "__private_x", Sort::Bool);
}

#[test]
fn adapter_display_name_cannot_alias_later_native_constant() {
    let mut solver = Solver::try_new(Logic::All).unwrap();
    let adapter = solver.declare_const_with_fresh_identity("x", "__private_x", Sort::Bool);
    let native = solver.declare_const("x", Sort::Int);

    assert_ne!(adapter, native);
    assert_eq!(solver.term_sort(adapter), Sort::Bool);
    assert_eq!(solver.term_sort(native), Sort::Int);
}

#[test]
fn native_declarations_survive_assertion_scope_pop() {
    let mut solver = Solver::try_new(Logic::QfUflia).unwrap();
    solver.try_push().unwrap();
    let x = solver.declare_const("x", Sort::Int);
    let function = solver
        .try_declare_fun("f", &[Sort::Int], Sort::Int)
        .unwrap();
    solver.try_pop().unwrap();

    assert_eq!(solver.declare_const("x", Sort::Int), x);
    assert!(matches!(
        solver.try_declare_fun("f", &[Sort::Bool], Sort::Bool),
        Err(SolverError::InvalidArgument {
            operation: "declare_fun",
            ..
        })
    ));
    let one = solver.int_const(1);
    let application = solver.try_apply(&function, &[one]).unwrap();
    let equality = solver.try_eq(application, one).unwrap();
    solver.try_assert_term(equality).unwrap();
    assert!(!solver.check_sat().is_unsat());
}

#[test]
fn native_declarations_invalidate_the_preceding_decision() {
    let mut solver = Solver::try_new(Logic::QfUf).unwrap();

    let _ = solver.check_sat();
    let _ = solver.declare_const("x", Sort::Int);
    assert!(matches!(solver.try_get_model(), Err(SolverError::NoResult)));

    let _ = solver.check_sat();
    let function = solver
        .try_declare_fun("private_f", &[Sort::Int], Sort::Int)
        .unwrap();
    assert!(matches!(solver.try_get_model(), Err(SolverError::NoResult)));

    let _ = solver.check_sat();
    solver
        .try_register_native_function_alias("f", &function)
        .unwrap();
    assert!(matches!(solver.try_get_model(), Err(SolverError::NoResult)));

    let _ = solver.check_sat();
    solver
        .try_register_native_function_alias("f", &function)
        .unwrap();
    assert!(
        solver.try_get_model().is_ok(),
        "an exact alias re-registration is a semantic no-op"
    );

    let _ = solver.check_sat();
    solver
        .try_define_fun(
            "identity",
            &[("x", Sort::Int)],
            Sort::Int,
            |_solver, params| Ok(params[0]),
        )
        .unwrap();
    assert!(matches!(solver.try_get_model(), Err(SolverError::NoResult)));

    let parameter = solver.declare_const("definition_parameter", Sort::Int);
    let _ = solver.check_sat();
    solver
        .try_define_fun_body("identity_body", &[("x", parameter)], Sort::Int, parameter)
        .unwrap();
    assert!(matches!(solver.try_get_model(), Err(SolverError::NoResult)));
}

#[test]
fn repeated_native_function_declaration_is_an_exact_no_op() {
    let mut solver = Solver::try_new(Logic::QfUf).unwrap();
    let first = solver
        .try_declare_fun("f", &[Sort::Int], Sort::Int)
        .unwrap();
    let event_count = solver.native_replay_events().len();
    let _ = solver.check_sat();
    let second = solver
        .try_declare_fun("f", &[Sort::Int], Sort::Int)
        .unwrap();

    assert_eq!(first, second);
    assert_eq!(solver.native_replay_events().len(), event_count + 1);
    assert!(
        solver.try_get_model().is_ok(),
        "an exact primary redeclaration must preserve the preceding result"
    );
}
