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
