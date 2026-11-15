// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates
//
//! Regression tests for bridged execute_direct error handling.

use super::*;
use crate::constraint::Constraint;
use crate::expr::ExprValue;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::sync::Arc;

fn malformed_expr(sort: Sort, value: ExprValue) -> Expr {
    Expr {
        sort,
        value: Arc::new(value),
    }
}

fn assert_reserved_declaration_is_error_without_unwind(
    program: AYProgram,
    expected_operation: &str,
) {
    let outer = catch_unwind(AssertUnwindSafe(|| execute(&program)));
    let result = outer.expect("reserved declaration must not unwind through execute_direct");
    let error = result.expect_err("reserved declaration must fail closed");
    match error {
        ExecuteError::ConstraintExecution(reason) => assert!(
            reason.contains(expected_operation) && reason.contains("reserved"),
            "expected reserved {expected_operation} error, got: {reason}"
        ),
        other => panic!("expected ConstraintExecution, got: {other:?}"),
    }
}

#[test]
fn test_execute_direct_reserved_declarations_return_errors_without_unwinding() {
    let mut declare_const = AYProgram::qf_lia();
    let _ = declare_const.declare_const("fp", Sort::int());
    assert_reserved_declaration_is_error_without_unwind(declare_const, "declare_const");

    let mut declare_var = AYProgram::qf_lia();
    declare_var.add_constraint(Constraint::declare_var(
        "__ay_reserved_variable",
        Sort::int(),
    ));
    assert_reserved_declaration_is_error_without_unwind(declare_var, "declare_var");

    let mut declare_fun = AYProgram::qf_lia();
    declare_fun.declare_fun("__ay_reserved_function", vec![Sort::int()], Sort::int());
    assert_reserved_declaration_is_error_without_unwind(declare_fun, "declare_fun");
}

#[test]
fn test_execute_direct_reserved_definition_returns_error_without_unwinding() {
    let mut program = AYProgram::qf_lia();
    program.define_fun(
        "__ay_reserved_definition",
        vec![("x".to_string(), Sort::int())],
        Expr::var("x", Sort::int()),
    );
    assert_reserved_declaration_is_error_without_unwind(program, "define_fun");
}

#[test]
fn test_execute_direct_reserved_definition_parameter_returns_error_without_unwinding() {
    let mut program = AYProgram::qf_lia();
    program.define_fun(
        "identity",
        vec![("__ay_reserved_parameter".to_string(), Sort::int())],
        Expr::var("__ay_reserved_parameter", Sort::int()),
    );
    assert_reserved_declaration_is_error_without_unwind(program, "define_fun parameter");
}

/// A constant spelled like a declared datatype SELECTOR is a rebinding of an
/// ay function symbol, and the bridge must refuse it as an `ExecuteError`, not
/// unwind. This is the shape of `compiler_consumer-ice-2026-09-08T05_49_46`: the kernel
/// `Expr` struct's field `kind` became a selector `kind`, a local `kind` became
/// a constant `kind` declared AFTER the datatype, and the panicking
/// `declare_const` path unwound into the embedding compiler. trust-router pins
/// it on its side; this pins it at the ay boundary, for both entry points.
#[test]
fn test_execute_direct_constant_rebinding_a_selector_returns_error_without_unwinding() {
    let expr_sort = Sort::struct_type("Expr", [("kind", Sort::int())]);
    let mut program = AYProgram::new();
    program.set_logic("ALL");
    program.declare_datatype(expr_sort.datatype_sort().unwrap().clone());
    let _ = program.declare_const("kind", Sort::int());
    let e = program.declare_const("e", expr_sort);
    let selected = e.field_select("Expr", "kind", Sort::int());
    program.assert(selected.eq(Expr::var("kind", Sort::int())));
    program.check_sat();

    let assert_rebinding_error = |error: &ExecuteError, entry: &str| match error {
        ExecuteError::ConstraintExecution(reason) => assert!(
            reason.contains("declare_const")
                && reason.contains("'kind'")
                && reason.contains("already bound to a different declaration"),
            "{entry}: the refusal must name the rebinding of `kind`, got: {reason}"
        ),
        other => panic!("{entry}: expected ConstraintExecution, got: {other:?}"),
    };

    let outer = catch_unwind(AssertUnwindSafe(|| execute(&program)));
    let result =
        outer.expect("execute: a selector rebinding must not unwind through execute_direct");
    match result {
        Err(error) => assert_rebinding_error(&error, "execute"),
        Ok(result) => panic!("execute: ay must refuse the rebinding of `kind`, got {result:?}"),
    }

    let outer = catch_unwind(AssertUnwindSafe(|| execute_incremental(&program)));
    let result = outer
        .expect("execute_incremental: a selector rebinding must not unwind through execute_direct");
    match result {
        Err(error) => assert_rebinding_error(&error, "execute_incremental"),
        Ok(outcomes) => {
            panic!("execute_incremental: ay must refuse the rebinding of `kind`, got {outcomes:?}")
        }
    }
}

#[test]
fn test_execute_direct_bridged_string_sort_error_returns_expr_translation() {
    let mut program = AYProgram::new();
    program.set_logic("QF_SLIA");
    program.assert(Expr::true_());
    program.add_constraint(Constraint::GetValue(vec![malformed_expr(
        Sort::string(),
        ExprValue::StrConcat(Expr::bool_const(true), Expr::bool_const(false)),
    )]));

    let err = execute(&program).expect_err("malformed bridged string op should error");
    match err {
        ExecuteError::ExprTranslation(reason) => {
            assert!(
                reason.contains("string.concat"),
                "expected string bridge context, got: {reason}"
            );
        }
        other => panic!("expected ExprTranslation for bridged string op, got: {other:?}"),
    }
}

#[test]
fn test_execute_direct_quantifier_binder_collision_returns_error_without_unwinding() {
    // A quantifier binder that shadows a declared constant of a DIFFERENT sort
    // is a recoverable embedder mistake. `translate_quantifier` used to declare
    // bound variables through the PANICKING `Solver::declare_const`, so this
    // program unwound out of `execute` — in compiler_consumer, one ICE report for any
    // contract whose `forall`/`exists` binder shadows a variable of another
    // type (e.g. `fn f(x: u64) ensures forall x: bool, ...`).
    let mut program = AYProgram::new();
    program.set_logic("LIA");
    let _ = program.declare_const("x", Sort::int());
    program.assert(Expr::forall(
        vec![("x".to_string(), Sort::bool())],
        Expr::var("x", Sort::bool()),
    ));
    program.check_sat();

    let outer = catch_unwind(AssertUnwindSafe(|| execute(&program)));
    let result = outer.expect("binder collision must not unwind through execute_direct");
    let error = result.expect_err("binder collision must fail closed");
    match error {
        ExecuteError::ExprTranslation(reason) => assert!(
            reason.contains("declare_const") && reason.contains("already declared"),
            "expected the declare_const collision to be named, got: {reason}"
        ),
        other => panic!("expected ExprTranslation, got: {other:?}"),
    }
}

#[test]
fn test_execute_direct_bridged_seq_sort_error_returns_expr_translation() {
    let mut program = AYProgram::new();
    program.set_logic("QF_SEQLIA");
    program.assert(Expr::true_());
    program.add_constraint(Constraint::GetValue(vec![malformed_expr(
        Sort::seq(Sort::int()),
        ExprValue::SeqConcat(Expr::int(1), Expr::int(2)),
    )]));

    let err = execute(&program).expect_err("malformed bridged sequence op should error");
    match err {
        ExecuteError::ExprTranslation(reason) => {
            assert!(
                reason.contains("seq.concat"),
                "expected sequence bridge context, got: {reason}"
            );
        }
        other => panic!("expected ExprTranslation for bridged sequence op, got: {other:?}"),
    }
}
