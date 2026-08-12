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
