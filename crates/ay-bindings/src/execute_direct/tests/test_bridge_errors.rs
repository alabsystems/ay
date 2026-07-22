// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates
//
//! Regression tests for bridged execute_direct error handling.

use super::*;
use crate::constraint::Constraint;
use crate::expr::ExprValue;
use std::sync::Arc;

fn malformed_expr(sort: Sort, value: ExprValue) -> Expr {
    Expr {
        sort,
        value: Arc::new(value),
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
