// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

use crate::error::SortError;
use crate::expr::Expr;
use crate::program::AYProgram;
use crate::sort::Sort;

#[test]
fn test_omt_program() {
    let mut program = AYProgram::new();
    program.set_logic("QF_LRA");

    let x = program.declare_const("x", Sort::real());
    let y = program.declare_const("y", Sort::real());

    program.assert(x.clone().real_ge(Expr::real_const(0)));
    program.assert(y.clone().real_ge(Expr::real_const(0)));

    program.maximize(x);
    program.minimize(y);
    program.check_sat();
    program.get_objectives();

    let output = program.to_string();
    assert!(
        output.contains("(maximize x)"),
        "missing maximize: {output}"
    );
    assert!(
        output.contains("(minimize y)"),
        "missing minimize: {output}"
    );
    assert!(
        output.contains("(get-objectives)"),
        "missing get-objectives: {output}"
    );
}

#[test]
fn test_try_pop_success() {
    let mut program = AYProgram::qf_bv();
    program.push();
    program.push();
    assert_eq!(program.context_level(), 2);
    assert!(program.try_pop(1).is_ok());
    assert_eq!(program.context_level(), 1);
    assert!(program.try_pop(1).is_ok());
    assert_eq!(program.context_level(), 0);
}

#[test]
fn test_try_pop_underflow() {
    let mut program = AYProgram::qf_bv();
    program.push();
    let result = program.try_pop(2);
    assert!(result.is_err());
    let err = result.unwrap_err();
    assert!(
        matches!(
            err,
            SortError::StackUnderflow {
                operation: "pop",
                requested: 2,
                available: 1
            }
        ),
        "error should be StackUnderflow: {err}"
    );
    // Context level should be unchanged after failure
    assert_eq!(program.context_level(), 1);
}
