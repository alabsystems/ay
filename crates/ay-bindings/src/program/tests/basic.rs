// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

use crate::constraint::logic;
use crate::expr::Expr;
use crate::program::{AYProgram, ProgramBuilder};
use crate::sort::Sort;

#[test]
fn test_basic_program() {
    let mut program = AYProgram::qf_bv();

    let x = program.declare_const("x", Sort::bv32());
    let y = program.declare_const("y", Sort::bv32());

    let sum = x.bvadd(y);
    let ten = Expr::bitvec_const(10i32, 32);
    program.assert(sum.eq(ten));

    program.check_sat();

    let output = program.to_string();
    assert!(output.contains("(set-logic QF_BV)"));
    assert!(output.contains("(declare-const x (_ BitVec 32))"));
    assert!(output.contains("(declare-const y (_ BitVec 32))"));
    assert!(output.contains("(check-sat)"));
}

#[test]
fn test_push_pop() {
    let mut program = AYProgram::qf_bv();

    let x = program.declare_const("x", Sort::bv32());

    program.push();
    assert_eq!(program.context_level(), 1);

    program.assert(x.clone().eq(Expr::bitvec_const(1i32, 32)));
    program.check_sat();

    program.pop(1);
    assert_eq!(program.context_level(), 0);

    program.assert(x.eq(Expr::bitvec_const(2i32, 32)));
    program.check_sat();
}

#[test]
fn test_assume() {
    // assume() is a semantic alias for assert() - same SMT-LIB output
    let mut program = AYProgram::qf_bv();
    let x = program.declare_const("x", Sort::bv32());
    let zero = Expr::bitvec_const(0i32, 32);
    program.assume(x.bvugt(zero));
    program.check_sat();

    let output = program.to_string();
    assert!(output.contains("(assert (bvugt x #x00000000))"));
}

#[test]
fn test_assume_labeled() {
    // assume_labeled() is a semantic alias for assert_labeled()
    let mut program = AYProgram::qf_bv();
    let x = program.declare_const("x", Sort::bv32());
    let zero = Expr::bitvec_const(0i32, 32);
    program.assume_labeled(x.bvugt(zero), "positive_constraint");
    program.check_sat();

    let output = program.to_string();
    assert!(output.contains("(assert (! (bvugt x #x00000000) :named positive_constraint))"));
}

#[test]
fn test_builder() {
    let program = ProgramBuilder::new()
        .logic(logic::QF_BV)
        .with_models()
        .build();

    let output = program.to_string();
    assert!(output.contains("produce-models"));
    assert!(output.contains("QF_BV"));
}

#[test]
fn test_is_declared() {
    let mut program = AYProgram::new();
    assert!(!program.is_declared("x"));

    let _ = program.declare_const("x", Sort::bv32());
    assert!(program.is_declared("x"));
    assert!(!program.is_declared("y"));
}

#[test]
fn test_define_fun_program_output_and_clear_commands() {
    let mut program = AYProgram::qf_lia();
    let n = Expr::var("n", Sort::int());
    program.define_fun(
        "inc",
        vec![("n".to_string(), Sort::int())],
        n.int_add(Expr::int(1)),
    );
    let x = program.declare_const("x", Sort::int());
    program.assert(Expr::func_app_with_sort("inc", vec![x], Sort::int()).eq(Expr::int(5)));

    let output = program.to_string();
    assert!(output.contains("(define-fun inc ((n Int)) Int (+ n 1))"));
    assert!(output.contains("(assert (= (inc x) 5))"));

    program.clear_commands();
    let reset_output = program.to_string();
    assert!(reset_output.contains("(define-fun inc ((n Int)) Int (+ n 1))"));
    assert!(!reset_output.contains("(assert (= (inc x) 5))"));
}

// ===== Fallible try_assert / try_assert_labeled (#3543) =====

#[test]
fn test_try_assert_bool_succeeds() {
    let mut program = AYProgram::qf_bv();
    let x = program.declare_const("x", Sort::bv32());
    let zero = Expr::bitvec_const(0i32, 32);
    let result = program.try_assert(x.bvugt(zero));
    assert!(result.is_ok(), "Bool expression should succeed: {result:?}");
}

#[test]
fn test_try_assert_non_bool_fails() {
    use crate::error::SortError;

    let mut program = AYProgram::qf_bv();
    let x = program.declare_const("x", Sort::bv32());
    let result = program.try_assert(x);
    assert!(result.is_err(), "non-Bool expression should fail");
    let err = result.unwrap_err();
    assert!(
        matches!(
            err,
            SortError::Mismatch {
                operation: "assert",
                ..
            }
        ),
        "expected SortError::Mismatch for assert, got {err:?}"
    );
}

#[test]
fn test_try_assert_labeled_bool_succeeds() {
    let mut program = AYProgram::qf_bv();
    let x = program.declare_const("x", Sort::bv32());
    let zero = Expr::bitvec_const(0i32, 32);
    let result = program.try_assert_labeled(x.bvugt(zero), "positive");
    assert!(result.is_ok(), "Bool expression should succeed: {result:?}");
}

#[test]
fn test_try_assert_labeled_non_bool_fails() {
    use crate::error::SortError;

    let mut program = AYProgram::qf_bv();
    let x = program.declare_const("x", Sort::bv32());
    let result = program.try_assert_labeled(x, "label");
    assert!(result.is_err(), "non-Bool expression should fail");
    let err = result.unwrap_err();
    assert!(
        matches!(
            err,
            SortError::Mismatch {
                operation: "assert_labeled",
                ..
            }
        ),
        "expected SortError::Mismatch for assert_labeled, got {err:?}"
    );
}
