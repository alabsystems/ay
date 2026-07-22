// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Integration test for the `ay::api` facade module (#564).
//!
//! Verifies that all consumer-facing types are accessible through
//! a single `ay::api` import path, matching the surface that
//! downstream crates (downstream verification consumers) currently fetch
//! from `ay_dpll::api`.

// This test uses deprecated panicking convenience methods for brevity.
#![allow(deprecated)]

use ay::api::{
    ArraySort, BitVecSort, DatatypeConstructor, DatatypeField, DatatypeSort, Logic, SolveResult,
    Solver, Sort,
};

fn assert_public_type<T>() {}

#[test]
fn test_api_facade_reexports_consumer_surface() {
    // Verify helper types are re-exported through ay::api
    assert_public_type::<ArraySort>();
    assert_public_type::<BitVecSort>();
    assert_public_type::<DatatypeConstructor>();
    assert_public_type::<DatatypeField>();
    assert_public_type::<DatatypeSort>();
    assert_public_type::<SolveResult>();

    // Smoke test: solve a trivial QF_LIA problem through the facade
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let ten = solver.int_const(10);
    let c1 = solver.gt(x, zero);
    solver.assert_term(c1);
    let c2 = solver.lt(x, ten);
    solver.assert_term(c2);

    let result = solver.check_sat();
    assert!(
        result.result().is_sat(),
        "expected SAT for 0 < x < 10, got {:?}",
        result.result()
    );

    // Model extraction through the facade path
    let model = solver.model().expect("SAT result should have model");
    let x_val = model
        .model()
        .int_val_i64("x")
        .expect("model should contain x");
    assert!(x_val > 0 && x_val < 10, "x={x_val} should be in (0, 10)");
}

#[test]
fn test_api_facade_solver_types() {
    // Verify solver/result/model types are accessible
    use ay::api::{
        CounterexampleStyle, FpSpecialKind, FuncDecl, Model, ModelValue, SolveDetails, SolverError,
        Statistics, Term, TermId, TermKind, UnknownReason, VerificationLevel, VerificationSummary,
        VerifiedModel, VerifiedSolveResult,
    };

    assert_public_type::<CounterexampleStyle>();
    assert_public_type::<FpSpecialKind>();
    assert_public_type::<FuncDecl>();
    assert_public_type::<Model>();
    assert_public_type::<ModelValue>();
    assert_public_type::<SolveDetails>();
    assert_public_type::<SolverError>();
    assert_public_type::<Statistics>();
    assert_public_type::<Term>();
    assert_public_type::<TermId>();
    assert_public_type::<TermKind>();
    assert_public_type::<UnknownReason>();
    assert_public_type::<VerificationLevel>();
    assert_public_type::<VerificationSummary>();
    assert_public_type::<VerifiedModel>();
    assert_public_type::<VerifiedSolveResult>();
}

#[test]
fn test_api_facade_sort_ext_trait() {
    use ay::api::SortExt;

    // SortExt provides to_command_sort() for DeclareFun integration
    let int_sort = Sort::Int;
    let _cmd_sort = int_sort.to_command_sort();

    // Sort constructors for compound sorts
    let _array = Sort::Array(Box::new(ArraySort::new(Sort::Int, Sort::Bool)));
    let _bv = Sort::BitVec(BitVecSort::new(32));
}
