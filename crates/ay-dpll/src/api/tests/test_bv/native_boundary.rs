// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Native dense-BV solve-boundary resource-envelope tests.

use super::*;

const FIRST_UNSUPPORTED_NATIVE_BV_WIDTH: u32 = (1 << 20) + 1;

#[test]
fn native_bv_boundary_rejects_unused_nested_declaration_sort() {
    // `declare_const` accepts native Sort values directly. The nested BV never
    // appears below an assertion, but SAT model completion still enumerates
    // declarations, so the symbol-signature scan must catch it.
    let mut solver = Solver::new(Logic::All);
    let nested = Sort::array(
        Sort::Int,
        Sort::seq(Sort::bitvec(FIRST_UNSUPPORTED_NATIVE_BV_WIDTH)),
    );
    let _array = solver.declare_const("oversized_nested_array", nested);

    let result = solver.check_sat();
    assert!(result.is_unknown());
    assert_eq!(solver.unknown_reason(), Some(UnknownReason::Incomplete));
}

#[test]
fn native_bv_boundary_scans_derived_assumption_dag() {
    // Extension can amplify individually-supported one-bit variables past the
    // dense-BV envelope. Only the temporary assumption reaches these terms.
    let mut solver = Solver::new(Logic::All);
    let x = solver.bv_var("small_x", 1);
    let y = solver.bv_var("small_y", 1);
    let wide_x = solver.bvzeroext(x, 1 << 20);
    let wide_y = solver.bvzeroext(y, 1 << 20);
    let assumption = solver.eq(wide_x, wide_y);

    let result = solver.check_sat_assuming(&[assumption]);
    assert!(result.is_unknown());
    assert_eq!(solver.unknown_reason(), Some(UnknownReason::Incomplete));
}

#[test]
fn native_bv_boundary_scans_unused_quantifier_binder_sort() {
    // The bound variable is deliberately absent from the body. Its width lives
    // only in `TermData::Forall` metadata, not in the Bool term/body sorts.
    let mut solver = Solver::new(Logic::All);
    let bound = solver.fresh_var(
        "oversized_bound",
        Sort::bitvec(FIRST_UNSUPPORTED_NATIVE_BV_WIDTH),
    );
    let truth = solver.bool_const(true);
    let quantified = solver.forall(&[bound], truth);
    solver.assert_term(quantified);

    assert!(solver.check_sat().is_unknown());
}

#[test]
fn native_bv_boundary_scans_optimization_objective_dag() {
    // Objective solving bypasses `check_sat_guarded`; preflight its DAG before
    // finite-domain binary search computes 2^width.
    let mut solver = Solver::new(Logic::All);
    let x = solver.int_var("objective_source");
    let oversized = solver.int2bv(x, FIRST_UNSUPPORTED_NATIVE_BV_WIDTH);
    solver.maximize(oversized);

    assert!(solver.optimize_check().is_unknown());
}

#[test]
fn native_bv_boundary_scans_maxsmt_soft_dag_before_scaffolding() {
    // Preflight native soft terms before relaxation/cardinality scaffolding,
    // rather than rediscovering the unsupported width during feasibility.
    let mut solver = Solver::new(Logic::All);
    let x = solver.int_var("soft_source_x");
    let y = solver.int_var("soft_source_y");
    let oversized_x = solver.int2bv(x, FIRST_UNSUPPORTED_NATIVE_BV_WIDTH);
    let oversized_y = solver.int2bv(y, FIRST_UNSUPPORTED_NATIVE_BV_WIDTH);
    let soft = solver.eq(oversized_x, oversized_y);
    solver.assert_soft(soft, 1, None).unwrap();

    let result = solver.check_sat_max().unwrap();
    assert_eq!(result.status, MaxSmtStatus::Unknown);
}
