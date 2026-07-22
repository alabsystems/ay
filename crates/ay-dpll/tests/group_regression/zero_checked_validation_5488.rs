// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Regression test for #5488: validate_model accepts SAT when all assertions
//! are skipped (zero-checked pass-through to consumers).
//!
//! When all assertions fall into skip categories (e.g., DT+BV combined), the
//! model validator must degrade to Unknown rather than report SAT with zero
//! validation evidence.
//!
//! IMPORTANT: The `execute_all` path (used by the SMT-LIB text interface) calls
//! `check_sat_internal` directly, which only runs a single validation pass with
//! DT axioms present. The zero-check guard only fires in the `Executor::check_sat`
//! public method, which runs a second validation after DT axioms are truncated.
//! Tests that use `execute_all` can never trigger the guard — they must use the
//! programmatic `Solver` API to exercise the double-validation path.

#![allow(deprecated)]

use ay_dpll::api::BitVecSort;
use ay_dpll::{
    ApiSolver as Solver, ApiSort as Sort, DatatypeConstructor, DatatypeField, DatatypeSort, Logic,
    SolveResult,
};
use ntest::timeout;

/// DT+BV combined problem via the execute path (single validation with DT
/// axioms present). The user assertion hits DT+BV skip, but internal DT axioms
/// (is-mk-wrapper, selector axiom) provide checked > 0. Result is SAT because
/// the execute path only validates once, with DT axioms present.
#[test]
#[timeout(60_000)]
fn test_dtbv_execute_path_returns_sat() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatype Wrapper ((mk-wrapper (val (_ BitVec 8)))))
        (declare-fun x () Wrapper)
        (assert (bvult (val x) #x02))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    let result_trimmed = result.trim();
    // Execute path: single validation with DT axioms → checked > 0 → SAT.
    assert_eq!(
        result_trimmed, "sat",
        "Execute path for DT+BV should return sat (single validation with DT axioms), got: {result_trimmed}"
    );
}

/// DT+BV combined problem via the programmatic Solver API.
/// After DT axiom truncation, user assertions are DT+BV combined.
/// The model validator uses SAT-model evidence for DT+BV assertions (#5689):
/// BV bitblasting is sound and complete, so SAT-model evidence counts as
/// independent theory-level validation. Result: SAT.
///
/// History: before #5689 fix, this returned Unknown because the zero-check
/// guard treated all DT+BV assertions as unchecked skips. The fix counts
/// SAT-verified DT+BV assertions as checked (BV provides independent evidence).
#[test]
#[timeout(60_000)]
fn test_dtbv_solver_api_returns_sat() {
    let mut solver = Solver::new(Logic::All);

    let wrapper = DatatypeSort {
        name: "Wrapper".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "mk-wrapper".to_string(),
            fields: vec![DatatypeField {
                name: "val".to_string(),
                sort: Sort::BitVec(BitVecSort { width: 8 }),
            }],
        }],
    };
    solver.declare_datatype(&wrapper);

    let x = solver.declare_const("x", Sort::Datatype(wrapper.clone()));
    let val_x = solver.datatype_selector("val", x, Sort::BitVec(BitVecSort { width: 8 }));
    let two = solver.bv_const(2, 8);
    let bvult = solver.bvult(val_x, two);
    solver.assert_term(bvult);

    let result = solver.check_sat();

    // DT+BV assertions are verified via SAT-model evidence (#5689).
    // BV bitblasting is sound and complete, so SAT-model true means the
    // assertion is satisfied by the model.
    assert_eq!(
        result,
        SolveResult::Sat,
        "Solver API for DT+BV should return Sat (SAT-model evidence for BV-complete theory), got: {result:?}"
    );
}

/// Multiple DT+BV assertions via execute path. Same reasoning: execute path
/// validates once with DT axioms present → checked > 0 → SAT.
#[test]
#[timeout(60_000)]
fn test_dtbv_multiple_assertions_execute_path_returns_sat() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatype Pair ((mk-pair (fst (_ BitVec 8)) (snd (_ BitVec 8)))))
        (declare-fun p () Pair)
        (assert (bvult (fst p) #x80))
        (assert (bvugt (snd p) #x10))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    let result_trimmed = result.trim();
    assert_eq!(
        result_trimmed, "sat",
        "Execute path for multiple DT+BV should return sat, got: {result_trimmed}"
    );
}

/// Mixed problem: one assertion is pure DT (evaluable), one is DT+BV (skipped).
/// Execute path validates once with DT axioms → checked >= 1 → SAT.
#[test]
#[timeout(60_000)]
fn test_dtbv_mixed_evaluable_and_skipped_execute_path_returns_sat() {
    let smt = r#"
        (set-logic ALL)
        (declare-datatype Color ((Red) (Green) (Blue)))
        (declare-datatype Wrapper ((mk-wrapper (val (_ BitVec 8)))))
        (declare-fun c () Color)
        (declare-fun w () Wrapper)
        (assert (= c Red))
        (assert (bvult (val w) #x80))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    let result_trimmed = result.trim();
    assert_eq!(
        result_trimmed, "sat",
        "Execute path for mixed DT + DT+BV should return sat, got: {result_trimmed}"
    );
}

/// Canary: verify the zero-check guard exists in source.
#[test]
fn test_zero_check_guard_exists_in_source() {
    let source = include_str!("../../src/executor/model/validation/pipeline.rs");
    assert!(
        source.contains("stats.checked == 0") && source.contains("skipped_dtbv > 0"),
        "BUG #5488: zero-check guard missing from validate_model()"
    );
    assert!(
        source.contains("ModelValidationError::incomplete"),
        "BUG #5488: typed incomplete error missing from validate_model()"
    );
}
