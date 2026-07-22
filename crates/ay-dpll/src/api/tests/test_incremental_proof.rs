// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for incremental proof certificate quality (#8154).
//!
//! Verifies that `SmtProofCertificate` survives push/pop cycles, that
//! multiple incremental UNSAT queries each produce a certificate, and
//! that SAT-then-UNSAT transitions within pushed scopes behave correctly.

use crate::api::*;

/// Proof certificate survives a push/pop cycle.
///
/// Asserts x > 10 at the base level, pushes, adds x < 5 (UNSAT),
/// verifies the certificate is present, pops, and confirms SAT.
#[test]
fn test_incremental_proof_certificate_survives_push_pop() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);

    // Base: x > 10
    let ten = solver.int_const(10);
    let gt = solver.gt(x, ten);
    solver.assert_term(gt);

    solver.push();

    // Pushed: x < 5 contradicts x > 10
    let five = solver.int_const(5);
    let lt = solver.lt(x, five);
    solver.assert_term(lt);

    let details = solver.check_sat_with_details();
    match details.accept_for_consumer() {
        Ok(SolveResult::Unsat(_cert)) => {
            // Certificate present in pushed scope -- good
        }
        other => panic!("Expected Unsat in pushed scope, got {other:?}"),
    }

    solver.pop();

    // After pop: x > 10 is still SAT
    let result = solver.check_sat();
    assert!(result.is_sat(), "After pop, x > 10 should be SAT");
}

/// Multiple push/pop cycles each produce UNSAT with certificate.
///
/// Uses a pure Boolean contradiction (a AND NOT a) in each pushed scope
/// to avoid theory-specific proof paths.
#[test]
fn test_incremental_proof_multiple_push_pop_cycles() {
    let mut solver = Solver::new(Logic::QfUf);
    let a = solver.declare_const("a", Sort::Bool);
    let not_a = solver.not(a);

    for i in 0..3 {
        solver.push();
        solver.assert_term(a);
        solver.assert_term(not_a);

        let details = solver.check_sat_with_details();
        match details.accept_for_consumer() {
            Ok(SolveResult::Unsat(_)) => {}
            other => panic!("Cycle {i}: expected Unsat, got {other:?}"),
        }
        solver.pop();
    }
}

/// SAT at base, UNSAT in pushed scope.
///
/// Asserts x > 0 (SAT), then pushes x < -5 (contradictory -> UNSAT),
/// verifies the certificate is present, and pops back to SAT.
#[test]
fn test_incremental_sat_then_unsat() {
    let mut solver = Solver::new(Logic::QfLia);
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let gt = solver.gt(x, zero);
    solver.assert_term(gt);

    // Base is SAT
    assert!(solver.check_sat().is_sat(), "x > 0 should be SAT");

    solver.push();

    // Push contradictory: x < -5
    let neg5 = solver.int_const(-5);
    let lt = solver.lt(x, neg5);
    solver.assert_term(lt);

    let details = solver.check_sat_with_details();
    match details.accept_for_consumer() {
        Ok(SolveResult::Unsat(_cert)) => {
            // Certificate present after SAT->UNSAT transition -- good
        }
        other => panic!("Expected Unsat in pushed scope, got {other:?}"),
    }

    solver.pop();

    // After pop: base constraints are SAT again
    assert!(
        solver.check_sat().is_sat(),
        "After pop, x > 0 should be SAT again"
    );
}
