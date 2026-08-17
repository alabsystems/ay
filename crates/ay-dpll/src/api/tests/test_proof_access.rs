// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! API-level proof access tests (#4412).
//!
//! Verifies that `api::Solver` correctly forwards proof controls to the
//! underlying `Executor` and that the proof lifecycle (enabled, disabled,
//! clear-on-solve) matches executor semantics.
//!
//! Uses pure Boolean contradictions (p AND NOT p) to avoid triggering the
//! proof rewrite path, which requires `assertions_parsed` parity that the
//! Rust API does not maintain (pre-existing gap in `proof_rewrite.rs:41`).

use crate::api::*;

/// Enable proofs, assert a Boolean contradiction, check UNSAT, verify proof is present.
#[test]
fn proof_enabled_unsat_exposes_proof() {
    let mut solver = Solver::new(Logic::QfUf);
    solver.set_produce_proofs(true);
    assert!(solver.is_producing_proofs());

    // p AND NOT p — trivial Boolean contradiction.
    let p = solver.declare_const("p", Sort::Bool);
    let not_p = solver.not(p);
    solver.assert_term(p);
    solver.assert_term(not_p);

    assert!(solver.check_sat().is_unsat());
    assert!(
        solver.last_proof().is_some(),
        "proof must be available after UNSAT with produce-proofs enabled"
    );
    solver.set_produce_proofs(false);
    assert!(
        solver.last_proof().is_some(),
        "solve-time request must persist"
    );
    assert!(solver.export_last_proof_alethe().is_some());
}

/// Keep proofs disabled, assert a contradiction, verify proof is None.
#[test]
fn proof_disabled_unsat_returns_none() {
    let mut solver = Solver::new(Logic::QfUf);
    // Proofs are disabled by default.
    assert!(!solver.is_producing_proofs());

    let p = solver.declare_const("p", Sort::Bool);
    let not_p = solver.not(p);
    solver.assert_term(p);
    solver.assert_term(not_p);

    assert!(solver.check_sat().is_unsat());
    assert!(
        solver.last_proof().is_none(),
        "proof must be None when produce-proofs is disabled"
    );
}

#[test]
fn later_proof_requests_do_not_expose_unrequested_solve() {
    let mut solver = Solver::new(Logic::QfUf);
    let p = solver.declare_const("p", Sort::Bool);
    let not_p = solver.not(p);
    solver.assert_term(p);
    solver.assert_term(not_p);

    assert!(solver.check_sat().is_unsat());
    assert!(solver.last_proof().is_none());
    assert!(solver.export_last_proof_alethe().is_none());

    solver.set_verification_level(VerificationLevel::ProofChecked);
    solver.set_produce_proofs(true);
    assert!(solver.last_proof().is_none());
    assert!(solver.export_last_proof_alethe().is_none());
}

/// First UNSAT with proof, then SAT — proof must be cleared.
///
/// Verifies the executor's clear-on-solve semantics: `last_proof` is reset
/// at the start of each `check_sat` call.
#[test]
fn proof_cleared_after_followup_sat() {
    let mut solver = Solver::new(Logic::QfUf);
    solver.set_produce_proofs(true);

    // First query: UNSAT (p AND NOT p).
    let p = solver.declare_const("p", Sort::Bool);
    let not_p = solver.not(p);
    solver.assert_term(p);
    solver.assert_term(not_p);
    assert!(solver.check_sat().is_unsat());
    assert!(solver.last_proof().is_some(), "proof present after UNSAT");

    // Reset and make a SAT query (q = true is satisfiable).
    solver.reset();
    solver.set_produce_proofs(true);
    let q = solver.declare_const("q", Sort::Bool);
    solver.assert_term(q);
    assert_eq!(solver.check_sat(), SolveResult::Sat);

    // Proof must be cleared after the SAT result.
    assert!(
        solver.last_proof().is_none(),
        "proof must be None after a SAT result (clear-on-solve semantics)"
    );
}
