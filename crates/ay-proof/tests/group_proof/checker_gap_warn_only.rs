// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// Behavior contracts for proof checker deployment hardening (#4393):
// 1. Partial checker validates non-hole steps and reports hole coverage counts.
// 2. Invalid non-hole derivations are still rejected in partial mode.
// 3. Standard checker keeps trust permissive; strict mode rejects trust.
//
// See sat-debuggability epic #4172.

use ay_core::{AletheRule, Proof, ProofStep, Sort, TermStore};
use ay_proof::{check_proof, check_proof_partial, check_proof_strict, ProofCheckError};

#[test]
fn test_partial_checker_validates_non_hole_subset() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let not_x = terms.mk_not(x);

    let mut proof = Proof::new();
    let h0 = proof.add_assume(x, None);
    let hole = proof.add_step(ProofStep::Step {
        rule: AletheRule::Hole,
        clause: vec![not_x],
        premises: vec![],
        args: vec![],
    });
    proof.add_resolution(vec![], x, hole, h0);

    let (partial, err) = check_proof_partial(&proof, &terms);
    assert!(
        err.is_none(),
        "partial checker should validate mixed hole/non-hole proof: {err:?}"
    );
    assert_eq!(partial.total_steps, 3);
    assert_eq!(partial.checked_steps, 2);
    assert_eq!(partial.skipped_hole_steps, 1);
}

#[test]
fn test_partial_checker_rejects_invalid_non_hole_resolution() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let y = terms.mk_var("y", Sort::Bool);
    let not_x = terms.mk_not(x);

    let mut proof = Proof::new();
    let h0 = proof.add_assume(x, None);
    let h1 = proof.add_assume(not_x, None);
    // Invalid: x and ¬x resolve to empty, not {y}.
    proof.add_step(ProofStep::Resolution {
        clause: vec![y],
        pivot: x,
        clause1: h0,
        clause2: h1,
    });

    let (_partial, err) = check_proof_partial(&proof, &terms);
    let err = err.expect("partial checker must reject invalid non-hole resolution");
    assert!(
        matches!(err, ProofCheckError::InvalidResolution { .. }),
        "expected InvalidResolution, got: {err:?}"
    );
}

#[test]
fn test_standard_checker_accepts_trust_but_strict_rejects_it() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let not_x = terms.mk_not(x);

    let mut proof = Proof::new();
    let h0 = proof.add_assume(x, None);
    let trust = proof.add_step(ProofStep::Step {
        rule: AletheRule::Trust,
        clause: vec![not_x],
        premises: vec![],
        args: vec![],
    });
    proof.add_resolution(vec![], x, trust, h0);

    check_proof(&proof, &terms).expect("standard checker accepts trust steps by design");
    check_proof_strict(&proof, &terms).expect_err("strict checker must reject trust steps");
}
