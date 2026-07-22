// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for #6725: split-loop incremental UNSAT proof recording.
//!
//! Before this fix, split-loop UNSAT paths (QF_LIA, QF_LRA, combined theories)
//! degraded to `:rule trust` because:
//! - Gap A: EUF conflicts had no `record_theory_conflict_unsat()` call
//! - Gap B: `BlockingClauseResult::Unsat` exited without stashing proof metadata

#![allow(deprecated)]

use ay_dpll::Executor;
use ay_frontend::parse;
use ay_proof::check_proof;
use ntest::timeout;

fn assert_last_unsat_proof_is_valid(exec: &Executor) {
    let proof = exec
        .last_proof()
        .expect("expected last proof after UNSAT with :produce-proofs");
    check_proof(proof, exec.terms())
        .expect("internal proof checker rejected proof for UNSAT result");
}

/// QF_LIA push/pop contradiction must produce a valid proof without trust fallback.
/// This exercises the split-loop path (`solve_incremental_split_loop_pipeline!`
/// via `solve_lia`). Before #6725, this produced `:rule trust` instead of
/// structured theory lemma steps.
#[test]
#[timeout(5_000)]
fn test_split_loop_lia_push_pop_proof_no_trust_6725() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_LIA)
        (declare-const x Int)
        (push 1)
        (assert (> x 1))
        (assert (< x 0))
        (check-sat)
        (get-proof)
    "#;

    let commands = parse(input).expect("parse input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute input");

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "unsat");

    let proof_text = &outputs[1];
    assert!(
        !proof_text.trim().is_empty(),
        "expected non-empty proof text after QF_LIA UNSAT"
    );

    // The proof must not degrade to `:rule trust` for the theory conflict.
    // Before #6725, the split-loop path produced a trust step instead of a
    // structured la_generic or theory_lemma step.
    assert!(
        !proof_text.contains(":rule trust"),
        "split-loop QF_LIA UNSAT proof must not degrade to :rule trust:\n{proof_text}"
    );

    assert_last_unsat_proof_is_valid(&exec);
}

/// QF_LIA push/pop with two scopes: each UNSAT must have a valid proof.
/// Exercises split-loop proof metadata stashing across pop boundaries.
#[test]
#[timeout(5_000)]
fn test_split_loop_lia_two_scopes_proof_6725() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_LIA)
        (declare-const x Int)
        (declare-const y Int)
        (push 1)
        (assert (> x 10))
        (assert (< x 5))
        (check-sat)
        (get-proof)
        (pop 1)
        (push 1)
        (assert (> y 20))
        (assert (< y 15))
        (check-sat)
        (get-proof)
    "#;

    let commands = parse(input).expect("parse input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute input");

    // check-sat1, get-proof1, check-sat2, get-proof2
    assert_eq!(outputs.len(), 4);
    assert_eq!(outputs[0], "unsat", "first check-sat should be UNSAT");
    assert_eq!(outputs[2], "unsat", "second check-sat should be UNSAT");

    let proof_1 = &outputs[1];
    let proof_2 = &outputs[3];

    // Neither proof should degrade to trust
    assert!(
        !proof_1.contains(":rule trust"),
        "first scope proof must not use trust:\n{proof_1}"
    );
    assert!(
        !proof_2.contains(":rule trust"),
        "second scope proof must not use trust:\n{proof_2}"
    );

    // Second proof must not reference x from the popped scope
    assert!(
        !proof_2.contains("(> x"),
        "second proof must not reference x from popped scope:\n{proof_2}"
    );

    assert_last_unsat_proof_is_valid(&exec);
}
