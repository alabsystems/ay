// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #ppp-l3 red→green: the AUFLIA `FlattenAnd`+`PropagateValues` fixpoint now
//! mints producer provenance and the strict certification funnel replays it.
//!
//! Each test drives an authored QF_AUFLIA problem whose refutation depends on
//! a propagation-rewritten assertion. Before L3 the rewritten assume had no
//! authority (record store empty on this route) and the published certificate
//! leaned on trust; with L3 the replay derives it from the authored roots and
//! the UNTOUCHED strict checker accepts a trust-free proof.

use super::*;

fn assert_unsat_with_strict_trust_free_proof(input: &str) {
    let commands = parse(input).expect("valid QF_AUFLIA fixture");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("solver executes");
    assert_eq!(outputs, vec!["unsat"]);
    let proof = exec.last_proof().expect("UNSAT publishes a proof");
    let quality = ay_proof::check_proof_strict(proof, exec.terms())
        .expect("the propagation-rewritten refutation must have a strict proof");
    assert_eq!(
        quality.trust_count, 0,
        "proof must be trust-free: {quality}"
    );
}

/// A ground UF value equality `(= (f 0) 1)` licenses the rewrite
/// `(> (select a (f 0)) 5) -> (> (select a 1) 5)`; the rewritten assume is
/// derived from its authored root through the replayed record.
#[test]
fn auflia_propagated_uf_value_rewrite_has_strict_certificate() {
    assert_unsat_with_strict_trust_free_proof(
        r#"
        (set-option :produce-proofs true)
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-fun f (Int) Int)
        (assert (= (f 0) 1))
        (assert (> (select a (f 0)) 5))
        (assert (< (select a 1) 3))
        (check-sat)
    "#,
    );
}

/// The Bool `(= x true)` fold (#ppp-l3 replay extension): substituting
/// `(f 0) -> 1` folds `(<= (f 0) 2)` to `true` and the Boolean equality
/// `(= r (<= (f 0) 2))` collapses to the bare atom `r`, whose assume the
/// replay derives from the authored biconditional plus the defining
/// equality. At the L3 baseline this exact fixture deferred `(cl r)` as an
/// undischargeable trust step ("original clause has no exact proof
/// authority") and the certificate carried a hole.
#[test]
fn auflia_propagated_bool_eq_fold_has_strict_certificate() {
    assert_unsat_with_strict_trust_free_proof(
        r#"
        (set-option :produce-proofs true)
        (set-logic QF_AUFLIA)
        (declare-const a (Array Int Int))
        (declare-fun f (Int) Int)
        (declare-const r Bool)
        (assert (= (f 0) 1))
        (assert (= r (<= (f 0) 2)))
        (assert (=> r (> (select a 1) 5)))
        (assert (< (select a 1) 3))
        (check-sat)
    "#,
    );
}
