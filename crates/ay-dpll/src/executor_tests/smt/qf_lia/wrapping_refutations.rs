// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Strict-proof regressions for wrapping arithmetic refutations.

use super::*;

fn assert_wrapping_refutation_has_strict_proof(input: &str) {
    let commands = parse(input).expect("valid wrapping-refutation fixture");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("solver executes");

    assert_eq!(outputs, vec!["unsat"]);
    let proof = exec.last_proof().expect("UNSAT publishes a proof");
    let quality = ay_proof::check_proof_strict(proof, exec.terms())
        .expect("wrapping-refutation UNSAT has a strict proof");
    assert_eq!(
        quality.trust_count, 0,
        "proof must be trust-free: {quality}"
    );
    assert!(
        ay_proof::terminal_trust_report(proof).is_trust_free(),
        "the empty-clause derivation must not depend on trust"
    );
}

/// Regression for the deductive-checks wrapping-refutation family
/// (#wrapping-refutation-t5, `wrapping_refutation_release_identity`): the i32
/// `x.wrapping_add(1).wrapping_sub(1) == x` roundtrip, exactly as the trust
/// compiler's in-process refutation lane asserts it — ONE top-level
/// conjunction root carrying the bounds, two NESTED formula-level wrapping
/// ITEs, and the refuted identity as a negated equality. The exported
/// refutation used to collapse onto a whole-problem `trust` step ("step t5
/// uses unverified trust rule") and mandatory strict certification published
/// `unknown`; the conjunction/nested-ITE/`la_disequality` seeding in
/// `rebuild_arith_ite_case_split_farkas` rebuilds the honest case-split proof.
#[test]
fn wrapping_roundtrip_signed_nested_ite_conjunction_has_strict_proof() {
    assert_wrapping_refutation_has_strict_proof(
        r#"
        (set-option :produce-proofs true)
        (set-option :produce-unsat-cores true)
        (set-logic ALL)
        (declare-const r Int)
        (declare-const s Int)
        (declare-const x Int)
        (assert (! (and
            (<= (- 2147483648) x) (<= x 2147483647)
            (ite (< 2147483647 (+ s (- 1)))
                 (= r (+ s (- 4294967297)))
                 (ite (< (+ s (- 1)) (- 2147483648))
                      (= r (+ s 4294967295))
                      (= r (+ s (- 1)))))
            (<= (- 2147483648) s) (<= s 2147483647)
            (ite (< 2147483647 (+ x 1))
                 (= s (+ x (- 4294967295)))
                 (ite (< (+ x 1) (- 2147483648))
                      (= s (+ x 4294967297))
                      (= s (+ x 1))))
            (not (= r x))) :named dn0))
        (check-sat)
    "#,
    );
}

/// The unsigned sibling (`usize` roundtrip): single-level wrapping ITEs under
/// the same conjunction root, with a symbolic wrap distance `n`. Exercises the
/// conjunction flattening and the `la_disequality` split without ITE nesting.
#[test]
fn wrapping_roundtrip_unsigned_ite_conjunction_has_strict_proof() {
    assert_wrapping_refutation_has_strict_proof(
        r#"
        (set-option :produce-proofs true)
        (set-option :produce-unsat-cores true)
        (set-logic ALL)
        (declare-const x Int)
        (declare-const n Int)
        (declare-const s Int)
        (declare-const r Int)
        (assert (! (and
            (<= 0 x) (<= x 18446744073709551615)
            (<= 0 n) (<= n 18446744073709551615)
            (ite (< (+ s (- n)) 0)
                 (= r (+ s (- n) 18446744073709551616))
                 (= r (+ s (- n))))
            (<= 0 s) (<= s 18446744073709551615)
            (ite (<= 18446744073709551616 (+ x n))
                 (= s (+ x n (- 18446744073709551616)))
                 (= s (+ x n)))
            (not (= r x))) :named dn0))
        (check-sat)
    "#,
    );
}
