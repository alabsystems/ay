// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

/// The loop-exit obligation `i <= n && !(i < n) => i = n` needs a
/// trichotomy lemma, not an unprintable arithmetic tautology. Keep strict
/// admission enabled: native checking and the Alethe wire must both succeed.
#[test]
fn loop_exit_equality_has_a_strict_hole_free_trichotomy_proof() {
    let input = r#"
        (set-logic QF_LIA)
        (set-option :produce-proofs true)
        (set-option :check-proofs-strict true)
        (declare-const i Int)
        (declare-const n Int)
        (assert (and (>= i 0) (<= i n)))
        (assert (not (< i n)))
        (assert (not (= i n)))
        (check-sat)
    "#;
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&parse(input).expect("parse loop exit"))
        .expect("execute loop exit");
    if outputs[0] != "unsat" {
        // Diagnose the producer without changing the assertion below: strict
        // rejection remains a regression even when the native-only solve is
        // able to retain its candidate for inspection.
        let mut diagnostic = Executor::new();
        let unchecked = input.replace(":check-proofs-strict true", ":check-proofs-strict false");
        let _ = diagnostic.execute_all(&parse(&unchecked).expect("parse diagnostic replay"));
        panic!(
            "strict output: {outputs:?}; producer proof: {:#?}",
            diagnostic.last_proof
        );
    }
    assert_eq!(
        outputs[0], "unsat",
        "retained proof: {:#?}",
        exec.last_proof
    );
    let printed = exec
        .execute_all(&parse("(get-proof)").expect("parse proof request"))
        .expect("export checked proof");
    let wire = &printed[0];
    assert!(wire.contains(":rule la_disequality"), "{wire}");
    assert!(
        !wire.contains(":rule hole") && !wire.contains(":rule trust"),
        "{wire}"
    );
    let proof = exec.last_proof.as_ref().expect("strict proof retained");
    assert!(exec
        .check_proof_strict_with_datatypes(proof)
        .is_ok_and(|quality| quality.is_complete()));
    assert!(!exec.proof_has_known_wire_gap(proof));
}

/// Without the upper bound the same disequality has a model (i > n).
#[test]
fn loop_exit_equality_without_upper_bound_is_satisfiable() {
    let input = r#"
        (set-logic QF_LIA)
        (set-option :produce-proofs true)
        (set-option :check-proofs-strict true)
        (declare-const i Int)
        (declare-const n Int)
        (assert (>= i 0))
        (assert (not (< i n)))
        (assert (not (= i n)))
        (check-sat)
    "#;
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&parse(input).expect("parse negative twin"))
        .expect("execute negative twin");
    assert_eq!(outputs[0], "sat");
}
