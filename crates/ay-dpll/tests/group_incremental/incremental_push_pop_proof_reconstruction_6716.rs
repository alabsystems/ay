// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(deprecated)]

use ay_dpll::Executor;
use ay_frontend::parse;
use ay_proof::check_proof;
use ntest::timeout;

fn assert_push_pop_unsat_with_valid_proof(input: &str) {
    let commands = parse(input).expect("SMT-LIB script should parse");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("SMT-LIB script should execute");

    assert_eq!(outputs.len(), 2, "expected check-sat + get-proof output");
    assert_eq!(outputs[0], "unsat", "expected UNSAT result");

    let proof_text = &outputs[1];
    assert!(
        proof_text.contains("(cl)"),
        "expected empty-clause derivation in proof:\n{proof_text}"
    );
    assert!(
        !proof_text.contains(":rule hole"),
        "push/pop proof reconstruction should not fall back to :rule hole:\n{proof_text}"
    );

    let proof = exec
        .last_proof()
        .expect("expected get-proof to populate the last proof object");
    check_proof(proof, exec.terms()).expect("internal proof checker rejected proof");
}

#[test]
#[timeout(5_000)]
fn test_incremental_push_pop_euf_unsat_produces_proof() {
    let input = r#"
        (set-logic QF_UF)
        (set-option :produce-proofs true)
        (declare-sort U 0)
        (declare-fun f (U) U)
        (declare-const a U)
        (declare-const b U)
        (push 1)
        (assert (= a b))
        (assert (not (= (f a) (f b))))
        (check-sat)
        (get-proof)
    "#;

    assert_push_pop_unsat_with_valid_proof(input);
}

#[test]
#[timeout(5_000)]
fn test_incremental_push_pop_lra_unsat_produces_proof() {
    let input = r#"
        (set-logic QF_LRA)
        (set-option :produce-proofs true)
        (declare-const x Real)
        (push 1)
        (assert (> x 1))
        (assert (< x 0))
        (check-sat)
        (get-proof)
    "#;

    assert_push_pop_unsat_with_valid_proof(input);
}
