// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

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

#[test]
#[timeout(5_000)]
fn test_incremental_euf_push_pop_congruence_get_proof_6716() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-fun a () U)
        (declare-fun b () U)
        (declare-fun f (U) U)
        (push 1)
        (assert (= a b))
        (assert (not (= (f a) (f b))))
        (check-sat)
        (get-proof)
    "#;

    let commands = parse(input).expect("parse input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute input");

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "unsat");
    assert!(
        !outputs[1].trim().is_empty(),
        "expected non-empty proof text after incremental EUF UNSAT"
    );
    assert_last_unsat_proof_is_valid(&exec);
}

#[test]
#[timeout(5_000)]
fn test_incremental_lra_push_pop_contradiction_get_proof_6716() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_LRA)
        (declare-const x Real)
        (push 1)
        (assert (<= x 5.0))
        (assert (>= x 10.0))
        (check-sat)
        (get-proof)
    "#;

    let commands = parse(input).expect("parse input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute input");

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "unsat");
    assert!(
        !outputs[1].trim().is_empty(),
        "expected non-empty proof text after incremental LRA UNSAT"
    );
    assert_last_unsat_proof_is_valid(&exec);
}
