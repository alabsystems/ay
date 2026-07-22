// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression coverage for #9037: proof-enabled early UNSAT exits must still
//! leave `Executor::last_proof()` populated before crossing check-sat boundary.

use ay_dpll::Executor;
use ay_frontend::parse;

fn execute_script(smt: &str) -> (Executor, Vec<String>) {
    let commands = parse(smt).unwrap_or_else(|err| panic!("parse failed: {err}\n{smt}"));
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .unwrap_or_else(|err| panic!("execution failed: {err}\n{smt}"));
    (exec, outputs)
}

fn assert_unsat_with_last_proof(smt: &str) {
    let (exec, outputs) = execute_script(smt);
    assert_eq!(outputs.first().map(String::as_str), Some("unsat"));
    assert!(
        exec.last_proof().is_some(),
        "proof-enabled UNSAT must populate last_proof; outputs={outputs:?}"
    );
}

#[test]
fn qf_s_ground_folded_false_unsat_keeps_proof() {
    assert_unsat_with_last_proof(
        r#"
        (set-option :produce-proofs true)
        (set-logic QF_S)
        (assert (= (str.++ "a" "b") "ac"))
        (check-sat)
        (get-proof)
        "#,
    );
}

#[test]
fn dt_occurs_check_fast_unsat_keeps_proof() {
    assert_unsat_with_last_proof(
        r#"
        (set-option :produce-proofs true)
        (set-logic ALL)
        (declare-datatypes ((List 0)) (((nil) (cons (head Int) (tail List)))))
        (declare-const x List)
        (declare-const n Int)
        (assert (= n 0))
        (assert (= x (cons 0 x)))
        (check-sat)
        (get-proof)
        "#,
    );
}
