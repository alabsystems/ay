// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

use ay_dpll::Executor;
use ay_frontend::parse;
use ay_proof::check_proof;
use ntest::timeout;

#[test]
#[timeout(5_000)]
fn test_lia_proof_tracking_check_sat_assuming_records_la_generic_6725() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_LIA)
        (declare-const x Int)
        (check-sat-assuming ((> x 1) (< x 0)))
        (get-proof)
    "#;

    let commands = parse(input).expect("parse input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute input");

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "unsat");

    let proof = exec
        .last_proof()
        .expect("expected last proof after UNSAT with :produce-proofs");
    check_proof(proof, exec.terms()).expect("internal proof checker rejected proof");

    assert!(
        outputs[1].contains(":rule la_generic"),
        "expected la_generic theory lemma in proof:\n{}",
        outputs[1]
    );
    assert!(
        outputs[1].contains(":args (1 1)"),
        "expected unit Farkas coefficients in proof:\n{}",
        outputs[1]
    );
    assert!(
        !outputs[1].contains(":rule trust"),
        "LIA check-sat-assuming proof must not fall back to trust:\n{}",
        outputs[1]
    );
}
