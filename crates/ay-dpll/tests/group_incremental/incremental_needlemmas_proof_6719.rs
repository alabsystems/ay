// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_dpll::Executor;
use ay_frontend::parse;
use ay_proof::check_proof_with_quality;
use ntest::timeout;

#[test]
#[timeout(5_000)]
fn test_qf_ax_needlemmas_unsat_proof_retains_theory_lemma_6719() {
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_AX)
        (declare-const a (Array Int Int))
        (declare-const b (Array Int Int))
        (declare-const i Int)
        (declare-const j Int)
        (declare-const v Int)
        (assert (= b (store a i v)))
        (assert (not (= i j)))
        (assert (not (= (select b j) (select a j))))
        (check-sat)
        (get-proof)
    "#;

    let commands = parse(input).expect("parse proof-enabled QF_AX NeedLemmas repro");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("execute proof-enabled QF_AX NeedLemmas repro");

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "unsat");

    let proof = exec
        .last_proof()
        .expect("expected proof after proof-enabled NeedLemmas UNSAT");
    let quality = check_proof_with_quality(proof, exec.terms())
        .expect("internal proof checker rejected NeedLemmas proof");

    assert!(
        quality.theory_lemma_count > 0,
        "expected ROW2 NeedLemmas proof to retain a TheoryLemma step: {quality:?}"
    );
    assert_eq!(
        quality.hole_count, 0,
        "ROW2 NeedLemmas proof should not contain hole steps: {quality:?}"
    );
}
