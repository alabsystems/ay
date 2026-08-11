// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;

const FORALL_GROUND_EQUALITY_CONFLICT: &str = r#"
    (set-option :produce-proofs true)
    (set-option :check-proofs-strict true)
    (set-logic AUFLIA)
    (declare-fun f (Int) Int)
    (assert (forall ((x Int)) (! (> (f x) 0) :pattern ((f x)))))
    (assert (= (f 7) (- 1)))
    (check-sat)
    (get-proof)
"#;

/// Variable substitution folds the arithmetic conflict into a provisional
/// `(not forall)` unit.  The exported proof must reconstruct that unit from
/// the authenticated E-matching instance and the original equality, never a
/// `Generic`/trust leaf.
#[test]
#[timeout(10_000)]
fn direct_ematching_instance_rebuilds_forall_farkas_conflict_without_trust() {
    let commands = parse(FORALL_GROUND_EQUALITY_CONFLICT).expect("parse AUFLIA regression");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("solve AUFLIA regression");
    assert_eq!(outputs.first().map(String::as_str), Some("unsat"));

    let proof = exec.last_proof().expect("strict UNSAT proof");
    let quality = ay_proof::check_proof_strict(proof, exec.terms())
        .expect("E-matching/Farkas reconstruction must pass the strict checker");
    assert_eq!(quality.trust_count, 0);
    assert!(ay_proof::terminal_trust_report(proof).is_trust_free());

    let rendered = outputs.last().expect("get-proof output");
    assert!(rendered.contains(":rule forall_inst"), "{rendered}");
    assert!(rendered.contains(":rule la_generic"), "{rendered}");
    assert!(!rendered.contains(":rule trust"), "{rendered}");
}
