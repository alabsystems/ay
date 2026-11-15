// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the finite-domain UF SAT certificate
//! (#finite-domain-uf-cert).

use super::*;

fn solved_outputs(script: &str) -> Vec<String> {
    let commands = ay_frontend::parse(script).expect("fixture parses");
    let mut exec = Executor::new();
    exec.set_timeout(Some(std::time::Duration::from_secs(20)));
    exec.execute_all(&commands).expect("fixture solves")
}

/// Functions returning the binder sort put this outside the EPR
/// finite-universe class; the finite-domain certificate must exhibit
/// a model (`g` everything to `b`, `f` everything to `a` works).
const COLLAPSE_SAT: &str = r#"
    (set-logic UF)
    (declare-sort S 0)
    (declare-fun a () S)
    (declare-fun b () S)
    (declare-fun f (S) S)
    (declare-fun g (S) S)
    (assert (forall ((x S)) (= (f (g x)) a)))
    (assert (= (g a) b))
    (assert (not (= a b)))
    (check-sat)
"#;

#[test]
fn finite_domain_uf_publishes_collapse_sat() {
    assert_eq!(solved_outputs(COLLAPSE_SAT), vec!["sat".to_string()]);
}

#[test]
fn finite_domain_uf_never_flips_an_unsat_collapse() {
    // The same collapse with the forced value denied is UNSAT; the
    // grant-only leg (consulted only on Unknown) must not flip it.
    let script = COLLAPSE_SAT.replace("(assert (not (= a b)))", "(assert (not (= (f b) a)))");
    let outputs = solved_outputs(&script);
    assert_ne!(
        outputs.last().map(String::as_str),
        Some("sat"),
        "an unsat collapse must never publish sat: {outputs:?}"
    );
}

#[test]
fn finite_domain_uf_model_validates_through_the_funnel() {
    // The published model must survive an independent re-read: solve
    // with model production and re-evaluate the quantified body at a
    // domain point under the stored model.
    let commands = ay_frontend::parse(COLLAPSE_SAT).expect("fixture parses");
    let mut exec = Executor::new();
    exec.set_best_effort_produce_proofs(1_000_000);
    exec.set_timeout(Some(std::time::Duration::from_secs(20)));
    let outputs = exec.execute_all(&commands).expect("fixture solves");
    assert_eq!(outputs, vec!["sat".to_string()]);
    assert!(exec.last_model_validated);
}
