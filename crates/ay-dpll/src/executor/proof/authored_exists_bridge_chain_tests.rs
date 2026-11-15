// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the exists-bridge chain translation (#exists-bridge-chain).

use super::*;

fn executor_with_assertions(script: &str) -> Executor {
    let commands = ay_frontend::parse(script).expect("bridge fixture parses");
    let mut exec = Executor::new();
    assert!(
        exec.execute_all(&commands)
            .expect("bridge fixture loads")
            .is_empty(),
        "fixture must contain declarations and assertions only"
    );
    exec
}

/// The bridge shape in miniature: `P a` authored, the bridge turns it
/// into an existential witness with `Q`, and the closing universal
/// turns `Q` into the denied equality.
const BRIDGE_MINIMIZER: &str = r#"
    (set-logic UF)
    (declare-sort S 0)
    (declare-fun a () S)
    (declare-fun b () S)
    (declare-fun P (S) Bool)
    (declare-fun Q (S) Bool)
    (assert (P a))
    (assert (forall ((x S)) (= (P x) (exists ((y S)) (and (= y x) (Q y))))))
    (assert (forall ((y S)) (=> (Q y) (= a b))))
    (assert (not (= a b)))
"#;

#[test]
fn bridge_minimizer_translates_to_a_strict_proof() {
    let mut exec = executor_with_assertions(BRIDGE_MINIMIZER);
    exec.begin_public_solve(false);
    exec.bind_unsat_query_assumptions(&[]);
    assert!(
        exec.try_translate_exists_bridge_chain_unsat(),
        "bridge at a, skolem witness, closing at the witness refutes"
    );
    let proof = exec
        .last_proof
        .clone()
        .expect("translation installs last_proof");
    assert!(proof.steps.iter().any(|step| matches!(
        step,
        ProofStep::Step {
            rule: AletheRule::Skolem,
            ..
        }
    )));
    assert!(exec
        .check_proof_strict_with_datatypes(&proof)
        .is_ok_and(|quality| quality.is_complete()));
    let authored = exec.exact_concrete_authored_scope();
    assert!(ay_proof::validate_reachable_assumes_in_problem_scope(&proof, &authored).is_ok());
}

#[test]
fn bridge_without_antecedent_cannot_mint_a_certificate() {
    // GUARD-REMOVAL PROOF: without `(P a)` the existential side is
    // underivable, so the stitcher must decline even though the probe
    // consequences (with the witness facts) would refute.
    let mut exec = executor_with_assertions(
        r#"
            (set-logic UF)
            (declare-sort S 0)
            (declare-fun a () S)
            (declare-fun b () S)
            (declare-fun P (S) Bool)
            (declare-fun Q (S) Bool)
            (assert (forall ((x S)) (= (P x) (exists ((y S)) (and (= y x) (Q y))))))
            (assert (forall ((y S)) (=> (Q y) (= a b))))
            (assert (not (= a b)))
        "#,
    );
    exec.begin_public_solve(false);
    exec.bind_unsat_query_assumptions(&[]);
    assert!(
        !exec.try_translate_exists_bridge_chain_unsat(),
        "a bridge whose antecedent is underivable must never mint"
    );
    assert!(exec.last_proof.is_none());
}
