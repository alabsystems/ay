// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Public native consumer controls for the unbounded UF parity cut. The
//! standalone kernel's UF proof-recording restriction is not changed here.

use ay_dpll::api::{
    Logic, NativeReplayArtifact, NativeReplayMetadata, ProofAcceptanceMode, Solver, Sort,
};
use std::time::Duration;

fn original_query(upper: i64) -> NativeReplayArtifact {
    let mut solver = Solver::new(Logic::QfUflia);
    solver.set_timeout(Some(Duration::from_millis(5624)));
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let two = solver.int_const(2);
    let q = solver.declare_fun("q", &[Sort::Int, Sort::Int], Sort::Int);
    let x2 = solver.add(x, two);
    let q0 = solver.apply(&q, &[x, two]);
    let q2 = solver.apply(&q, &[x2, two]);
    let twice0 = solver.mul(two, q0);
    let twice2 = solver.mul(two, q2);
    let r0 = solver.sub(x, twice0);
    let r2 = solver.sub(x2, twice2);
    let positive = solver.gt(r2, zero);
    let even = solver.eq(r0, zero);
    let upper = solver.int_const(upper);
    let bounded = solver.le(r2, upper);
    for root in [positive, even, bounded] {
        solver.assert_term(root);
    }
    solver.export_native_replay_artifact(NativeReplayMetadata::default(), None)
}

#[test]
fn original_native_uf_parity_cut_has_a_complete_accepted_proof() {
    let input = original_query(1);
    assert_eq!(input.assertions.len(), 3);
    assert_eq!(input.timeout_ms, Some(5624));
    let (details, proof) = Solver::replay_native_replay_artifact_with_checked_proof(
        &input,
        Duration::from_millis(5624),
    )
    .unwrap();
    assert!(
        details.accept_for_consumer().unwrap().is_unsat(),
        "{details:?}"
    );
    assert!(details.verification.unsat_proof_strictly_verified);
    let proof = proof.expect("accepted original-query proof must be retained");
    proof
        .accept_for_consumer(ProofAcceptanceMode::Strict)
        .unwrap();
    assert_eq!(proof.quality.trust_count, 0);
    assert_eq!(proof.quality.hole_count, 0);
    assert!(proof.alethe_problem_smt2.is_some());
}

#[test]
fn original_native_uf_parity_looser_neighbor_has_a_validated_model() {
    let input = original_query(2);
    let (details, proof) = Solver::replay_native_replay_artifact_with_checked_proof(
        &input,
        Duration::from_millis(5624),
    )
    .unwrap();
    assert!(
        details.accept_for_consumer().unwrap().is_sat(),
        "{details:?}"
    );
    assert!(details.result.was_model_validated());
    assert!(details.result.has_sat_emission_witness());
    assert!(proof.is_none());
}
