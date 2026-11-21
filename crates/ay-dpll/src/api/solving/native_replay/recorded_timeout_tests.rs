// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

fn input(timeout: Option<Duration>, contradiction: bool) -> NativeReplayArtifact {
    let mut solver = Solver::new(Logic::QfUf);
    solver.set_timeout(timeout);
    let p = solver.declare_const("recorded_timeout_p", crate::api::Sort::Bool);
    solver.assert_term(p);
    if contradiction {
        let negative = solver.not(p);
        solver.assert_term(negative);
    }
    solver.export_native_replay_artifact(NativeReplayMetadata::default(), None)
}

#[test]
fn native_replay_proof_keeps_the_original_optional_timeout_in_the_executing_solver() {
    for (recorded, caller, effective) in [
        (None, None, None),
        (Some(2_000), None, Some(2_000_u64)),
        (Some(2_000), Some(1_000), Some(1_000)),
    ] {
        let original = input(recorded.map(Duration::from_millis), true);
        let before = original.to_json_value();
        let (details, executed) = Solver::replay_native_replay_artifact_impl(
            &original,
            caller.map(Duration::from_millis),
            true,
        )
        .unwrap();
        Solver::require_native_replay_proof_authority(details).unwrap();
        let after = executed.export_native_replay_artifact(NativeReplayMetadata::default(), None);
        assert_eq!(after.timeout_ms, effective.map(u128::from));
        assert_eq!(original.to_json_value(), before);
        executed
            .export_last_unsat_artifact()
            .unwrap()
            .accept_for_consumer(ProofAcceptanceMode::Strict)
            .unwrap();
    }
}

#[test]
fn native_replay_public_proof_entries_accept_no_override_with_strict_authority() {
    let original = input(None, true);
    assert_eq!(original.timeout_ms, None);
    let details = Solver::replay_native_replay_artifact_with_proofs(&original, None).unwrap();
    assert!(details.result.is_unsat());
    assert!(details.verification.unsat_proof_strictly_verified);

    let (details, proof) =
        Solver::replay_native_replay_artifact_with_checked_proof(&original, None).unwrap();
    assert!(details.result.is_unsat());
    assert!(details.verification.unsat_proof_strictly_verified);
    let proof = proof.unwrap();
    proof
        .accept_for_consumer(ProofAcceptanceMode::Strict)
        .unwrap();
    assert_eq!(proof.quality.trust_count, 0);
    assert_eq!(proof.quality.hole_count, 0);
}

#[test]
fn native_replay_optional_proof_limit_does_not_turn_sat_into_unsat_evidence() {
    let original = input(None, false);
    let (details, proof) =
        Solver::replay_native_replay_artifact_with_checked_proof(&original, None).unwrap();
    assert!(details.result.is_sat());
    assert!(details.result.was_model_validated());
    assert!(details.result.has_sat_emission_witness());
    assert!(proof.is_none());
}

#[test]
fn native_replay_original_mapping_checks_every_step_and_withholds_unexportable_proof() {
    let input = include_str!("data/mapping_invalid_key_native.json");
    assert_eq!(
        format!("{:x}", Sha256::digest(input.as_bytes())),
        "aea2047d84cf8dbadf51900170dad9972d6be581e38444f1242dc92bee6b7b2a"
    );
    let original = NativeReplayArtifact::from_json_str(input).unwrap();
    assert_eq!(original.timeout_ms, None);
    assert_eq!(
        original
            .assertions
            .iter()
            .map(|row| row.term.0)
            .collect::<Vec<_>>(),
        vec![7, 10, 19, 0, 41]
    );
    // The native ROW rule can prove the read from a constant-false array at
    // every unwritten index. The pinned Alethe checker has no such primitive.
    let (details, proof) =
        Solver::replay_native_replay_artifact_with_checked_proof(&original, None).unwrap();
    let stats = &details.statistics;
    assert!(stats.proof_complete);
    let checked = stats.get_int("proof_checker_checked_steps");
    assert!(checked.is_some_and(|steps| steps > 0));
    assert_eq!(checked, stats.get_int("proof_checker_total_steps"));
    assert_eq!(stats.get_int("proof_checker_failures"), Some(0));
    assert_eq!(stats.get_int("proof_checker_skipped_hole_steps"), Some(0));
    assert_eq!(stats.get_int("proof_trust"), Some(0));

    assert!(details.result.is_unknown(), "{details:?}");
    assert_eq!(
        stats.get_string("unknown.cost_center"),
        Some("proof-trusted")
    );
    assert!(stats
        .get_string("unknown.detail")
        .is_some_and(|reason| reason.contains("Alethe rendering has a known wire gap")));
    assert!(!details.verification.unsat_proof_strictly_verified);
    assert!(proof.is_none());
}

fn check_wp_body_packet(input: &str, digest: &str, roots: &[u32]) {
    assert_eq!(format!("{:x}", Sha256::digest(input.as_bytes())), digest);
    let original = NativeReplayArtifact::from_json_str(input).unwrap();
    assert_eq!(original.timeout_ms, Some(5_624));
    assert_eq!(
        original
            .assertions
            .iter()
            .map(|row| row.term.0)
            .collect::<Vec<_>>(),
        roots
    );
    let before = original.to_json_value();
    let (details, proof) =
        Solver::replay_native_replay_artifact_with_checked_proof(&original, None).unwrap();
    assert_eq!(original.to_json_value(), before);
    assert!(details.result.is_unsat(), "{details:?}");
    assert!(details.verification.unsat_proof_strictly_verified);
    let proof = proof.expect("the actual WP body obligation needs a complete checked proof");
    proof
        .accept_for_consumer(ProofAcceptanceMode::Strict)
        .unwrap();
    assert_eq!(proof.quality.trust_count, 0);
    assert_eq!(proof.quality.hole_count, 0);
}

#[test]
fn native_replay_wp_nested_body_keeps_original_guarded_function_law() {
    check_wp_body_packet(
        include_str!("data/wp_nested_body_native.json"),
        "aaf2050e05a8aec239632e43ef4c99b0250cb734fdf2aad7fec9b3e6c6d6d340",
        &[7, 10, 17, 21],
    );
}

#[test]
fn native_replay_wp_bool_body_keeps_original_membership_and_reflexive_result() {
    check_wp_body_packet(
        include_str!("data/wp_bool_body_native.json"),
        "b2cf0bdb7dc80bc9d704ce0ae35ffa9552ad9e33abe98cf5bdaf9cacdcedee89",
        &[7, 10, 17],
    );
}
