// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Native replay coverage for the admitted QF_UFBVLIA scalar subset.

#[cfg(feature = "proof-checker")]
use std::time::Duration;

use crate::api::{
    Logic, NativeReplayArtifact, NativeReplayEventKind, NativeReplayMetadata, Solver, Sort,
    UnknownReason,
};

fn assert_native_replay_logic(artifact: &NativeReplayArtifact, expected: &str) {
    let expected_route = format!("native-api:{expected}");
    assert_eq!(artifact.logic.as_deref(), Some(expected));
    assert_eq!(
        artifact.selected_route.as_deref(),
        Some(expected_route.as_str())
    );
    assert!(matches!(
        artifact.events.first().map(|event| &event.kind),
        Some(NativeReplayEventKind::SetLogic { logic }) if logic == expected
    ));
}

#[test]
fn qf_ufbvlia_native_replay_round_trips_validated_sat() {
    let mut solver = Solver::try_new(Logic::QfUfbvlia).expect("solver");
    let byte_sort = Sort::bitvec(8);
    let b = solver.declare_const("qf_ufbvlia_replay_b", byte_sort.clone());
    let i = solver.declare_const("qf_ufbvlia_replay_i", Sort::Int);
    let function = solver
        .try_declare_fun(
            "qf_ufbvlia_replay_f",
            std::slice::from_ref(&byte_sort),
            byte_sort.clone(),
        )
        .expect("declare BV function");
    let five = solver.bv_const(5, 8);
    let six = solver.bv_const(6, 8);
    let three = solver.int_const(3);
    let b_eq_five = solver.try_eq(b, five).expect("b = 5");
    let function_of_b = solver.try_apply(&function, &[b]).expect("f(b)");
    let function_eq_six = solver.try_eq(function_of_b, six).expect("f(b) = 6");
    let i_eq_three = solver.try_eq(i, three).expect("i = 3");
    for assertion in [b_eq_five, function_eq_six, i_eq_three] {
        solver
            .try_assert_term(assertion)
            .expect("assert scalar fact");
    }

    let details = solver.check_sat_with_details();
    assert!(details.result.is_sat());
    assert!(
        details.result.was_model_validated() && details.verification.sat_model_validated,
        "the source mixed scalar query must publish only a validated SAT model"
    );
    let artifact =
        solver.export_native_replay_artifact(NativeReplayMetadata::default(), Some(&details));
    assert_native_replay_logic(&artifact, "QF_UFBVLIA");

    let replay = Solver::replay_native_replay_artifact(&artifact).expect("in-memory replay");
    assert!(replay.result.is_sat());
    assert!(replay.result.was_model_validated() && replay.verification.sat_model_validated);
    let replay_from_json =
        Solver::replay_native_replay_json_str(&artifact.to_pretty_json()).expect("JSON replay");
    assert!(replay_from_json.result.is_sat());
    assert!(
        replay_from_json.result.was_model_validated()
            && replay_from_json.verification.sat_model_validated
    );
}

#[test]
fn qf_ufbvlia_native_replay_round_trips_int2bv_bridge_sat() {
    let mut solver = Solver::try_new(Logic::QfUfbvlia).expect("solver");
    let i = solver.declare_const("qf_ufbvlia_int2bv_i", Sort::Int);
    let residue = solver.int2bv(i, 8);
    let two_hundred_sixty_one = solver.int_const(261);
    let five = solver.bv_const(5, 8);
    let i_eq_261 = solver.try_eq(i, two_hundred_sixty_one).expect("i = 261");
    let residue_eq_five = solver.try_eq(residue, five).expect("int2bv(i) = #x05");
    solver.try_assert_term(i_eq_261).expect("assert integer");
    solver
        .try_assert_term(residue_eq_five)
        .expect("assert residue");

    let details = solver.check_sat_with_details();
    assert!(details.result.is_sat());
    assert!(details.result.was_model_validated() && details.verification.sat_model_validated);
    assert_eq!(
        details.statistics.get_string("solver.logic_category"),
        Some("QfBvLia")
    );
    let artifact =
        solver.export_native_replay_artifact(NativeReplayMetadata::default(), Some(&details));
    assert_native_replay_logic(&artifact, "QF_UFBVLIA");

    let replay = Solver::replay_native_replay_artifact(&artifact).expect("int2bv replay");
    assert!(replay.result.is_sat());
    assert!(replay.result.was_model_validated() && replay.verification.sat_model_validated);
    assert_eq!(
        replay.statistics.get_string("solver.logic_category"),
        Some("QfBvLia")
    );
    let replay_from_json = Solver::replay_native_replay_json_str(&artifact.to_pretty_json())
        .expect("JSON int2bv replay");
    assert!(replay_from_json.result.is_sat());
    assert!(
        replay_from_json.result.was_model_validated()
            && replay_from_json.verification.sat_model_validated
    );
}

#[cfg(feature = "proof-checker")]
#[test]
fn qf_ufbvlia_native_replay_preserves_strict_unsat_authority() {
    let mut solver = Solver::try_new(Logic::QfUfbvlia).expect("solver");
    solver.set_produce_proofs(true);
    solver
        .try_set_option(":check-proofs-strict", "true")
        .expect("enable strict proof checking");
    let b = solver.declare_const("qf_ufbvlia_strict_b", Sort::bitvec(8));
    let i = solver.declare_const("qf_ufbvlia_strict_i", Sort::Int);
    let p = solver.declare_const("qf_ufbvlia_strict_p", Sort::Bool);
    let five = solver.bv_const(5, 8);
    let three = solver.int_const(3);
    let b_eq_five = solver.try_eq(b, five).expect("b = 5");
    let i_eq_three = solver.try_eq(i, three).expect("i = 3");
    let not_p = solver.try_not(p).expect("not p");
    for assertion in [b_eq_five, i_eq_three, p, not_p] {
        solver
            .try_assert_term(assertion)
            .expect("assert strict fact");
    }

    let details = solver.check_sat_with_details();
    assert!(details.result.is_unsat());
    assert!(details.result.was_unsat_strictly_verified());
    assert_eq!(
        details.statistics.get_string("solver.logic_category"),
        Some("QfBvLiaIndep")
    );
    let artifact =
        solver.export_native_replay_artifact(NativeReplayMetadata::default(), Some(&details));
    assert_native_replay_logic(&artifact, "QF_UFBVLIA");

    let replay =
        Solver::replay_native_replay_artifact_with_proofs(&artifact, Duration::from_secs(5))
            .expect("strict QF_UFBVLIA replay");
    assert!(replay.result.is_unsat());
    assert!(replay.result.was_unsat_strictly_verified());
    assert_eq!(
        replay.statistics.get_string("solver.logic_category"),
        Some("QfBvLiaIndep")
    );
    assert!(replay.verification.unsat_proof_available);
    assert!(replay.verification.unsat_proof_strictly_verified);
    assert_eq!(replay.verification.unsat_proof_checker_failures, 0);
    assert!(replay.statistics.proof_complete);
    assert_eq!(replay.statistics.get_int("proof_trust"), Some(0));
    assert_eq!(
        replay
            .statistics
            .get_int("proof_checker_skipped_hole_steps"),
        Some(0)
    );
}

#[test]
fn qf_ufbvlia_native_replay_preserves_assumption_fail_close() {
    let mut solver = Solver::try_new(Logic::QfUfbvlia).expect("solver");
    let b = solver.declare_const("qf_ufbvlia_assumption_b", Sort::bitvec(2));
    let i = solver.declare_const("qf_ufbvlia_assumption_i", Sort::Int);
    let predicate = solver
        .try_declare_fun(
            "qf_ufbvlia_assumption_p",
            &[Sort::bitvec(2), Sort::Int],
            Sort::Bool,
        )
        .expect("declare mixed predicate");
    let zero_bv = solver.bv_const(0, 2);
    let zero_int = solver.int_const(0);
    let b_eq_zero = solver.try_eq(b, zero_bv).expect("b = 0");
    let i_eq_zero = solver.try_eq(i, zero_int).expect("i = 0");
    solver.try_assert_term(b_eq_zero).expect("assert b");
    solver.try_assert_term(i_eq_zero).expect("assert i");
    let coupled = solver
        .try_apply(&predicate, &[b, i])
        .expect("mixed predicate application");

    let details = solver.check_sat_assuming_with_details(&[coupled]);
    assert!(details.solve.result.is_unknown());
    assert_eq!(
        details.solve.unknown_reason,
        Some(UnknownReason::Incomplete)
    );
    assert!(!details.solve.verification.unsat_proof_available);
    assert!(!details.solve.verification.sat_model_validated);
    let artifact =
        solver.export_native_replay_artifact(NativeReplayMetadata::default(), Some(&details.solve));
    assert_native_replay_logic(&artifact, "QF_UFBVLIA");
    let source = artifact.solve.as_ref().expect("source solve summary");
    assert_eq!(source.unknown_reason.as_deref(), Some("incomplete"));
    assert!(!source.proof.available);
    assert!(!source.model.validated);
    assert!(artifact
        .events
        .iter()
        .any(|event| matches!(&event.kind, NativeReplayEventKind::CheckSatAssuming { .. })));

    let replay = Solver::replay_native_replay_artifact(&artifact).expect("assumption replay");
    assert!(replay.result.is_unknown());
    assert_eq!(replay.unknown_reason, Some(UnknownReason::Incomplete));
    assert!(!replay.verification.unsat_proof_available);
    assert!(!replay.verification.sat_model_validated);
    let replay_from_json = Solver::replay_native_replay_json_str(&artifact.to_pretty_json())
        .expect("JSON assumption replay");
    assert!(replay_from_json.result.is_unknown());
}

#[test]
fn qf_aufbvlia_native_replay_round_trips_validated_scalar_sat() {
    let mut solver = Solver::try_new(Logic::QfAufbvlia).expect("solver");
    let b = solver.declare_const("qf_aufbvlia_replay_b", Sort::bitvec(8));
    let i = solver.declare_const("qf_aufbvlia_replay_i", Sort::Int);
    let five = solver.bv_const(5, 8);
    let three = solver.int_const(3);
    let b_eq_five = solver.try_eq(b, five).expect("b = 5");
    let i_eq_three = solver.try_eq(i, three).expect("i = 3");
    solver.try_assert_term(b_eq_five).expect("assert b");
    solver.try_assert_term(i_eq_three).expect("assert i");

    let details = solver.check_sat_with_details();
    assert!(details.result.is_sat());
    assert!(details.result.was_model_validated() && details.verification.sat_model_validated);
    let artifact =
        solver.export_native_replay_artifact(NativeReplayMetadata::default(), Some(&details));
    assert_native_replay_logic(&artifact, "QF_AUFBVLIA");

    let replay = Solver::replay_native_replay_artifact(&artifact).expect("scalar replay");
    assert!(replay.result.is_sat());
    assert!(replay.result.was_model_validated() && replay.verification.sat_model_validated);
}

#[test]
fn qf_aufbvlia_native_replay_keeps_live_arrays_fail_closed() {
    let mut solver = Solver::try_new(Logic::QfAufbvlia).expect("solver");
    let byte_sort = Sort::bitvec(8);
    let array = solver.declare_const(
        "qf_aufbvlia_replay_array",
        Sort::array(byte_sort.clone(), byte_sort),
    );
    let i = solver.declare_const("qf_aufbvlia_replay_i", Sort::Int);
    let index = solver.bv_const(0, 8);
    let value = solver.bv_const(1, 8);
    let zero = solver.int_const(0);
    let selected = solver.try_select(array, index).expect("array select");
    let selected_eq_value = solver.try_eq(selected, value).expect("select = 1");
    let i_eq_zero = solver.try_eq(i, zero).expect("i = 0");
    solver
        .try_assert_term(selected_eq_value)
        .expect("assert array fact");
    solver
        .try_assert_term(i_eq_zero)
        .expect("assert integer fact");

    let details = solver.check_sat_with_details();
    assert!(details.result.is_unknown());
    assert_eq!(details.unknown_reason, Some(UnknownReason::Incomplete));
    assert!(!details.verification.unsat_proof_available);
    assert!(!details.verification.sat_model_validated);
    let artifact =
        solver.export_native_replay_artifact(NativeReplayMetadata::default(), Some(&details));
    assert_native_replay_logic(&artifact, "QF_AUFBVLIA");
    let source = artifact.solve.as_ref().expect("source solve summary");
    assert_eq!(source.unknown_reason.as_deref(), Some("incomplete"));
    assert!(!source.proof.available);
    assert!(!source.model.validated);

    let replay = Solver::replay_native_replay_artifact(&artifact).expect("array replay");
    assert!(replay.result.is_unknown());
    assert_eq!(replay.unknown_reason, Some(UnknownReason::Incomplete));
    assert!(!replay.verification.unsat_proof_available);
    assert!(!replay.verification.sat_model_validated);
    let replay_from_json = Solver::replay_native_replay_json_str(&artifact.to_pretty_json())
        .expect("JSON array replay");
    assert!(replay_from_json.result.is_unknown());
}
