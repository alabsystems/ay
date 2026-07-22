// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Native replay artifact tests for downstream reducer handoff.

use std::time::Duration;

use crate::api::{
    Logic, NativeReplayArtifact, NativeReplayEventKind, NativeReplayMetadata, SolveResult, Solver,
    Sort,
};

#[test]
fn native_replay_artifact_round_trips_active_assertions() {
    let mut solver = Solver::try_new(Logic::QfLia).expect("solver");
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let one = solver.int_const(1);
    let x_gt_zero = solver.try_gt(x, zero).expect("x > 0");
    solver
        .try_assert_named(x_gt_zero, "precondition")
        .expect("assert");
    let x_eq_one = solver.try_eq(x, one).expect("x = 1");
    solver.try_assert_term(x_eq_one).expect("assert");

    let details = solver.check_sat_with_details();
    assert_eq!(*details.result.result(), SolveResult::Sat);

    let artifact = solver.export_native_replay_artifact(
        NativeReplayMetadata {
            consumer: Some("verification-consumer".to_string()),
            fixture_path: Some("tests/should_succeed/take_first_mut.rs".to_string()),
            obligation_kind: Some("ensures".to_string()),
            ..Default::default()
        },
        Some(&details),
    );

    assert_eq!(artifact.schema, "ay.native-replay.v1");
    assert_eq!(
        artifact.metadata.consumer.as_deref(),
        Some("verification-consumer")
    );
    assert!(artifact
        .events
        .iter()
        .any(|event| matches!(event.kind, NativeReplayEventKind::CheckSat)));
    assert_eq!(artifact.assertions.len(), 2);
    let json = artifact.to_pretty_json();
    assert!(json.contains("precondition"));

    let replay = Solver::replay_native_replay_artifact(&artifact).expect("native replay");
    assert_eq!(replay.result.result(), details.result.result());

    let parsed = NativeReplayArtifact::from_json_str(&json).expect("parse native replay JSON");
    let replay_from_json =
        Solver::replay_native_replay_artifact(&parsed).expect("native replay from parsed JSON");
    assert_eq!(replay_from_json.result.result(), details.result.result());

    let replay_from_json_str =
        Solver::replay_native_replay_json_str(&json).expect("native replay from JSON string");
    assert_eq!(
        replay_from_json_str.result.result(),
        details.result.result()
    );
}

#[test]
fn native_replay_artifact_carries_checked_replay_proof_model_status() {
    let mut solver = Solver::try_new(Logic::QfLia).expect("solver");
    let x = solver.declare_const("x", Sort::Int);
    let one = solver.int_const(1);
    let x_eq_one = solver.try_eq(x, one).expect("x = 1");
    solver
        .try_assert_named(x_eq_one, "verification-consumer-ensures")
        .expect("assert");

    let details = solver.check_sat_with_details();
    assert_eq!(*details.result.result(), SolveResult::Sat);

    let artifact = solver.export_native_replay_artifact(
        NativeReplayMetadata {
            consumer: Some("verification-consumer".to_string()),
            fixture_path: Some("tests/should_succeed/bitvectors/popcount.rs".to_string()),
            obligation_kind: Some("ensures".to_string()),
            ..Default::default()
        },
        Some(&details),
    );
    let replay = Solver::replay_native_replay_artifact(&artifact).expect("native replay");
    let artifact = artifact.with_checked_replay(&replay);

    let checked = artifact.checked_replay.as_ref().expect("checked replay");
    assert_eq!(checked.original_result.as_deref(), Some("sat"));
    assert_eq!(checked.replay_result, "sat");
    assert!(checked.result_matches);
    assert_eq!(
        checked.original_proof_status.as_deref(),
        Some("not-applicable")
    );
    assert_eq!(checked.replay_proof_status, "not-applicable");
    assert!(checked.proof_status_matches);
    assert_eq!(
        checked.original_model_status.as_deref(),
        Some(checked.replay_model_status.as_str())
    );
    assert!(checked.model_status_matches);

    let json = artifact.to_json_value();
    assert_eq!(
        json["checked_replay"]["result_matches"].as_bool(),
        Some(true)
    );
    assert_eq!(
        json["checked_replay"]["replay_proof_status"].as_str(),
        Some("not-applicable")
    );
    assert!(json["checked_replay"]["replay_model_status"].is_string());

    let parsed =
        NativeReplayArtifact::from_json_str(&artifact.to_pretty_json()).expect("parse JSON");
    assert_eq!(parsed.checked_replay, artifact.checked_replay);
}

#[test]
fn native_replay_verification_consumer_hashmap_get_restore_bridge_replays_sat() {
    let artifact = NativeReplayArtifact::from_json_str(include_str!(
        "../../../tests/fixtures/verification_consumer_9185/hashmap_get_init_native_min.json"
    ))
    .expect("parse verification-consumer hashmap get native replay fixture");
    let replay = Solver::replay_native_replay_artifact(&artifact).expect("native replay");
    assert_eq!(
        *replay.result.result(),
        SolveResult::Sat,
        "unknown_reason={:?} diagnostic={:?}",
        replay.unknown_reason,
        replay.unknown_diagnostic,
    );
}

#[test]
fn native_replay_artifact_carries_unknown_progress() {
    let mut solver = Solver::try_new(Logic::QfLia).expect("solver");
    solver.set_timeout(Some(Duration::ZERO));

    let artifact = solver.try_check_sat_with_native_replay(NativeReplayMetadata {
        consumer: Some("verification-consumer".to_string()),
        notes: Some("timeout preflight".to_string()),
        ..Default::default()
    });

    let solve = artifact.solve.as_ref().expect("solve summary");
    assert_eq!(solve.result, "unknown");
    assert_eq!(solve.unknown_reason.as_deref(), Some("timeout"));
    assert_eq!(solve.unknown_phase.as_deref(), Some("search-control"));
    let progress = solve.unknown_progress.as_ref().expect("unknown progress");
    assert_eq!(progress.reason, "timeout");
    assert_eq!(
        progress.responsible_phase.as_deref(),
        Some("search-control")
    );
    assert_eq!(progress.wall_time_budget_ms, Some(0));
    assert!(artifact.to_pretty_json().contains("unknown_progress"));
}

#[test]
fn native_replay_artifact_records_scopes_and_duplicate_assertion_names() {
    let mut solver = Solver::try_new(Logic::QfLia).expect("solver");
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let x_ge_zero = solver.try_ge(x, zero).expect("x >= 0");

    solver
        .try_assert_named(x_ge_zero, "base-lower-bound")
        .expect("base assert");
    solver.try_push().expect("push");
    solver
        .try_assert_named(x_ge_zero, "scoped-shadow")
        .expect("scoped assert");
    solver.try_pop().expect("pop");
    solver
        .try_assert_named(x_ge_zero, "base-lower-bound-duplicate")
        .expect("duplicate base assert");

    let details = solver.check_sat_with_details();
    let artifact =
        solver.export_native_replay_artifact(NativeReplayMetadata::default(), Some(&details));
    let json = artifact.to_pretty_json();

    assert!(artifact
        .events
        .iter()
        .any(|event| matches!(event.kind, NativeReplayEventKind::Push)));
    assert!(artifact
        .events
        .iter()
        .any(|event| matches!(event.kind, NativeReplayEventKind::Pop)));
    assert!(json.contains("\"event\": \"push\""));
    assert!(json.contains("\"event\": \"pop\""));
    assert_eq!(artifact.assertions.len(), 2);
    assert_eq!(
        artifact.assertions[0].name.as_deref(),
        Some("base-lower-bound")
    );
    assert_eq!(
        artifact.assertions[1].name.as_deref(),
        Some("base-lower-bound-duplicate")
    );

    let parsed = NativeReplayArtifact::from_json_str(&json).expect("parse scoped replay JSON");
    assert_eq!(parsed.events.len(), artifact.events.len());
    let replay = Solver::replay_native_replay_artifact(&parsed).expect("scoped replay");
    assert_eq!(replay.result.result(), details.result.result());
}

#[test]
fn native_replay_artifact_preserves_active_same_term_scope_depths() {
    let mut solver = Solver::try_new(Logic::QfLia).expect("solver");
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let x_ge_zero = solver.try_ge(x, zero).expect("x >= 0");

    solver
        .try_assert_named(x_ge_zero, "base-lower-bound")
        .expect("base assert");
    solver.try_push().expect("push");
    solver
        .try_assert_named(x_ge_zero, "scoped-lower-bound")
        .expect("scoped assert");

    let details = solver.check_sat_with_details();
    let artifact =
        solver.export_native_replay_artifact(NativeReplayMetadata::default(), Some(&details));

    assert_eq!(artifact.assertions.len(), 2);
    assert_eq!(
        artifact.assertions[0].name.as_deref(),
        Some("base-lower-bound")
    );
    assert_eq!(artifact.assertions[0].scope_depth, 0);
    assert_eq!(
        artifact.assertions[1].name.as_deref(),
        Some("scoped-lower-bound")
    );
    assert_eq!(artifact.assertions[1].scope_depth, 1);

    let replay = Solver::replay_native_replay_artifact(&artifact).expect("active scoped replay");
    assert_eq!(replay.result.result(), details.result.result());

    let replay_from_json =
        Solver::replay_native_replay_json_str(&artifact.to_pretty_json()).expect("JSON replay");
    assert_eq!(replay_from_json.result.result(), details.result.result());
}

#[test]
fn native_replay_replays_active_scoped_assertions_from_json() {
    let mut solver = Solver::try_new(Logic::QfLia).expect("solver");
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let x_ge_zero = solver.try_ge(x, zero).expect("x >= 0");
    let x_lt_zero = solver.try_lt(x, zero).expect("x < 0");

    solver
        .try_assert_named(x_ge_zero, "base-lower-bound")
        .expect("base assert");
    solver.try_push().expect("push");
    solver
        .try_assert_named(x_lt_zero, "scoped-upper-bound")
        .expect("scoped assert");

    let details = solver.check_sat_with_details();
    assert!(details.result.result().is_unsat());

    let artifact =
        solver.export_native_replay_artifact(NativeReplayMetadata::default(), Some(&details));
    assert_eq!(artifact.assertions.len(), 2);
    assert_eq!(
        artifact.assertions[1].name.as_deref(),
        Some("scoped-upper-bound")
    );
    assert_eq!(artifact.assertions[1].scope_depth, 1);

    let replay_from_json =
        Solver::replay_native_replay_json_str(&artifact.to_pretty_json()).expect("JSON replay");
    assert_eq!(replay_from_json.result.result(), details.result.result());
}

#[test]
fn native_replay_replays_check_sat_assuming_event() {
    let mut solver = Solver::try_new(Logic::QfLia).expect("solver");
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let x_ge_zero = solver.try_ge(x, zero).expect("x >= 0");
    let x_lt_zero = solver.try_lt(x, zero).expect("x < 0");

    solver
        .try_assert_named(x_ge_zero, "base-lower-bound")
        .expect("base assert");
    let details = solver.check_sat_assuming_with_details(&[x_lt_zero]);
    assert!(details.solve.result.result().is_unsat());

    let artifact =
        solver.export_native_replay_artifact(NativeReplayMetadata::default(), Some(&details.solve));
    assert!(artifact
        .events
        .iter()
        .any(|event| matches!(event.kind, NativeReplayEventKind::CheckSatAssuming { .. })));

    let replay = Solver::replay_native_replay_artifact(&artifact).expect("assumption replay");
    assert_eq!(replay.result.result(), details.solve.result.result());

    let parsed =
        NativeReplayArtifact::from_json_str(&artifact.to_pretty_json()).expect("parse JSON");
    let replay_from_json =
        Solver::replay_native_replay_artifact(&parsed).expect("assumption replay from JSON");
    assert_eq!(
        replay_from_json.result.result(),
        details.solve.result.result()
    );
}
