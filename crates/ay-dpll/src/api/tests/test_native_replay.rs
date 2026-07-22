// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Native replay artifact tests for downstream reducer handoff.

use std::time::Duration;

use crate::api::{
    DatatypeConstructor, DatatypeField, DatatypeSort, Logic, NativeReplayArtifact,
    NativeReplayEventKind, NativeReplayMetadata, SolveResult, Solver, Sort,
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

#[test]
fn native_replay_preserves_datatype_semantics_in_memory_and_json() {
    let mut solver = Solver::try_new(Logic::Uf).expect("solver");
    let color = DatatypeSort::new(
        "ReplayColor",
        vec![
            DatatypeConstructor::unit("ReplayRed"),
            DatatypeConstructor::unit("ReplayBlue"),
        ],
    );
    solver
        .try_declare_datatype(&color)
        .expect("declare datatype");
    let value = solver.declare_const("replay_color_value", Sort::Datatype(color.clone()));
    let red = solver.datatype_constructor(&color, "ReplayRed", &[]);
    let blue = solver.datatype_constructor(&color, "ReplayBlue", &[]);
    let value_is_red = solver.try_eq(value, red).expect("value = red");
    let value_is_blue = solver.try_eq(value, blue).expect("value = blue");
    solver.try_assert_term(value_is_red).expect("assert red");
    solver.try_assert_term(value_is_blue).expect("assert blue");

    let details = solver.check_sat_with_details();
    assert!(details.result.result().is_unsat());
    let artifact =
        solver.export_native_replay_artifact(NativeReplayMetadata::default(), Some(&details));
    assert!(artifact.events.iter().any(|event| matches!(
        &event.kind,
        NativeReplayEventKind::DeclareDatatype { datatype } if datatype == &color
    )));

    let replay = Solver::replay_native_replay_artifact(&artifact).expect("datatype replay");
    assert!(replay.result.result().is_unsat());
    let replay_from_json = Solver::replay_native_replay_json_str(&artifact.to_pretty_json())
        .expect("datatype JSON replay");
    assert!(replay_from_json.result.result().is_unsat());
}

#[test]
fn native_replay_exports_only_active_term_dependencies() {
    let mut solver = Solver::try_new(Logic::QfLia).expect("solver");
    let active = solver.declare_const("active", Sort::Int);
    let dead = solver.declare_const("dead", Sort::Int);
    let one = solver.int_const(1);
    let dead_sum = solver.try_add(dead, one).expect("dead expression");
    let active_eq_one = solver.try_eq(active, one).expect("active = 1");
    solver
        .try_assert_term(active_eq_one)
        .expect("assert active");

    let details = solver.check_sat_with_details();
    let artifact =
        solver.export_native_replay_artifact(NativeReplayMetadata::default(), Some(&details));
    assert!(artifact.terms.iter().all(|node| node.id != dead.0));
    assert!(artifact.terms.iter().all(|node| node.id != dead_sum.0));
    assert!(artifact
        .declarations
        .iter()
        .all(|declaration| declaration.term != dead.0));

    let replay = Solver::replay_native_replay_json_str(&artifact.to_pretty_json())
        .expect("dependency-sliced JSON replay");
    assert_eq!(replay.result.result(), details.result.result());
}

#[test]
fn native_replay_distinguishes_fresh_vars_shadowing_nullary_constructors() {
    let mut solver = Solver::try_new(Logic::All).expect("solver");
    let color = DatatypeSort::new(
        "ShadowColor",
        vec![
            DatatypeConstructor::unit("ShadowRed"),
            DatatypeConstructor::unit("ShadowBlue"),
        ],
    );
    solver.try_declare_datatype(&color).expect("datatype");
    let red = solver.datatype_constructor(&color, "ShadowRed", &[]);
    let shadow = solver.declare_const_with_fresh_identity(
        "ShadowRed",
        "!ay.test-shadow-red",
        Sort::Datatype(color.clone()),
    );
    let shadow_ne_red = solver
        .try_eq(shadow, red)
        .and_then(|equal| solver.try_not(equal))
        .expect("shadow != red");
    solver.try_assert_term(shadow_ne_red).expect("assert");

    let details = solver.check_sat_with_details();
    assert!(details.result.result().is_sat());
    let artifact =
        solver.export_native_replay_artifact(NativeReplayMetadata::default(), Some(&details));
    let shadow_node = artifact
        .terms
        .iter()
        .find(|node| node.id == shadow.0)
        .expect("shadow node");
    assert!(!shadow_node.is_datatype_constructor);
    let red_node = artifact
        .terms
        .iter()
        .find(|node| node.id == red.0)
        .expect("constructor node");
    assert!(red_node.is_datatype_constructor);

    let replay = Solver::replay_native_replay_json_str(&artifact.to_pretty_json())
        .expect("shadowing replay");
    assert!(
        replay.result.result().is_sat(),
        "replay result={:?} unknown={:?} executor={:?}",
        replay.result.result(),
        replay.unknown_reason,
        replay.executor_error
    );
}

#[test]
fn native_replay_structural_sorts_round_trip_without_kind_loss() {
    let mut solver = Solver::try_new(Logic::All).expect("solver");
    let char_value = solver.declare_const("char_value", Sort::Char);
    let finite_sort = Sort::FiniteDomain("FiniteFive".to_string(), 5);
    let finite_value = solver.declare_const("finite_value", finite_sort.clone());
    let type_var_sort = Sort::TypeVar("TypeAlpha".to_string());
    let type_left = solver.declare_const("type_left", type_var_sort.clone());
    let type_right = solver.declare_const("type_right", type_var_sort.clone());
    let zero = solver.int_const(0);
    let char_nonnegative = solver.try_ge(char_value, zero).expect("char >= 0");
    let finite_nonnegative = solver.try_ge(finite_value, zero).expect("finite >= 0");
    let types_equal = solver
        .try_eq(type_left, type_right)
        .expect("type vars equal");
    solver
        .try_assert_term(char_nonnegative)
        .expect("assert char");
    solver
        .try_assert_term(finite_nonnegative)
        .expect("assert finite");
    solver
        .try_assert_term(types_equal)
        .expect("assert type var");

    let nested = DatatypeSort::new(
        "StructuralBox",
        vec![DatatypeConstructor::new(
            "StructuralBoxMk",
            vec![DatatypeField::new("structural_char", Sort::Char)],
        )],
    );
    solver
        .try_declare_datatype(&nested)
        .expect("nested datatype");

    let details = solver.check_sat_with_details();
    let artifact =
        solver.export_native_replay_artifact(NativeReplayMetadata::default(), Some(&details));
    let parsed = NativeReplayArtifact::from_json_str(&artifact.to_pretty_json())
        .expect("parse structural sorts");
    for expected in [Sort::Char, finite_sort, type_var_sort] {
        assert!(parsed
            .declarations
            .iter()
            .any(|declaration| declaration.sort == expected));
    }
    assert!(parsed.events.iter().any(|event| matches!(
        &event.kind,
        NativeReplayEventKind::DeclareDatatype { datatype } if datatype == &nested
    )));
    let replay = Solver::replay_native_replay_artifact(&parsed).expect("structural sort replay");
    assert_eq!(replay.result.result(), details.result.result());
}

#[test]
fn native_replay_u128_json_is_lossless_above_u64() {
    let solver = Solver::try_new(Logic::QfLia).expect("solver");
    let mut artifact = solver.export_native_replay_artifact(NativeReplayMetadata::default(), None);
    let large = u128::from(u64::MAX) + 42;
    artifact.created_unix_ms = large;
    artifact.timeout_ms = Some(large + 1);

    let json = artifact.to_pretty_json();
    let parsed = NativeReplayArtifact::from_json_str(&json).expect("parse large u128 values");
    assert_eq!(parsed.created_unix_ms, large);
    assert_eq!(parsed.timeout_ms, Some(large + 1));
}

#[test]
fn native_replay_keeps_functions_referenced_by_as_array_and_array_map() {
    let mut solver = Solver::try_new(Logic::All).expect("solver");
    solver
        .try_declare_fun("replay_array_function", &[Sort::Int], Sort::Int)
        .expect("declare mapped function");
    let array_sort = Sort::array(Sort::Int, Sort::Int);
    let as_array = solver.as_array("replay_array_function", array_sort.clone());
    let source = solver.declare_const("replay_source_array", array_sort.clone());
    let mapped = solver.array_map("replay_array_function", &[source], array_sort.clone());
    let zero = solver.int_const(0);
    let as_array_value = solver.try_select(as_array, zero).expect("select as-array");
    let mapped_value = solver.try_select(mapped, zero).expect("select map");
    let values_equal = solver
        .try_eq(as_array_value, mapped_value)
        .expect("array values equal");
    solver.try_assert_term(values_equal).expect("assert");

    let details = solver.check_sat_with_details();
    let artifact =
        solver.export_native_replay_artifact(NativeReplayMetadata::default(), Some(&details));
    assert!(artifact
        .function_declarations
        .iter()
        .any(|declaration| declaration.name == "replay_array_function"));
    let replay = Solver::replay_native_replay_json_str(&artifact.to_pretty_json())
        .expect("higher-order array replay");
    assert_eq!(replay.result.result(), details.result.result());
}
