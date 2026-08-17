// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Textually included by `optimize::max_clique::tests` to preserve test FQNs.

#[test]
fn replayable_frontier_export_legacy_keeps_raw_frontier_shape() {
    let frontier = ReplayableCliqueBbPartialFrontier {
        target_size: 3,
        root: CliqueBbPartialFrontierNode {
            candidates: vec![0, 1, 2],
            proof: CliqueBbPartialFrontierProof::OpenObligation {},
        },
    };
    let target = test_frontier_import_target(3, 0x1234, 3);
    let mut json = Vec::new();

    write_legacy_replayable_frontier_json(&mut json, &frontier)
        .expect("legacy frontier should serialize");
    let value: serde_json::Value =
        serde_json::from_slice(&json).expect("legacy frontier should parse");
    assert!(value.get("metadata").is_none());
    assert!(value.get("frontier").is_none());

    let import: ReplayableCliqueFrontierImport =
        serde_json::from_slice(&json).expect("legacy import should parse");
    assert_eq!(
        resolve_replayable_frontier_import(import, target, false),
        Err(ReplayableCliqueFrontierImportReject::MissingMetadata)
    );

    let import: ReplayableCliqueFrontierImport =
        serde_json::from_slice(&json).expect("legacy import should parse");
    assert_eq!(
        resolve_replayable_frontier_import(import, target, true),
        Ok(frontier)
    );
}

#[test]
fn replayable_frontier_import_targets_include_c1000_no69() {
    let c500 = clique_frontier_import_target_by_fingerprint(500, C500_9_FINGERPRINT)
        .expect("C500 no58 import target should be registered");
    let c1000 = clique_frontier_import_target_by_fingerprint(1000, C1000_9_FINGERPRINT)
        .expect("C1000 no69 import target should be registered");

    assert_eq!(c500.target_size, C500_NO58_TARGET_SIZE);
    assert_eq!(c500.incumbent_size, C500_NO58_INCUMBENT_SIZE);
    assert_eq!(c500.incumbent.len(), C500_NO58_INCUMBENT_SIZE);
    assert_eq!(c1000.target_size, C1000_NO69_TARGET_SIZE);
    assert_eq!(c1000.incumbent_size, C1000_NO69_INCUMBENT_SIZE);
    assert_eq!(c1000.incumbent.len(), C1000_NO69_INCUMBENT_SIZE);
}

#[test]
fn replayable_frontier_import_accepts_generalized_metadata() {
    let fragment = test_fragment_from_edges(5, &[(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]);
    let graph = replayable_graph_from_fragment(&fragment);
    let mut should_stop = || false;
    let mut builder = CliquePartialFrontierBuilder::new(&fragment, &mut should_stop, 10_000, 8);
    let frontier = builder
        .build(3, &BitSet::full(5))
        .expect("cycle no-triangle frontier should close");
    let target = test_frontier_import_target(5, 0x0123_4567_89ab_cdef, 3);
    let import: ReplayableCliqueFrontierImport =
        serde_json::from_value(replayable_frontier_artifact_json(target, &frontier))
            .expect("metadata artifact should parse");

    let resolved = resolve_replayable_frontier_import(import, target, false)
        .expect("matching metadata should accept");
    let check = check_replayable_clique_bb_partial_frontier(&graph, &resolved)
        .expect("accepted frontier should still replay");

    assert_eq!(resolved, frontier);
    assert_eq!(check.open_obligations, 0);
    assert!(check.proves_no_target_clique);
}

#[test]
fn replayable_frontier_import_rejects_mismatched_target_and_fingerprint() {
    let frontier = ReplayableCliqueBbPartialFrontier {
        target_size: 3,
        root: CliqueBbPartialFrontierNode {
            candidates: vec![0, 1, 2],
            proof: CliqueBbPartialFrontierProof::OpenObligation {},
        },
    };
    let target = test_frontier_import_target(3, 0xfeed_beef, 3);

    let mut wrong_target = replayable_frontier_artifact_json(target, &frontier);
    wrong_target["metadata"]["target_size"] = serde_json::json!(4);
    let import: ReplayableCliqueFrontierImport =
        serde_json::from_value(wrong_target).expect("wrong-target artifact should parse");
    assert_eq!(
        resolve_replayable_frontier_import(import, target, false),
        Err(ReplayableCliqueFrontierImportReject::WrongTarget)
    );

    let mut wrong_fingerprint = replayable_frontier_artifact_json(target, &frontier);
    wrong_fingerprint["metadata"]["graph_fingerprint"] = serde_json::json!("0xfeed_beee");
    let import: ReplayableCliqueFrontierImport =
        serde_json::from_value(wrong_fingerprint).expect("wrong-fingerprint artifact should parse");
    assert_eq!(
        resolve_replayable_frontier_import(import, target, false),
        Err(ReplayableCliqueFrontierImportReject::WrongFingerprint)
    );
}

#[test]
fn replayable_frontier_import_rejects_raw_frontier_without_legacy_path() {
    let frontier = ReplayableCliqueBbPartialFrontier {
        target_size: 3,
        root: CliqueBbPartialFrontierNode {
            candidates: vec![0, 1, 2],
            proof: CliqueBbPartialFrontierProof::OpenObligation {},
        },
    };
    let target = test_frontier_import_target(3, 0x1234, 3);
    let import = ReplayableCliqueFrontierImport::LegacyFrontier(frontier.clone());

    assert_eq!(
        resolve_replayable_frontier_import(import, target, false),
        Err(ReplayableCliqueFrontierImportReject::MissingMetadata)
    );
    assert_eq!(
        resolve_replayable_frontier_import(
            ReplayableCliqueFrontierImport::LegacyFrontier(frontier.clone()),
            target,
            true,
        ),
        Ok(frontier)
    );
}

#[test]
fn replayable_frontier_import_rejects_invalid_incumbent_after_closed_replay() {
    let instance = unconstrained_instance(2);
    let objective = instance.objective.as_ref().expect("test objective");
    let fragment = test_fragment_from_edges(2, &[]);
    let mut should_stop = || false;
    let mut on_improve = |_objective: i128, _assignment: &[bool]| {};
    let initial_assignment = build_assignment(instance.num_vars, &fragment, &[]);
    let initial_objective = validate_assignment(&instance, objective, &initial_assignment)
        .expect("initial assignment should validate");
    let mut search = MaxCliqueSearch {
        instance: &instance,
        objective,
        fragment: &fragment,
        should_stop: &mut should_stop,
        on_improve: &mut on_improve,
        best_vertices: Vec::new(),
        best_assignment: initial_assignment,
        best_objective: initial_objective,
        interrupted: false,
        validation_failed: false,
        coloring_scratch: ColoringScratch::new(),
    };
    let target = test_frontier_import_target(2, 0x9876, 2);

    assert!(
        search.seed_validated_frontier_incumbent(target).is_none(),
        "a closed frontier must still fail closed when the target incumbent is not a clique"
    );
    assert!(search.best_vertices.is_empty());
}

#[test]
fn interrupted_search_returns_satisfiable_incumbent() {
    let instance = parse_opb(
        "* #variable= 3 #constraint= 0\n\
             min: -1 x1 -1 x2 -1 x3 ;\n",
    )
    .expect("test OPB should parse");
    let objective = instance.objective.as_ref().unwrap();
    let fragment = detect_fragment(&instance, objective)
        .expect("unconstrained max-clique fragment should be detected");
    let mut should_stop = || true;

    let result = solve_detected_max_clique(
        &instance,
        objective,
        &fragment,
        &mut should_stop,
        &mut |_, _| {},
        &mut PublishedCliqueExactModeStats::default(),
    )
    .expect("detected fragment should return a validated incumbent");

    assert_eq!(result.status, PbStatus::Satisfiable);
    assert_eq!(result.objective, Some(0));
    assert!(verify_all_constraints(
        &instance.constraints,
        &result.assignment
    ));
}

#[test]
fn semantic_validation_failure_downgrades_exhaustive_claim() {
    let instance = parse_opb(
        "* #variable= 2 #constraint= 1\n\
             min: -1 x1 -1 x2 ;\n\
             -1 x1 -1 x2 >= -1 ;\n",
    )
    .expect("test OPB should parse");
    let objective = instance.objective.as_ref().unwrap();
    let mut fragment =
        detect_fragment(&instance, objective).expect("base fragment should be detected");
    fragment.adjacency[0].insert(1);
    fragment.adjacency[1].insert(0);

    let mut should_stop = || false;
    let result = solve_detected_max_clique(
        &instance,
        objective,
        &fragment,
        &mut should_stop,
        &mut |_, _| {},
        &mut PublishedCliqueExactModeStats::default(),
    )
    .expect("invalid search graph should still return the validated incumbent");

    assert_eq!(result.status, PbStatus::Satisfiable);
    assert_eq!(result.objective, Some(-1));
    assert!(verify_all_constraints(
        &instance.constraints,
        &result.assignment
    ));
}
