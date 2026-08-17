// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Textually included by `optimize::max_clique::tests` to preserve test FQNs.

#[test]
fn decision_search_proves_repairable_cycle_no_triangle() {
    let instance = unconstrained_instance(6);
    let objective = instance.objective.as_ref().unwrap();
    let fragment = test_fragment_from_edges(6, &REPAIRABLE_SIX_CYCLE_EDGES);
    let mut should_stop = || false;
    let mut on_improve = |_: i128, _: &[bool]| {};
    let mut search = MaxCliqueSearch {
        instance: &instance,
        objective,
        fragment: &fragment,
        should_stop: &mut should_stop,
        on_improve: &mut on_improve,
        best_vertices: vec![0, 4],
        best_assignment: build_assignment(instance.num_vars, &fragment, &[0, 4]),
        best_objective: -2,
        interrupted: false,
        validation_failed: false,
        coloring_scratch: ColoringScratch::new(),
    };
    let candidates = BitSet::full(6);
    let root_key = candidates.words.clone();
    let mut no_clique_cache = HashMap::new();

    let result = search.decide_clique_of_size(3, &candidates, &mut no_clique_cache);

    assert_eq!(result, DecisionSearchResult::NoClique);
    assert_eq!(search.best_vertices, vec![0, 4]);
    assert_eq!(search.best_objective, -2);
    assert_eq!(no_clique_cache.get(&root_key), Some(&3));
}

#[test]
fn k_plus_one_decision_finalizer_proves_absent_large_fragment() {
    let num_vars = DECISION_FINALIZER_MIN_OBJECTIVE_VARS;
    let mut input = format!("* #variable= {num_vars} #constraint= 0\nmin:");
    for var in 1..=num_vars {
        input.push_str(&format!(" -1 x{var}"));
    }
    input.push_str(" ;\n");
    let instance = parse_opb(&input).expect("test OPB should parse");
    let objective = instance.objective.as_ref().unwrap();

    let mut adjacency = vec![test_bitset(num_vars, &[]); num_vars];
    for lhs in 0..3 {
        for rhs in lhs + 1..3 {
            add_test_edge(&mut adjacency, lhs, rhs);
        }
    }
    for lhs in 3..num_vars {
        for rhs in lhs + 1..num_vars {
            add_test_edge(&mut adjacency, lhs, rhs);
        }
    }
    let degrees = adjacency.iter().map(BitSet::cardinality).collect();
    let fragment = MaxCliqueFragment {
        objective_vars: (1..=num_vars as u32).collect(),
        adjacency,
        degrees,
        side_assignment: HashMap::new(),
    };
    let mut should_stop = || false;
    let mut improvements = 0usize;
    let mut on_improve = |_: i128, _: &[bool]| {
        improvements += 1;
    };
    let mut search = MaxCliqueSearch {
        instance: &instance,
        objective,
        fragment: &fragment,
        should_stop: &mut should_stop,
        on_improve: &mut on_improve,
        best_vertices: (3..num_vars).collect(),
        best_assignment: Vec::new(),
        best_objective: 0,
        interrupted: false,
        validation_failed: false,
        coloring_scratch: ColoringScratch::new(),
    };

    let result = search.finalize_k_plus_one_decision(&BitSet::full(num_vars));

    assert_eq!(result, DecisionSearchResult::NoClique);
    assert_eq!(search.best_vertices.len(), num_vars - 3);
    assert_eq!(improvements, 0);
}

#[test]
fn k_plus_one_decision_finalizer_records_found_clique() {
    let num_vars = DECISION_FINALIZER_MIN_OBJECTIVE_VARS;
    let mut input = format!("* #variable= {num_vars} #constraint= 0\nmin:");
    for var in 1..=num_vars {
        input.push_str(&format!(" -1 x{var}"));
    }
    input.push_str(" ;\n");
    let instance = parse_opb(&input).expect("test OPB should parse");
    let objective = instance.objective.as_ref().unwrap();

    let mut adjacency = vec![test_bitset(num_vars, &[]); num_vars];
    for lhs in 0..4 {
        for rhs in lhs + 1..4 {
            add_test_edge(&mut adjacency, lhs, rhs);
        }
    }
    let degrees = adjacency.iter().map(BitSet::cardinality).collect();
    let fragment = MaxCliqueFragment {
        objective_vars: (1..=num_vars as u32).collect(),
        adjacency,
        degrees,
        side_assignment: HashMap::new(),
    };
    let mut should_stop = || false;
    let mut improvements = 0usize;
    let mut on_improve = |_: i128, _: &[bool]| {
        improvements += 1;
    };
    let mut search = MaxCliqueSearch {
        instance: &instance,
        objective,
        fragment: &fragment,
        should_stop: &mut should_stop,
        on_improve: &mut on_improve,
        best_vertices: vec![0, 1, 2],
        best_assignment: build_assignment(instance.num_vars, &fragment, &[0, 1, 2]),
        best_objective: -3,
        interrupted: false,
        validation_failed: false,
        coloring_scratch: ColoringScratch::new(),
    };

    let result = search.finalize_k_plus_one_decision(&BitSet::full(num_vars));

    assert_eq!(result, DecisionSearchResult::NoClique);
    assert_eq!(search.best_vertices.len(), 4);
    assert_eq!(search.best_objective, -4);
    assert_eq!(improvements, 1);
}

#[test]
fn bounded_k_plus_one_finalizer_is_not_exact_at_node_limit() {
    let num_vars = DECISION_FINALIZER_MIN_OBJECTIVE_VARS;
    let instance = unconstrained_instance(num_vars);
    let objective = instance.objective.as_ref().unwrap();
    let fragment = test_fragment_from_edges(num_vars, &[(0, 1), (0, 2), (1, 2)]);
    let mut should_stop = || false;
    let mut on_improve = |_: i128, _: &[bool]| {};
    let mut search = MaxCliqueSearch {
        instance: &instance,
        objective,
        fragment: &fragment,
        should_stop: &mut should_stop,
        on_improve: &mut on_improve,
        best_vertices: vec![0, 1],
        best_assignment: build_assignment(instance.num_vars, &fragment, &[0, 1]),
        best_objective: -2,
        interrupted: false,
        validation_failed: false,
        coloring_scratch: ColoringScratch::new(),
    };

    let result =
        search.finalize_k_plus_one_decision_with_node_limit(&BitSet::full(num_vars), Some(0));

    assert_eq!(result, DecisionSearchResult::Interrupted);
    assert_eq!(search.best_vertices, vec![0, 1]);
    assert_eq!(search.best_objective, -2);
    assert!(!search.interrupted);
    assert!(!search.validation_failed);
}

#[test]
fn decision_pruning_removes_vertices_below_target_core() {
    let instance = parse_opb(
        "* #variable= 5 #constraint= 0\n\
             min: -1 x1 -1 x2 -1 x3 -1 x4 -1 x5 ;\n",
    )
    .expect("test OPB should parse");
    let objective = instance.objective.as_ref().unwrap();
    let mut adjacency = vec![test_bitset(5, &[]); 5];
    for (lhs, rhs) in [(0, 1), (1, 2), (3, 4)] {
        add_test_edge(&mut adjacency, lhs, rhs);
    }
    let degrees = adjacency.iter().map(BitSet::cardinality).collect();
    let fragment = MaxCliqueFragment {
        objective_vars: (1..=5).collect(),
        adjacency,
        degrees,
        side_assignment: HashMap::new(),
    };
    let mut should_stop = || false;
    let mut on_improve = |_: i128, _: &[bool]| {};
    let mut search = MaxCliqueSearch {
        instance: &instance,
        objective,
        fragment: &fragment,
        should_stop: &mut should_stop,
        on_improve: &mut on_improve,
        best_vertices: Vec::new(),
        best_assignment: Vec::new(),
        best_objective: 0,
        interrupted: false,
        validation_failed: false,
        coloring_scratch: ColoringScratch::new(),
    };
    let mut candidates = BitSet::full(5);

    assert!(search.prune_decision_candidates(3, &mut candidates));

    assert!(candidates.cardinality() < 3);
    assert!(!candidates.contains(0));
    assert!(!candidates.contains(2));
    assert!(!candidates.contains(3));
    assert!(!candidates.contains(4));
}

#[test]
fn decision_core_prune_trace_emits_replayable_transcript() {
    let fragment = test_fragment_from_edges(5, &[(0, 1), (1, 2), (3, 4)]);
    let graph = replayable_graph_from_fragment(&fragment);
    let mut should_stop = || false;
    let mut interrupted = false;
    let mut no_clique_cache = HashMap::new();
    let mut stats = DecisionSearchStats::new(3);
    let mut prover = CliqueNoKPlusOneProver::new(
        &fragment,
        &mut should_stop,
        &mut interrupted,
        &mut no_clique_cache,
        &mut stats,
    );
    let mut candidates = BitSet::full(5);
    let root_candidates = bitset_vertices(&candidates);
    let mut pruned_vertices = Vec::new();

    assert!(prover.prune_candidates_with_trace(3, &mut candidates, Some(&mut pruned_vertices)));

    let child_candidates = bitset_vertices(&candidates);
    assert_eq!(pruned_vertices, vec![0, 2, 3, 4]);
    assert_eq!(child_candidates, vec![1]);

    let transcript = ReplayableCliqueBbTranscript {
        target_size: 3,
        root: CliqueBbNodeTranscript {
            candidates: root_candidates,
            proof: CliqueBbNodeProof::DegreeCorePrune {
                pruned_vertices,
                child: Box::new(CliqueBbNodeTranscript {
                    candidates: child_candidates,
                    proof: CliqueBbNodeProof::CardinalityPrune {},
                }),
            },
        },
    };
    let check = check_replayable_clique_bb_transcript(&graph, &transcript)
        .expect("emitted degree-core transcript should replay");

    assert_eq!(check.visited_nodes, 2);
    assert_eq!(check.degree_core_prunes, 1);
    assert_eq!(check.degree_core_pruned_vertices, 4);
    assert_eq!(check.cardinality_prunes, 1);
    assert!(!interrupted);
}

#[test]
fn partial_frontier_builder_leaves_explicit_open_obligation_at_node_limit() {
    let fragment = test_fragment_from_edges(5, &REPLAYABLE_CERTIFICATE_TEST_EDGES);
    let graph = replayable_graph_from_fragment(&fragment);
    let mut should_stop = || false;
    let mut builder = CliquePartialFrontierBuilder::new(&fragment, &mut should_stop, 0, 1);

    let frontier = builder
        .build(4, &BitSet::full(5))
        .expect("open root frontier should be representable");
    let check = check_replayable_clique_bb_partial_frontier(&graph, &frontier)
        .expect("open frontier should replay");

    assert_eq!(frontier.target_size, 4);
    assert_eq!(check.open_obligations, 1);
    assert!(!check.proves_no_target_clique);
}

#[test]
fn partial_frontier_builder_can_close_small_absent_target() {
    let fragment = test_fragment_from_edges(5, &[(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]);
    let graph = replayable_graph_from_fragment(&fragment);
    let mut should_stop = || false;
    let mut builder = CliquePartialFrontierBuilder::new(&fragment, &mut should_stop, 10_000, 8);

    let frontier = builder
        .build(3, &BitSet::full(5))
        .expect("cycle no-triangle frontier should close");
    let check = check_replayable_clique_bb_partial_frontier(&graph, &frontier)
        .expect("closed frontier should replay");

    assert_eq!(check.target_size, 3);
    assert_eq!(check.open_obligations, 0);
    assert!(check.proves_no_target_clique);
}

#[test]
fn partial_frontier_json_uses_checker_compatible_empty_variant_objects() {
    let frontier = ReplayableCliqueBbPartialFrontier {
        target_size: 3,
        root: CliqueBbPartialFrontierNode {
            candidates: vec![0, 1, 2],
            proof: CliqueBbPartialFrontierProof::OpenObligation {},
        },
    };

    let json = serde_json::to_string(&frontier).expect("frontier should serialize as JSON");
    assert!(json.contains(r#""OpenObligation":{}"#));

    let parsed: ReplayableCliqueBbPartialFrontier =
        serde_json::from_str(&json).expect("serialized frontier should parse");
    assert_eq!(parsed, frontier);
}

#[test]
fn clique_frontier_export_path_values_are_default_off_and_independent() {
    let none = clique_frontier_export_paths_from_env_values(None, None);
    assert!(none.is_empty());
    assert!(!clique_frontier_export_requested_from_env_values(
        None, None
    ));

    let general = OsStr::new("frontier.json");
    let legacy = OsStr::new("c500-frontier.json");
    let both = clique_frontier_export_paths_from_env_values(Some(general), Some(legacy));
    assert_eq!(both.general_artifact, Some(OsString::from(general)));
    assert_eq!(both.legacy_c500_raw, Some(OsString::from(legacy)));
    assert!(!both.is_empty());
    assert!(clique_frontier_export_requested_from_env_values(
        Some(general),
        Some(legacy)
    ));

    let legacy_only = clique_frontier_export_paths_from_env_values(None, Some(legacy));
    assert_eq!(legacy_only.general_artifact, None);
    assert_eq!(legacy_only.legacy_c500_raw, Some(OsString::from(legacy)));
}

#[test]
fn replayable_frontier_export_general_writes_metadata_artifact() {
    let frontier = ReplayableCliqueBbPartialFrontier {
        target_size: 3,
        root: CliqueBbPartialFrontierNode {
            candidates: vec![0, 1, 2],
            proof: CliqueBbPartialFrontierProof::OpenObligation {},
        },
    };
    let target = test_frontier_import_target(3, 0x0123_4567_89ab_cdef, 3);
    let mut json = Vec::new();

    write_replayable_frontier_artifact_json(&mut json, target, &frontier)
        .expect("general frontier artifact should serialize");
    let value: serde_json::Value =
        serde_json::from_slice(&json).expect("general artifact should parse");

    assert_eq!(
        value["format"],
        serde_json::json!(REPLAYABLE_CLIQUE_FRONTIER_FORMAT)
    );
    assert_eq!(
        value["metadata"]["benchmark"],
        serde_json::json!(target.name)
    );
    assert_eq!(value["metadata"]["vertex_count"], serde_json::json!(3));
    assert_eq!(
        value["metadata"]["graph_fingerprint"],
        serde_json::json!("0x0123456789abcdef")
    );
    assert_eq!(value["metadata"]["target_size"], serde_json::json!(3));
    assert_eq!(
        value["metadata"]["incumbent_size"],
        serde_json::json!(TEST_FRONTIER_INCUMBENT.len())
    );
    assert!(value.get("frontier").is_some());
}

#[test]
fn replayable_frontier_export_general_round_trips_through_general_import() {
    let fragment = test_fragment_from_edges(5, &[(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]);
    let graph = replayable_graph_from_fragment(&fragment);
    let mut should_stop = || false;
    let mut builder = CliquePartialFrontierBuilder::new(&fragment, &mut should_stop, 10_000, 8);
    let frontier = builder
        .build(3, &BitSet::full(5))
        .expect("cycle no-triangle frontier should close");
    let target = test_frontier_import_target(5, 0x0123_4567_89ab_cdef, 3);
    let mut json = Vec::new();

    write_replayable_frontier_artifact_json(&mut json, target, &frontier)
        .expect("general frontier artifact should serialize");
    let import: ReplayableCliqueFrontierImport =
        serde_json::from_slice(&json).expect("general artifact should parse");
    let resolved = resolve_replayable_frontier_import(import, target, false)
        .expect("matching metadata should accept");
    let check = check_replayable_clique_bb_partial_frontier(&graph, &resolved)
        .expect("accepted frontier should still replay");

    assert_eq!(resolved, frontier);
    assert_eq!(check.open_obligations, 0);
    assert!(check.proves_no_target_clique);
}
