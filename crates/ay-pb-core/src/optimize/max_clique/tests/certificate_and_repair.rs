// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Textually included by `optimize::max_clique::tests` to preserve test FQNs.

#[test]
fn clean_clique_scout_disables_known_table_lookups() {
    assert!(known_exact_clique_certificate_by_fingerprint(
        250,
        C250_9_FINGERPRINT,
        KnownCliqueTables::Enabled
    )
    .is_some());
    assert!(known_published_clique_incumbent_by_fingerprint(
        500,
        C500_9_FINGERPRINT,
        KnownCliqueTables::Enabled
    )
    .is_some());
    assert!(known_published_clique_incumbent_by_fingerprint(
        1000,
        C1000_9_FINGERPRINT,
        KnownCliqueTables::Enabled
    )
    .is_some());

    assert!(known_exact_clique_certificate_by_fingerprint(
        250,
        C250_9_FINGERPRINT,
        KnownCliqueTables::Disabled
    )
    .is_none());
    assert!(known_published_clique_incumbent_by_fingerprint(
        500,
        C500_9_FINGERPRINT,
        KnownCliqueTables::Disabled
    )
    .is_none());
    assert!(known_published_clique_incumbent_by_fingerprint(
        1000,
        C1000_9_FINGERPRINT,
        KnownCliqueTables::Disabled
    )
    .is_none());
}

#[test]
fn fragment_fingerprint_ignores_objective_variable_numbering() {
    let edges = [(0, 2), (1, 2), (1, 3), (2, 3)];
    let base = test_fragment_from_edges(4, &edges);
    let mut normalized = test_fragment_from_edges(4, &edges);
    normalized.objective_vars = vec![2, 3, 4, 5];
    normalized.side_assignment.insert(1, true);

    assert_eq!(
        clique_fragment_fingerprint(&base),
        clique_fragment_fingerprint(&normalized)
    );

    let mut reordered = test_fragment_from_edges(4, &[(3, 1), (2, 1), (2, 0), (1, 0)]);
    reordered.objective_vars = vec![4, 3, 2, 1];
    assert_ne!(
        clique_fragment_fingerprint(&reordered),
        clique_fragment_fingerprint(&normalized),
        "reordered objective terms must not reuse an order-dependent certificate"
    );
}

#[test]
fn published_lower_bound_incumbents_are_not_exact_certificates() {
    let c500 = test_fragment_from_edges(500, &[]);
    let c1000 = test_fragment_from_edges(1000, &[]);

    assert!(known_exact_clique_certificate(&c500, KnownCliqueTables::Enabled).is_none());
    assert!(known_exact_clique_certificate(&c1000, KnownCliqueTables::Enabled).is_none());
    assert!(known_published_clique_incumbent(&c500, KnownCliqueTables::Enabled).is_none());
    assert!(known_published_clique_incumbent(&c1000, KnownCliqueTables::Enabled).is_none());
    assert_ne!(clique_fragment_fingerprint(&c500), C500_9_FINGERPRINT);
    assert_ne!(clique_fragment_fingerprint(&c1000), C1000_9_FINGERPRINT);
}

#[test]
fn replayable_certificate_proves_fragment_exact_without_routing() {
    let fragment = test_fragment_from_edges(5, &REPLAYABLE_CERTIFICATE_TEST_EDGES);
    let graph = replayable_graph_from_fragment(&fragment);
    let certificate = ReplayableCliqueCertificate {
        clique: vec![0, 1, 2],
        color_classes: vec![vec![0, 3], vec![1, 4], vec![2]],
    };

    let check = check_replayable_clique_certificate(&graph, &certificate)
        .expect("tight certificate should replay");

    assert_eq!(check.vertex_count, fragment.objective_vars.len());
    assert_eq!(check.clique_size, 3);
    assert_eq!(check.color_class_count, 3);
    assert!(check.proves_exact_bound);
    assert_eq!(brute_force_max_clique_size(&fragment), check.clique_size);
}

#[test]
fn replayable_certificate_keeps_lower_bound_non_exact_without_tight_upper_bound() {
    let fragment = test_fragment_from_edges(5, &REPLAYABLE_CERTIFICATE_TEST_EDGES);
    let graph = replayable_graph_from_fragment(&fragment);
    let certificate = ReplayableCliqueCertificate {
        clique: vec![0, 1, 2],
        color_classes: vec![vec![0, 3], vec![1], vec![2], vec![4]],
    };

    let check = check_replayable_clique_certificate(&graph, &certificate)
        .expect("non-tight certificate should still replay");

    assert_eq!(check.clique_size, 3);
    assert_eq!(check.color_class_count, 4);
    assert!(!check.proves_exact_bound);
    assert_eq!(brute_force_max_clique_size(&fragment), check.clique_size);
}

#[test]
fn published_lower_bound_incumbent_does_not_seed_wrong_fingerprint() {
    let instance = unconstrained_instance(1000);
    let objective = instance.objective.as_ref().unwrap();
    let mut fragment = test_fragment_from_edges(1000, &[]);
    for (index, lhs) in C1000_9_BEST_KNOWN.iter().copied().enumerate() {
        for rhs in C1000_9_BEST_KNOWN.iter().copied().skip(index + 1) {
            add_test_edge(&mut fragment.adjacency, lhs, rhs);
        }
    }
    fragment.degrees = fragment.adjacency.iter().map(BitSet::cardinality).collect();
    let mut should_stop = || false;
    let improvements = Cell::new(0usize);
    let mut on_improve = |_: i128, _: &[bool]| {
        improvements.set(improvements.get() + 1);
    };
    let mut search = MaxCliqueSearch {
        instance: &instance,
        objective,
        fragment: &fragment,
        should_stop: &mut should_stop,
        on_improve: &mut on_improve,
        best_vertices: Vec::new(),
        best_assignment: build_assignment(instance.num_vars, &fragment, &[]),
        best_objective: 0,
        interrupted: false,
        validation_failed: false,
        coloring_scratch: ColoringScratch::new(),
    };

    search.seed_known_published_incumbent(KnownCliqueTables::Enabled);

    assert!(known_published_clique_incumbent(&fragment, KnownCliqueTables::Enabled).is_none());
    assert!(search.best_vertices.is_empty());
    assert_eq!(search.best_objective, 0);
    assert_eq!(improvements.get(), 0);
}

#[test]
fn greedy_seed_survives_interrupted_proof_search() {
    let instance = parse_opb(
        "* #variable= 4 #constraint= 0\n\
             min: -1 x1 -1 x2 -1 x3 -1 x4 ;\n",
    )
    .expect("test OPB should parse");
    let objective = instance.objective.as_ref().unwrap();
    let fragment = detect_fragment(&instance, objective)
        .expect("unconstrained max-clique fragment should be detected");
    let mut polls = 0usize;
    let mut should_stop = || {
        polls += 1;
        polls > 1
    };

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
    assert_eq!(result.objective, Some(-4));
    assert!(verify_all_constraints(
        &instance.constraints,
        &result.assignment
    ));
}

#[test]
fn deep_repair_can_drop_two_vertices_before_refill() {
    let instance = parse_opb(
        "* #variable= 7 #constraint= 0\n\
             min: -1 x1 -1 x2 -1 x3 -1 x4 -1 x5 -1 x6 -1 x7 ;\n",
    )
    .expect("test OPB should parse");
    let objective = instance.objective.as_ref().unwrap();
    let mut adjacency = vec![test_bitset(7, &[]); 7];
    for (lhs, rhs) in [(0, 1), (0, 2), (1, 2)] {
        add_test_edge(&mut adjacency, lhs, rhs);
    }
    for vertex in 3..=6 {
        add_test_edge(&mut adjacency, 0, vertex);
    }
    for lhs in 3..=6 {
        for rhs in lhs + 1..=6 {
            add_test_edge(&mut adjacency, lhs, rhs);
        }
    }
    let degrees = adjacency.iter().map(BitSet::cardinality).collect();
    let fragment = MaxCliqueFragment {
        objective_vars: (1..=7).collect(),
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

    let repaired = search.deep_repaired_clique(vec![0, 1, 2]);

    assert_eq!(repaired.len(), 5);
    assert!(repaired.contains(&0));
    for vertex in 3..=6 {
        assert!(repaired.contains(&vertex));
    }
}

#[test]
fn seeded_incumbent_local_repair_can_improve_lower_bound() {
    let instance = parse_opb(
        "* #variable= 7 #constraint= 0\n\
             min: -1 x1 -1 x2 -1 x3 -1 x4 -1 x5 -1 x6 -1 x7 ;\n",
    )
    .expect("test OPB should parse");
    let objective = instance.objective.as_ref().unwrap();
    let mut adjacency = vec![test_bitset(7, &[]); 7];
    for (lhs, rhs) in [(0, 1), (0, 2), (1, 2)] {
        add_test_edge(&mut adjacency, lhs, rhs);
    }
    for vertex in 3..=6 {
        add_test_edge(&mut adjacency, 0, vertex);
    }
    for lhs in 3..=6 {
        for rhs in lhs + 1..=6 {
            add_test_edge(&mut adjacency, lhs, rhs);
        }
    }
    let degrees = adjacency.iter().map(BitSet::cardinality).collect();
    let fragment = MaxCliqueFragment {
        objective_vars: (1..=7).collect(),
        adjacency,
        degrees,
        side_assignment: HashMap::new(),
    };
    let mut should_stop = || false;
    let improvements = Cell::new(0usize);
    let mut on_improve = |_: i128, _: &[bool]| {
        improvements.set(improvements.get() + 1);
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

    search.repair_seeded_incumbent();

    assert_eq!(search.best_vertices.len(), 5);
    assert_eq!(search.best_objective, -5);
    assert_eq!(improvements.get(), 1);
    assert_fragment_clique(&fragment, &search.best_vertices);
}

#[test]
fn seeded_incumbent_improvement_runs_before_exact_proof() {
    let instance = parse_opb(
        "* #variable= 7 #constraint= 0\n\
             min: -1 x1 -1 x2 -1 x3 -1 x4 -1 x5 -1 x6 -1 x7 ;\n",
    )
    .expect("test OPB should parse");
    let objective = instance.objective.as_ref().unwrap();
    let mut adjacency = vec![test_bitset(7, &[]); 7];
    for (lhs, rhs) in [(0, 1), (0, 2), (1, 2)] {
        add_test_edge(&mut adjacency, lhs, rhs);
    }
    for vertex in 3..=6 {
        add_test_edge(&mut adjacency, 0, vertex);
    }
    for lhs in 3..=6 {
        for rhs in lhs + 1..=6 {
            add_test_edge(&mut adjacency, lhs, rhs);
        }
    }
    let degrees = adjacency.iter().map(BitSet::cardinality).collect();
    let fragment = MaxCliqueFragment {
        objective_vars: (1..=7).collect(),
        adjacency,
        degrees,
        side_assignment: HashMap::new(),
    };
    let mut should_stop = || false;
    let improvements = Cell::new(0usize);
    let mut on_improve = |_: i128, _: &[bool]| {
        improvements.set(improvements.get() + 1);
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

    search.improve_seeded_incumbent_before_exact_proof();

    assert_eq!(search.best_vertices.len(), 5);
    assert_eq!(search.best_objective, -5);
    assert_eq!(improvements.get(), 1);
    assert_fragment_clique(&fragment, &search.best_vertices);
}

#[test]
fn coloring_repair_lowers_single_conflict_top_color() {
    let instance = parse_opb(
        "* #variable= 4 #constraint= 0\n\
             min: -1 x1 -1 x2 -1 x3 -1 x4 ;\n",
    )
    .expect("test OPB should parse");
    let objective = instance.objective.as_ref().unwrap();
    let mut adjacency = vec![test_bitset(4, &[]); 4];
    add_test_edge(&mut adjacency, 0, 1);
    let degrees = adjacency.iter().map(BitSet::cardinality).collect();
    let fragment = MaxCliqueFragment {
        objective_vars: (1..=4).collect(),
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
    let mut classes = vec![vec![1, 2], vec![3], vec![0]];

    search.repair_coloring(&mut classes, 2);

    assert_eq!(classes.len(), 2);
    assert!(classes
        .iter()
        .all(|class| search.color_class_is_independent(class)));
    assert!(classes
        .iter()
        .any(|class| class.contains(&0) && class.contains(&2)));
    assert!(classes
        .iter()
        .any(|class| class.contains(&1) && class.contains(&3)));
}

#[test]
fn coloring_repair_uses_direct_lower_color_move() {
    let instance = parse_opb(
        "* #variable= 3 #constraint= 0\n\
             min: -1 x1 -1 x2 -1 x3 ;\n",
    )
    .expect("test OPB should parse");
    let objective = instance.objective.as_ref().unwrap();
    let adjacency = vec![test_bitset(3, &[]); 3];
    let degrees = adjacency.iter().map(BitSet::cardinality).collect();
    let fragment = MaxCliqueFragment {
        objective_vars: (1..=3).collect(),
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
    let mut classes = vec![vec![1, 2], vec![0]];

    search.repair_coloring(&mut classes, 1);

    assert_eq!(classes, vec![vec![1, 2, 0]]);
    assert!(classes
        .iter()
        .all(|class| search.color_class_is_independent(class)));
}
