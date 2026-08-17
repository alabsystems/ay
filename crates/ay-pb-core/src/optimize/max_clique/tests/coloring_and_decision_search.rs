// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Textually included by `optimize::max_clique::tests` to preserve test FQNs.

#[test]
fn low_degree_pruning_removes_vertices_that_cannot_improve_incumbent() {
    let instance = parse_opb(
        "* #variable= 6 #constraint= 0\n\
             min: -1 x1 -1 x2 -1 x3 -1 x4 -1 x5 -1 x6 ;\n",
    )
    .expect("test OPB should parse");
    let objective = instance.objective.as_ref().unwrap();
    let mut adjacency = vec![test_bitset(6, &[]); 6];
    for lhs in 0..4 {
        for rhs in lhs + 1..4 {
            add_test_edge(&mut adjacency, lhs, rhs);
        }
    }
    add_test_edge(&mut adjacency, 4, 0);
    add_test_edge(&mut adjacency, 5, 1);
    let degrees = adjacency.iter().map(BitSet::cardinality).collect();
    let fragment = MaxCliqueFragment {
        objective_vars: (1..=6).collect(),
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
        best_vertices: vec![0, 1, 2, 3],
        best_assignment: Vec::new(),
        best_objective: 0,
        interrupted: false,
        validation_failed: false,
        coloring_scratch: ColoringScratch::new(),
    };
    let mut candidates = BitSet::full(6);

    assert!(search.branch_cannot_improve(0, &candidates, 4));
    assert!(!search.branch_cannot_improve(0, &candidates, 0));

    search.prune_low_degree_candidates(0, &mut candidates);

    assert!(candidates.cardinality() < 5);
    assert!(!candidates.contains(2));
    assert!(!candidates.contains(3));
}

#[test]
fn color_sort_uses_residual_degree_for_tighter_bound() {
    let instance = parse_opb(
        "* #variable= 6 #constraint= 0\n\
             min: -1 x1 -1 x2 -1 x3 -1 x4 -1 x5 -1 x6 ;\n",
    )
    .expect("test OPB should parse");
    let objective = instance.objective.as_ref().unwrap();
    let mut adjacency = vec![test_bitset(6, &[]); 6];
    for (lhs, rhs) in [
        (0, 1),
        (0, 3),
        (0, 4),
        (1, 2),
        (2, 4),
        (2, 5),
        (3, 4),
        (3, 5),
        (4, 5),
    ] {
        add_test_edge(&mut adjacency, lhs, rhs);
    }
    let degrees = adjacency.iter().map(BitSet::cardinality).collect();
    let fragment = MaxCliqueFragment {
        objective_vars: (1..=6).collect(),
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

    let (_, colors) = search
        .color_sort(&BitSet::full(6), 3)
        .expect("coloring should finish");

    assert_eq!(colors.iter().copied().max(), Some(3));
}

#[test]
fn color_sort_returns_exact_order_and_color_bounds() {
    let instance = unconstrained_instance(6);
    let objective = instance.objective.as_ref().unwrap();
    let fragment = test_fragment_from_edges(
        6,
        &[
            (0, 1),
            (0, 3),
            (0, 4),
            (1, 2),
            (2, 4),
            (2, 5),
            (3, 4),
            (3, 5),
            (4, 5),
        ],
    );
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

    let (order, colors) = search
        .color_sort(&BitSet::full(6), 3)
        .expect("coloring should finish");
    let branch_order = order.iter().rev().copied().collect::<Vec<_>>();

    assert_eq!(order, vec![4, 1, 3, 2, 0, 5]);
    assert_eq!(colors, vec![1, 1, 2, 2, 3, 3]);
    assert_eq!(branch_order, vec![5, 0, 2, 3, 1, 4]);
}

#[test]
fn decision_color_sort_targets_absent_bound() {
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
        best_vertices: Vec::new(),
        best_assignment: Vec::new(),
        best_objective: 0,
        interrupted: false,
        validation_failed: false,
        coloring_scratch: ColoringScratch::new(),
    };
    let candidates = BitSet::full(6);

    let (_, plain_colors) = search
        .color_sort(&candidates, 3)
        .expect("plain coloring should finish");
    let (_, decision_colors) = search
        .decision_color_sort(&candidates, 3)
        .expect("decision coloring should finish");

    assert_eq!(plain_colors.iter().copied().max(), Some(3));
    assert_eq!(decision_colors.iter().copied().max(), Some(2));
}

#[test]
fn inherited_colored_bound_uses_highest_remaining_color() {
    let order = ColoredOrder {
        vertices: vec![4, 1, 3, 2, 0],
        bounds: vec![1, 1, 2, 2, 3],
        covered: test_bitset(6, &[0, 1, 2, 3, 4]),
    };
    let high = test_bitset(6, &[4, 3, 0]);
    let low = test_bitset(6, &[4, 1]);
    let empty = test_bitset(6, &[]);
    let unknown = test_bitset(6, &[4, 5]);

    assert_eq!(order.max_bound_for_subset(&high), 3);
    assert_eq!(order.max_bound_for_subset(&low), 1);
    assert_eq!(order.max_bound_for_subset(&empty), 0);
    assert_eq!(order.max_bound_for_subset(&unknown), 3);
}

#[test]
fn no_k_plus_one_prover_matches_all_graphs_up_to_six_vertices() {
    for num_vertices in 1..=6 {
        let possible_edges = (0..num_vertices)
            .flat_map(|lhs| (lhs + 1..num_vertices).map(move |rhs| (lhs, rhs)))
            .collect::<Vec<_>>();

        for edge_mask in 0usize..(1usize << possible_edges.len()) {
            let edges = possible_edges
                .iter()
                .copied()
                .enumerate()
                .filter_map(|(bit, edge)| ((edge_mask & (1usize << bit)) != 0).then_some(edge))
                .collect::<Vec<_>>();
            let fragment = test_fragment_from_edges(num_vertices, &edges);
            let candidates = BitSet::full(num_vertices);

            for target_size in 1..=num_vertices + 1 {
                let expected = brute_force_has_clique(&fragment, target_size);
                let mut should_stop = || false;
                let mut interrupted = false;
                let mut no_clique_cache = HashMap::new();
                let mut stats = DecisionSearchStats::new(target_size);
                let mut prover = CliqueNoKPlusOneProver::new(
                    &fragment,
                    &mut should_stop,
                    &mut interrupted,
                    &mut no_clique_cache,
                    &mut stats,
                );

                let outcome = prover.prove(target_size, &candidates);

                match (expected, outcome) {
                        (true, CliqueProofOutcome::FoundClique(clique)) => {
                            assert_eq!(clique.len(), target_size);
                            assert_fragment_clique(&fragment, &clique);
                        }
                        (false, CliqueProofOutcome::NoClique) => {}
                        (expected, actual) => panic!(
                            "n={num_vertices} edge_mask={edge_mask:#x} target={target_size} expected clique={expected}, got {actual:?}"
                        ),
                    }
                assert!(!interrupted);
                assert!(!stats.interrupted);
            }
        }
    }
}

#[test]
fn branch_local_coloring_is_valid_after_repair() {
    let fragment = test_fragment_from_edges(6, &REPAIRABLE_SIX_CYCLE_EDGES);
    let candidates = BitSet::full(6);
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

    let color_count = prover
        .branch_local_color_count(&candidates, 3)
        .expect("branch-local coloring should finish");

    assert_eq!(color_count, 2);
    assert!(color_classes_cover_candidates_once(
        &fragment.adjacency,
        &candidates,
        &prover.coloring_scratch.classes
    ));
    assert!(!interrupted);
}

#[test]
fn decision_search_finds_target_clique_and_records_incumbent() {
    let instance = unconstrained_instance(6);
    let objective = instance.objective.as_ref().unwrap();
    let fragment = test_fragment_from_edges(6, &[(0, 1), (0, 2), (1, 2), (2, 3), (3, 4), (4, 5)]);
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
    let mut no_clique_cache = HashMap::new();

    let result = search.decide_clique_of_size(3, &BitSet::full(6), &mut no_clique_cache);

    assert_eq!(result, DecisionSearchResult::FoundClique);
    assert_eq!(search.best_vertices.len(), 3);
    assert_eq!(search.best_objective, -3);
    assert_eq!(improvements.get(), 1);
    assert_fragment_clique(&fragment, &search.best_vertices);
}

#[test]
fn decision_search_proves_odd_cycle_has_no_triangle() {
    let instance = unconstrained_instance(5);
    let objective = instance.objective.as_ref().unwrap();
    let fragment = test_fragment_from_edges(5, &[(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]);
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
    let candidates = BitSet::full(5);
    let root_key = candidates.words.clone();
    let mut no_clique_cache = HashMap::new();

    let result = search.decide_clique_of_size(3, &candidates, &mut no_clique_cache);

    assert_eq!(result, DecisionSearchResult::NoClique);
    assert_eq!(search.best_vertices, vec![0, 1]);
    assert_eq!(search.best_objective, -2);
    assert_eq!(no_clique_cache.get(&root_key), Some(&3));
}

#[test]
fn decision_search_stats_count_prunes_and_cache_hits() {
    let instance = unconstrained_instance(5);
    let objective = instance.objective.as_ref().unwrap();
    let fragment = test_fragment_from_edges(5, &[(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]);
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
    let candidates = BitSet::full(5);
    let mut no_clique_cache = HashMap::new();
    let mut first_stats = DecisionSearchStats::new(3);

    let first_result = search.decide_clique_of_size_with_stats(
        3,
        &candidates,
        &mut no_clique_cache,
        &mut first_stats,
    );

    assert_eq!(first_result, DecisionSearchResult::NoClique);
    assert_eq!(first_stats.target_size, 3);
    assert_eq!(first_stats.nodes_visited, 1);
    assert!(first_stats.color_prunes > 0);
    assert_eq!(first_stats.max_depth, 0);
    assert!(!first_stats.interrupted);

    let mut second_stats = DecisionSearchStats::new(3);
    let second_result = search.decide_clique_of_size_with_stats(
        3,
        &candidates,
        &mut no_clique_cache,
        &mut second_stats,
    );

    assert_eq!(second_result, DecisionSearchResult::NoClique);
    assert_eq!(second_stats.nodes_visited, 1);
    assert_eq!(second_stats.cache_hits, 1);
    assert_eq!(second_stats.max_depth, 0);
    assert_eq!(second_stats.color_prunes, 0);
    assert!(!second_stats.interrupted);
}

#[test]
fn decision_no_clique_cache_is_monotone_by_target_size() {
    let instance = unconstrained_instance(6);
    let objective = instance.objective.as_ref().unwrap();
    let fragment = test_fragment_from_edges(
        6,
        &[
            (0, 3),
            (0, 4),
            (0, 5),
            (1, 3),
            (1, 4),
            (1, 5),
            (2, 3),
            (2, 4),
            (2, 5),
        ],
    );
    let mut should_stop = || false;
    let mut on_improve = |_: i128, _: &[bool]| {};
    let mut search = MaxCliqueSearch {
        instance: &instance,
        objective,
        fragment: &fragment,
        should_stop: &mut should_stop,
        on_improve: &mut on_improve,
        best_vertices: vec![0, 3],
        best_assignment: build_assignment(instance.num_vars, &fragment, &[0, 3]),
        best_objective: -2,
        interrupted: false,
        validation_failed: false,
        coloring_scratch: ColoringScratch::new(),
    };
    let candidates = BitSet::full(6);
    let mut no_clique_cache = HashMap::new();
    let mut triangle_stats = DecisionSearchStats::new(3);

    let triangle_result = search.decide_clique_of_size_with_stats(
        3,
        &candidates,
        &mut no_clique_cache,
        &mut triangle_stats,
    );

    assert_eq!(triangle_result, DecisionSearchResult::NoClique);
    assert_eq!(no_clique_cache.get(&candidates.words), Some(&3));

    let mut four_stats = DecisionSearchStats::new(4);
    let four_result = search.decide_clique_of_size_with_stats(
        4,
        &candidates,
        &mut no_clique_cache,
        &mut four_stats,
    );

    assert_eq!(four_result, DecisionSearchResult::NoClique);
    assert_eq!(four_stats.nodes_visited, 1);
    assert_eq!(four_stats.cache_hits, 1);

    let mut edge_stats = DecisionSearchStats::new(2);
    let edge_result = search.decide_clique_of_size_with_stats(
        2,
        &candidates,
        &mut no_clique_cache,
        &mut edge_stats,
    );

    assert_eq!(edge_result, DecisionSearchResult::FoundClique);
    assert_eq!(edge_stats.cache_hits, 0);
}
