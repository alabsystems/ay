// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Textually included by `optimize::max_clique::tests` to preserve test FQNs.

#[test]
fn decision_search_stats_mark_interrupted_stop() {
    let instance = unconstrained_instance(3);
    let objective = instance.objective.as_ref().unwrap();
    let fragment = test_fragment_from_edges(3, &[(0, 1), (0, 2), (1, 2)]);
    let mut should_stop = || true;
    let mut on_improve = |_: i128, _: &[bool]| {};
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
    let mut stats = DecisionSearchStats::new(2);

    let result = search.decide_clique_of_size_with_stats(
        2,
        &BitSet::full(3),
        &mut no_clique_cache,
        &mut stats,
    );

    assert_eq!(result, DecisionSearchResult::Interrupted);
    assert_eq!(stats.nodes_visited, 1);
    assert_eq!(stats.max_depth, 0);
    assert!(stats.interrupted);
    assert!(no_clique_cache.is_empty());
}

#[test]
fn decision_search_node_limit_is_fail_closed_without_global_interruption() {
    let instance = unconstrained_instance(3);
    let objective = instance.objective.as_ref().unwrap();
    let fragment = test_fragment_from_edges(3, &[(0, 1), (0, 2), (1, 2)]);
    let mut should_stop = || false;
    let mut on_improve = |_: i128, _: &[bool]| {};
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
    let mut stats = DecisionSearchStats::new(2);

    let result = search.decide_clique_of_size_with_stats_and_node_limit(
        2,
        &BitSet::full(3),
        &mut no_clique_cache,
        &mut stats,
        Some(0),
    );

    assert_eq!(result, DecisionSearchResult::Interrupted);
    assert_eq!(stats.nodes_visited, 0);
    assert!(stats.interrupted);
    assert!(!search.interrupted);
    assert!(search.best_vertices.is_empty());
    assert!(no_clique_cache.is_empty());
}

#[test]
fn incumbent_exactness_proof_reports_completed_no_clique() {
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

    let result = search.prove_current_incumbent_exact(&BitSet::full(5));

    assert_eq!(result, DecisionSearchResult::NoClique);
    assert!(!search.interrupted);
    assert_eq!(search.best_objective, -2);
}

#[test]
fn incumbent_exactness_proof_preserves_interruption() {
    let instance = unconstrained_instance(3);
    let objective = instance.objective.as_ref().unwrap();
    let fragment = test_fragment_from_edges(3, &[(0, 1), (0, 2), (1, 2)]);
    let mut should_stop = || true;
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

    let result = search.prove_current_incumbent_exact(&BitSet::full(3));

    assert_eq!(result, DecisionSearchResult::Interrupted);
    assert!(search.interrupted);
    assert_eq!(search.best_objective, -2);
}

#[test]
fn incumbent_exchange_finalizer_finds_profitable_drop_exchange() {
    let instance = unconstrained_instance(5);
    let objective = instance.objective.as_ref().unwrap();
    let fragment = test_fragment_from_edges(
        5,
        &[
            (0, 1),
            (0, 2),
            (1, 2),
            (1, 3),
            (1, 4),
            (2, 3),
            (2, 4),
            (3, 4),
        ],
    );
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

    let result = search.finalize_incumbent_exchange();

    assert_eq!(result, IncumbentExchangeFinalizerResult::Exact);
    assert_eq!(search.best_vertices.len(), 4);
    assert_eq!(search.best_objective, -4);
    assert!(improvements.get() >= 1);
    assert!(search.best_vertices.contains(&1));
    assert!(search.best_vertices.contains(&2));
    assert!(search.best_vertices.contains(&3));
    assert!(search.best_vertices.contains(&4));
    assert_fragment_clique(&fragment, &search.best_vertices);
}

#[test]
fn incumbent_exchange_dominance_accepts_covering_lower_drop_branch() {
    let fragment =
        test_fragment_from_edges(5, &[(0, 1), (0, 2), (0, 4), (1, 2), (1, 3), (2, 3), (3, 4)]);
    let incumbent = vec![0, 1];
    let mut should_stop = || false;
    let mut interrupted = false;
    let mut stats = DecisionSearchStats::new(3);
    let prover = IncumbentExchangeProver::new(
        &fragment,
        &incumbent,
        &mut should_stop,
        &mut interrupted,
        &mut stats,
    );
    let current_drop_mask = BitSet::empty(incumbent.len());
    let mut vertex_drop_mask = current_drop_mask.clone();
    vertex_drop_mask.union_with(&prover.drop_masks[4]);
    let mut next_candidates = BitSet::empty(fragment.objective_vars.len());
    next_candidates.insert(3);

    assert_eq!(
        prover.explored_branch_dominates(
            4,
            &current_drop_mask,
            &vertex_drop_mask,
            &next_candidates,
            &[2],
        ),
        Some(2)
    );
}

#[test]
fn incumbent_exchange_dominance_rejects_uncovered_suffix() {
    let fragment =
        test_fragment_from_edges(5, &[(0, 1), (0, 2), (0, 4), (1, 2), (1, 3), (2, 3), (3, 4)]);
    let incumbent = vec![0, 1];
    let mut should_stop = || false;
    let mut interrupted = false;
    let mut stats = DecisionSearchStats::new(3);
    let prover = IncumbentExchangeProver::new(
        &fragment,
        &incumbent,
        &mut should_stop,
        &mut interrupted,
        &mut stats,
    );
    let current_drop_mask = BitSet::empty(incumbent.len());
    let mut vertex_drop_mask = current_drop_mask.clone();
    vertex_drop_mask.union_with(&prover.drop_masks[4]);
    let mut next_candidates = BitSet::empty(fragment.objective_vars.len());
    next_candidates.insert(3);
    next_candidates.insert(4);

    assert_eq!(
        prover.explored_branch_dominates(
            4,
            &current_drop_mask,
            &vertex_drop_mask,
            &next_candidates,
            &[2],
        ),
        None
    );
}

#[test]
fn incumbent_exchange_dominance_rejects_larger_drop_mask() {
    let fragment = test_fragment_from_edges(4, &[(0, 1), (0, 2), (0, 3), (1, 3), (2, 3)]);
    let incumbent = vec![0, 1];
    let mut should_stop = || false;
    let mut interrupted = false;
    let mut stats = DecisionSearchStats::new(3);
    let prover = IncumbentExchangeProver::new(
        &fragment,
        &incumbent,
        &mut should_stop,
        &mut interrupted,
        &mut stats,
    );
    let current_drop_mask = BitSet::empty(incumbent.len());
    let mut vertex_drop_mask = current_drop_mask.clone();
    vertex_drop_mask.union_with(&prover.drop_masks[3]);
    let next_candidates = BitSet::empty(fragment.objective_vars.len());

    assert_eq!(
        prover.explored_branch_dominates(
            3,
            &current_drop_mask,
            &vertex_drop_mask,
            &next_candidates,
            &[2],
        ),
        None
    );
}

#[test]
fn incumbent_exchange_finalizer_uses_dominance_prune_without_losing_exactness() {
    let fragment =
        test_fragment_from_edges(5, &[(0, 1), (0, 2), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4)]);
    let incumbent = vec![0, 1, 2];
    let mut should_stop = || false;
    let mut interrupted = false;
    let mut stats = DecisionSearchStats::new(4);
    let mut prover = IncumbentExchangeProver::new(
        &fragment,
        &incumbent,
        &mut should_stop,
        &mut interrupted,
        &mut stats,
    );

    assert_eq!(prover.prove(), IncumbentExchangeOutcome::NoPositiveExchange);
    assert_eq!(prover.stats.dominance_prunes, 1);
    assert!(!*prover.interrupted);
}

#[test]
fn incumbent_exchange_finalizer_matches_bruteforce_on_all_graphs_up_to_five_vertices() {
    for num_vertices in 1..=5 {
        let instance = unconstrained_instance(num_vertices);
        let objective = instance.objective.as_ref().unwrap();
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
            let expected = brute_force_max_clique_size(&fragment);

            for incumbent_mask in 1usize..(1usize << num_vertices) {
                let incumbent = (0..num_vertices)
                    .filter(|vertex| (incumbent_mask & (1usize << vertex)) != 0)
                    .collect::<Vec<_>>();
                if !clique_vertices_are_pairwise_adjacent(&fragment, &incumbent) {
                    continue;
                }

                let mut should_stop = || false;
                let mut on_improve = |_: i128, _: &[bool]| {};
                let mut search = MaxCliqueSearch {
                    instance: &instance,
                    objective,
                    fragment: &fragment,
                    should_stop: &mut should_stop,
                    on_improve: &mut on_improve,
                    best_vertices: incumbent.clone(),
                    best_assignment: build_assignment(instance.num_vars, &fragment, &incumbent),
                    best_objective: -(incumbent.len() as i128),
                    interrupted: false,
                    validation_failed: false,
                    coloring_scratch: ColoringScratch::new(),
                };

                let result = search.finalize_incumbent_exchange();

                assert_eq!(
                    result,
                    IncumbentExchangeFinalizerResult::Exact,
                    "n={num_vertices} edge_mask={edge_mask:#x} incumbent={incumbent:?}"
                );
                assert_eq!(
                    search.best_vertices.len(),
                    expected,
                    "n={num_vertices} edge_mask={edge_mask:#x} incumbent={incumbent:?}"
                );
                assert!(!search.interrupted);
                assert!(!search.validation_failed);
                assert_fragment_clique(&fragment, &search.best_vertices);
            }
        }
    }
}

#[test]
fn incumbent_exchange_finalizer_interruption_is_not_exact() {
    let instance = unconstrained_instance(3);
    let objective = instance.objective.as_ref().unwrap();
    let fragment = test_fragment_from_edges(3, &[(0, 1), (0, 2), (1, 2)]);
    let mut should_stop = || true;
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

    let result = search.finalize_incumbent_exchange();

    assert_eq!(result, IncumbentExchangeFinalizerResult::Interrupted);
    assert!(search.interrupted);
    assert_eq!(search.best_vertices, vec![0, 1]);
    assert_eq!(search.best_objective, -2);
}
