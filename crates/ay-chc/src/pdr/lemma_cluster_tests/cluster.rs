// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_cluster_store_semantic_equivalence_clusters_together() {
    // Tests that semantically equivalent cubes (le vs not(gt)) cluster together
    // via the SemanticMatcher's negation equivalence handling.
    let mut store = ClusterStore::new();
    let pred = PredicateId::new(0);

    // cube1: (x <= 5) creates pattern `le(x, __gg_k0)` with value 5
    let cube1 = ChcExpr::le(make_var("x"), ChcExpr::Int(5));
    let idx1 = store.add_blocking_cube(pred, &cube1, 1).unwrap();
    assert_eq!(idx1, 0);

    // cube2: !(x > 7) is semantically equivalent to (x <= 7)
    // SemanticMatcher matches this against pattern `le(x, __gg_k0)` extracting value 7
    let cube2 = ChcExpr::not(make_gt(make_var("x"), ChcExpr::Int(7)));
    let idx2 = store.add_blocking_cube(pred, &cube2, 2).unwrap();
    assert_eq!(idx2, 0); // Same cluster as cube1

    let clusters = store.get_clusters(pred).unwrap();
    assert_eq!(clusters.len(), 1);
    // For `x <= k`, HigherSubsumes applies: value 7 subsumes value 5.
    // So only member [7] remains in the Pareto frontier.
    assert_eq!(clusters[0].size(), 1);
    assert_eq!(clusters[0].samples_seen, 2);
}

#[test]
fn test_cluster_store_refines_singleton_pattern_via_anti_unify() {
    let mut store = ClusterStore::new();
    let pred = PredicateId::new(0);

    // First lemma creates an over-abstracted singleton pattern: (= x k0) ∧ (= y k1)
    let cube1 = make_and(
        ChcExpr::eq(make_var("x"), ChcExpr::Int(0)),
        ChcExpr::eq(make_var("y"), ChcExpr::Int(5)),
    );
    let idx1 = store.add_blocking_cube(pred, &cube1, 1).unwrap();
    assert_eq!(idx1, 0);

    // Second lemma matches the singleton; we should refine the pattern to keep the common `0`
    // as a constant, abstracting only the differing `y` value.
    let cube2 = make_and(
        ChcExpr::eq(make_var("x"), ChcExpr::Int(0)),
        ChcExpr::eq(make_var("y"), ChcExpr::Int(10)),
    );
    let idx2 = store.add_blocking_cube(pred, &cube2, 2).unwrap();
    assert_eq!(idx2, 0);

    let clusters = store.get_clusters(pred).unwrap();
    assert_eq!(clusters.len(), 1);
    assert_eq!(clusters[0].pattern_vars.len(), 1);
    assert_eq!(clusters[0].pattern_vars[0].sort, ChcSort::Int);
    assert!(
        contains_int(&clusters[0].pattern, 0),
        "refined pattern should keep the common constant 0: {}",
        clusters[0].pattern
    );

    let kept: Vec<i128> = clusters[0]
        .members
        .iter()
        .map(|m| m.subst_values[0])
        .collect();
    assert_eq!(kept, vec![5, 10]);

    let counters = store.counters();
    assert_eq!(counters.singleton_refined, 1);
}

#[test]
fn test_cluster_store_creates_cluster_with_neighbours_when_no_match() {
    let mut store = ClusterStore::new();
    let pred = PredicateId::new(0);

    // First two lemmas refine the singleton cluster to keep the common x=0 constant.
    let cube1 = make_and(
        ChcExpr::eq(make_var("x"), ChcExpr::Int(0)),
        ChcExpr::eq(make_var("y"), ChcExpr::Int(5)),
    );
    store.add_blocking_cube(pred, &cube1, 1).unwrap();

    let cube2 = make_and(
        ChcExpr::eq(make_var("x"), ChcExpr::Int(0)),
        ChcExpr::eq(make_var("y"), ChcExpr::Int(10)),
    );
    store.add_blocking_cube(pred, &cube2, 2).unwrap();

    // This cube is a neighbour of both members (differs only in Int constants), but does not
    // match the refined pattern that kept `x=0` as a constant.
    let cube3 = make_and(
        ChcExpr::eq(make_var("x"), ChcExpr::Int(1)),
        ChcExpr::eq(make_var("y"), ChcExpr::Int(5)),
    );
    let idx3 = store.add_blocking_cube(pred, &cube3, 3).unwrap();
    assert_eq!(idx3, 1);

    let clusters = store.get_clusters(pred).unwrap();
    assert_eq!(clusters.len(), 2);
    assert_eq!(clusters[1].size(), 3);
    assert_eq!(clusters[1].pattern_vars.len(), 2);

    let counters = store.counters();
    assert_eq!(counters.neighbour_clusters_created, 1);
}

#[test]
fn test_cluster_add_member() {
    let pred = PredicateId::new(0);
    let pattern_var = ChcVar::new("__gg_k0", ChcSort::Int);
    // Use equality pattern so no member dominates another (`Equal` direction).
    let pattern = ChcExpr::eq(make_var("x"), ChcExpr::Var(pattern_var.clone()));

    let mut cluster = LemmaCluster::new(pred, pattern, vec![pattern_var]);

    // Add first member
    cluster.add_member(LemmaInstance::new(2, vec![5]));
    assert_eq!(cluster.size(), 1);

    // Add second member (different value, no dominance with equality)
    cluster.add_member(LemmaInstance::new(3, vec![10]));
    assert_eq!(cluster.size(), 2);

    // Add duplicate (should be deduplicated)
    cluster.add_member(LemmaInstance::new(4, vec![5]));
    assert_eq!(cluster.size(), 2);
}

#[test]
fn test_cluster_min_level() {
    // Tests that min_level_seen tracks the minimum level across ALL members ever added,
    // even if those members are later pruned by dominance.
    // Uses `x > k` pattern (LowerSubsumes): member [1] dominates [2] and [3],
    // so only [1] remains in members. But min_level_seen preserves level 2.
    let pred = PredicateId::new(0);
    let pattern_var = ChcVar::new("__gg_k0", ChcSort::Int);
    let pattern = make_gt(make_var("x"), ChcExpr::Var(pattern_var.clone()));

    let mut cluster = LemmaCluster::new(pred, pattern, vec![pattern_var]);
    assert_eq!(cluster.min_level(), None);

    cluster.add_member(LemmaInstance::new(5, vec![1]));
    assert_eq!(cluster.min_level(), Some(5));

    // Member [2] is dominated by [1] and pruned, but level 2 is remembered
    cluster.add_member(LemmaInstance::new(2, vec![2]));
    assert_eq!(cluster.min_level(), Some(2));

    // Member [3] is dominated by [1] and pruned, level stays at 2
    cluster.add_member(LemmaInstance::new(8, vec![3]));
    assert_eq!(cluster.min_level(), Some(2));
}

#[test]
fn test_cluster_eligibility() {
    let pred = PredicateId::new(0);
    let pattern_var = ChcVar::new("__gg_k0", ChcSort::Int);
    // Use an equality pattern so no member dominates another (`Equal` direction).
    let pattern = ChcExpr::eq(make_var("x"), ChcExpr::Var(pattern_var.clone()));

    let mut cluster = LemmaCluster::new(pred, pattern, vec![pattern_var]);

    // Not eligible: no members
    assert!(!cluster.is_eligible());

    // Not eligible: only 1 member
    cluster.add_member(LemmaInstance::new(1, vec![1]));
    assert!(!cluster.is_eligible());

    // Eligible: 2 members (equality has no dominance, both kept)
    cluster.add_member(LemmaInstance::new(2, vec![2]));
    assert!(cluster.is_eligible());

    // Exhaust gas
    for _ in 0..DEFAULT_CLUSTER_GAS {
        cluster.dec_gas();
    }
    assert!(!cluster.is_eligible());
}

#[test]
fn test_cluster_store() {
    let mut store = ClusterStore::new();
    let pred = PredicateId::new(0);

    // Add first blocking cube: x > 5
    let cube1 = make_gt(make_var("x"), ChcExpr::Int(5));
    let idx1 = store.add_blocking_cube(pred, &cube1, 1);
    assert!(idx1.is_some());

    // Add second blocking cube with same pattern: x > 10
    // For `x > k`, lower k values subsume higher ones (LowerSubsumes direction).
    // So [5] dominates [10], and only [5] is kept in the Pareto frontier.
    let cube2 = make_gt(make_var("x"), ChcExpr::Int(10));
    let idx2 = store.add_blocking_cube(pred, &cube2, 2);

    // Should be added to same cluster
    assert_eq!(idx1, idx2);

    // Verify cluster state: 1 member kept, but 2 samples seen
    let clusters = store.get_clusters(pred).unwrap();
    assert_eq!(clusters.len(), 1);
    assert_eq!(clusters[0].size(), 1);
    assert_eq!(clusters[0].samples_seen, 2);

    // Stats reflect actual members kept
    let stats = store.stats();
    assert_eq!(stats.total_clusters, 1);
    assert_eq!(stats.total_members, 1);
    assert_eq!(stats.max_cluster_size, 1);
}

#[test]
fn test_cluster_dominance_pruning_keeps_most_general() {
    // Renamed from test_cluster_store_overflow_prefers_subsumption_over_fifo:
    // This test now demonstrates dominance pruning (not overflow handling).
    let mut store = ClusterStore::new();
    let pred = PredicateId::new(0);

    // x > 0, x > 1, ..., x > 5
    // For `x > k` pattern (LowerSubsumes direction), the first member [0]
    // dominates all subsequent members [1], [2], ..., [5].
    // So only [0] is kept in the Pareto frontier.
    for i in 0..=(MAX_CLUSTER_SIZE as i128) {
        let cube = make_gt(make_var("x"), ChcExpr::Int(i));
        store.add_blocking_cube(pred, &cube, 1);
    }

    let clusters = store.get_clusters(pred).unwrap();
    assert_eq!(clusters.len(), 1);
    assert_eq!(clusters[0].size(), 1);
    assert_eq!(clusters[0].samples_seen, MAX_CLUSTER_SIZE + 1);

    let kept: Vec<i128> = clusters[0]
        .members
        .iter()
        .map(|m| m.subst_values[0])
        .collect();
    assert_eq!(kept, vec![0]);
}

#[test]
fn test_cluster_store_overflow_falls_back_to_fifo_without_subsumption() {
    let mut store = ClusterStore::new();
    let pred = PredicateId::new(0);

    // Points along an anti-diagonal: no member implies another.
    // When over capacity, we must deterministically evict by FIFO.
    for i in 0..=(MAX_CLUSTER_SIZE as i128) {
        let cube = ChcExpr::and(
            make_gt(make_var("x"), ChcExpr::Int(i)),
            make_gt(make_var("y"), ChcExpr::Int(MAX_CLUSTER_SIZE as i128 - i)),
        );
        store.add_blocking_cube(pred, &cube, 1);
    }

    let clusters = store.get_clusters(pred).unwrap();
    assert_eq!(clusters.len(), 1);
    assert_eq!(clusters[0].size(), MAX_CLUSTER_SIZE);

    let kept: Vec<(i128, i128)> = clusters[0]
        .members
        .iter()
        .map(|m| (m.subst_values[0], m.subst_values[1]))
        .collect();
    let expected: Vec<(i128, i128)> = (1..=MAX_CLUSTER_SIZE as i128)
        .map(|i| (i, MAX_CLUSTER_SIZE as i128 - i))
        .collect();
    assert_eq!(kept, expected);
}

#[test]
fn test_min_max_proposals_from_equality_cluster() {
    let pred = PredicateId::new(0);
    let pv = ChcVar::new("__gg_k0", ChcSort::Int);
    let pattern = ChcExpr::eq(make_var("x"), ChcExpr::var(pv.clone()));
    let mut cluster = LemmaCluster::new(pred, pattern, vec![pv]);

    cluster.add_member(LemmaInstance::new(1, vec![-3]));
    cluster.add_member(LemmaInstance::new(1, vec![-2]));
    cluster.add_member(LemmaInstance::new(1, vec![-1]));

    let proposals = cluster.propose_min_max_blocking_cubes();
    let expected = vec![
        normalize_cube(&ChcExpr::le(make_var("x"), ChcExpr::Int(-1))),
        normalize_cube(&ChcExpr::ge(make_var("x"), ChcExpr::Int(-3))),
    ];
    assert_eq!(proposals, expected);
}

#[test]
fn test_min_max_proposals_from_ge_cluster() {
    let pred = PredicateId::new(0);
    let pv = ChcVar::new("__gg_k0", ChcSort::Int);
    let pattern = ChcExpr::ge(make_var("x"), ChcExpr::var(pv.clone()));
    let mut cluster = LemmaCluster::new(pred, pattern, vec![pv]);

    cluster.add_member(LemmaInstance::new(1, vec![10]));
    cluster.add_member(LemmaInstance::new(1, vec![5]));
    cluster.add_member(LemmaInstance::new(1, vec![7]));

    let proposals = cluster.propose_min_max_blocking_cubes();
    let expected = vec![normalize_cube(&ChcExpr::ge(make_var("x"), ChcExpr::Int(5)))];
    assert_eq!(proposals, expected);
}

#[test]
fn test_min_max_proposals_from_bounded_cluster() {
    let pred = PredicateId::new(0);
    let pv0 = ChcVar::new("__gg_k0", ChcSort::Int);
    let pv1 = ChcVar::new("__gg_k1", ChcSort::Int);

    let pattern = ChcExpr::and(
        ChcExpr::ge(make_var("x"), ChcExpr::var(pv0.clone())),
        ChcExpr::le(make_var("x"), ChcExpr::var(pv1.clone())),
    );
    let mut cluster = LemmaCluster::new(pred, pattern, vec![pv0, pv1]);

    cluster.add_member(LemmaInstance::new(1, vec![0, 10]));
    cluster.add_member(LemmaInstance::new(1, vec![1, 11]));
    cluster.add_member(LemmaInstance::new(1, vec![2, 12]));

    let proposals = cluster.propose_min_max_blocking_cubes();
    let expected = vec![normalize_cube(&ChcExpr::and(
        ChcExpr::le(make_var("x"), ChcExpr::Int(12)),
        ChcExpr::ge(make_var("x"), ChcExpr::Int(0)),
    ))];
    assert_eq!(proposals, expected);
}

#[test]
fn test_min_max_proposals_requires_three_members() {
    let pred = PredicateId::new(0);
    let pv = ChcVar::new("__gg_k0", ChcSort::Int);
    let pattern = ChcExpr::ge(make_var("x"), ChcExpr::var(pv.clone()));
    let mut cluster = LemmaCluster::new(pred, pattern, vec![pv]);

    cluster.add_member(LemmaInstance::new(1, vec![0]));
    cluster.add_member(LemmaInstance::new(1, vec![1]));

    let proposals = cluster.propose_min_max_blocking_cubes();
    assert!(proposals.is_empty());
}

#[test]
fn test_min_max_proposals_handles_pattern_var_on_left() {
    let pred = PredicateId::new(0);
    let pv = ChcVar::new("__gg_k0", ChcSort::Int);
    // pattern: (<= __gg_k0 x) is the same as (>= x __gg_k0)
    let pattern = ChcExpr::le(ChcExpr::var(pv.clone()), make_var("x"));
    let mut cluster = LemmaCluster::new(pred, pattern, vec![pv]);

    cluster.add_member(LemmaInstance::new(1, vec![10]));
    cluster.add_member(LemmaInstance::new(1, vec![5]));
    cluster.add_member(LemmaInstance::new(1, vec![7]));

    let proposals = cluster.propose_min_max_blocking_cubes();
    let expected = vec![normalize_cube(&ChcExpr::ge(make_var("x"), ChcExpr::Int(5)))];
    assert_eq!(proposals, expected);
}

#[test]
fn test_cluster_store_capacity_bounded() {
    // After inserting more than MAX_CLUSTERS_PER_PREDICATE distinct patterns
    // for one predicate, cluster count must stay at MAX_CLUSTERS_PER_PREDICATE.
    let mut store = ClusterStore::new();
    let pred = PredicateId::new(0);

    // Insert N+2 distinct patterns (each with a different variable name)
    // to trigger eviction twice
    for i in 0..(MAX_CLUSTERS_PER_PREDICATE + 2) {
        let var_name = format!("v{i}");
        let cube = make_gt(make_var(&var_name), ChcExpr::Int(1));
        store.add_blocking_cube(pred, &cube, 1);
    }

    let clusters = store.get_clusters(pred).unwrap();
    assert_eq!(
        clusters.len(),
        MAX_CLUSTERS_PER_PREDICATE,
        "cluster count must be capped at MAX_CLUSTERS_PER_PREDICATE"
    );

    // Verify counters
    let counters = store.counters();
    assert_eq!(counters.calls, (MAX_CLUSTERS_PER_PREDICATE + 2) as u64);
    assert_eq!(counters.misses, (MAX_CLUSTERS_PER_PREDICATE + 2) as u64);
    assert_eq!(counters.hits, 0);
    assert_eq!(counters.clusters_evicted, 2);
}

#[test]
fn test_cluster_store_evicts_ineligible_first() {
    // When at capacity, ineligible clusters (size < 2 or gas == 0) are evicted first.
    let mut store = ClusterStore::new();
    let pred = PredicateId::new(0);

    // Fill to capacity with distinct patterns using equality (no dominance pruning)
    for i in 0..MAX_CLUSTERS_PER_PREDICATE {
        let var_name = format!("x{i}");
        let cube = ChcExpr::eq(make_var(&var_name), ChcExpr::Int(1));
        store.add_blocking_cube(pred, &cube, 1);
    }

    // Add a second member to the first cluster to make it eligible
    // With equality pattern, both members are kept (no dominance relationship)
    let cube_first = ChcExpr::eq(make_var("x0"), ChcExpr::Int(2));
    store.add_blocking_cube(pred, &cube_first, 1);

    // All clusters except first have size 1 (ineligible)
    // Add one more distinct pattern to trigger eviction
    let new_cube = ChcExpr::eq(make_var("new_var"), ChcExpr::Int(1));
    store.add_blocking_cube(pred, &new_cube, 1);

    let clusters = store.get_clusters(pred).unwrap();
    assert_eq!(clusters.len(), MAX_CLUSTERS_PER_PREDICATE);

    // First cluster (eligible) should be retained
    // Check that an eligible cluster exists
    let has_eligible = clusters.iter().any(LemmaCluster::is_eligible);
    assert!(has_eligible, "eligible cluster should be retained");

    // Verify that ineligible was evicted
    let counters = store.counters();
    assert_eq!(counters.evicted_ineligible, 1);
}

#[test]
fn test_cluster_store_eviction_determinism() {
    // Given a fixed insertion order, eviction removes the same pattern every run.
    let mut store = ClusterStore::new();
    let pred = PredicateId::new(0);

    // Fill to capacity
    for i in 0..MAX_CLUSTERS_PER_PREDICATE {
        let var_name = format!("y{i}");
        let cube = make_gt(make_var(&var_name), ChcExpr::Int(i as i128));
        store.add_blocking_cube(pred, &cube, 1);
    }

    // Trigger eviction
    let overflow_cube = make_gt(make_var("overflow"), ChcExpr::Int(100));
    store.add_blocking_cube(pred, &overflow_cube, 1);

    let clusters = store.get_clusters(pred).unwrap();
    assert_eq!(clusters.len(), MAX_CLUSTERS_PER_PREDICATE);

    // The new cluster should be present
    let has_overflow = clusters
        .iter()
        .any(|c| c.pattern.to_string().contains("overflow"));
    assert!(has_overflow, "new cluster should be added after eviction");

    // The oldest ineligible cluster (y0) should have been evicted
    let has_y0 = clusters
        .iter()
        .any(|c| c.pattern.to_string().contains("y0"));
    assert!(!has_y0, "oldest ineligible cluster (y0) should be evicted");
}
