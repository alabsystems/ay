// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::counted_storage::test_owner;

fn lit(index: u32) -> Literal {
    Literal::positive(Variable::new(index))
}

fn fixture() -> Solver {
    let mut s = Solver::new(12);
    for i in 1..10 {
        assert!(s.add_clause(vec![lit(0), lit(i), lit(i + 1)]));
    }
    s.initialize_watches();
    s
}

fn capacities(frontier: &RelevancyFrontier) -> Vec<usize> {
    [
        frontier.buf.capacity(),
        frontier.var_unsat.capacity(),
        frontier.true_count.capacity(),
        frontier.occ.capacity(),
    ]
    .into_iter()
    .chain(frontier.occ.iter().map(Vec::capacity))
    .collect()
}

fn check_prepared_sync(s: &Solver, mut actual: RelevancyFrontier, mut expected: RelevancyFrontier) {
    let owner = test_owner(10_000_000, 10_000_000);
    let before = actual.backtrack_test_snapshot();
    let mut storage = actual.prepare_selection(s, &owner).unwrap();
    assert_eq!(actual.backtrack_test_snapshot(), before);
    // New headers have not been committed, but every header and inner buffer
    // the rebuild will adopt already has capacity. Capture both ownerships.
    let mut reserved = capacities(&actual);
    reserved.extend(storage.extra_occ.iter().map(Vec::capacity));
    reserved.truncate(4 + s.num_vars * 2);
    assert_eq!(
        actual.sync_prepared(s, Some(&mut storage)),
        expected.sync(s)
    );
    assert_eq!(storage.extra_occ.len(), 0);
    assert_eq!(capacities(&actual), reserved);
    assert_eq!(
        actual.backtrack_test_snapshot(),
        expected.backtrack_test_snapshot()
    );
    assert_eq!(capacities(&actual), capacities(&expected));
    #[cfg(any(debug_assertions, feature = "relevancy-frontier-invariants"))]
    {
        let reference_capacity = storage.reference.capacity();
        assert_eq!(
            s.fill_relevancy_frontier(&mut storage.reference),
            actual.size > 0
        );
        assert_eq!(storage.reference, actual.buf);
        assert_eq!(storage.reference.capacity(), reference_capacity);
    }
}

#[test]
fn first_rebuild_installs_paid_inner_vectors_without_commit_allocation() {
    check_prepared_sync(
        &fixture(),
        RelevancyFrontier::default(),
        RelevancyFrontier::default(),
    );
}

#[test]
fn incremental_folds_and_appended_occurrences_keep_ordinary_layout() {
    let mut s = fixture();
    let mut actual = RelevancyFrontier::default();
    let mut expected = RelevancyFrontier::default();
    actual.sync(&s);
    expected.sync(&s);
    s.decide(lit(1));
    assert!(s.search_propagate().is_none());
    for _ in 0..10 {
        s.arena.add(&[lit(0), lit(10), lit(11)], true);
    }
    check_prepared_sync(&s, actual, expected);
}

#[test]
fn append_count_fallback_pays_append_peak_and_actual_rebuild() {
    let mut s = fixture();
    let mut actual = RelevancyFrontier::default();
    let mut expected = RelevancyFrontier::default();
    actual.sync(&s);
    expected.sync(&s);
    // Exercise the existing defensive count mismatch independently of epoch
    // invalidation: the sync must append first, then take its real rebuild.
    actual.arena_clauses -= 1;
    expected.arena_clauses -= 1;
    for _ in 0..10 {
        s.arena.add(&[lit(0), lit(10), lit(11)], true);
    }
    assert!(!actual.needs_rebuild(&s));
    check_prepared_sync(&s, actual, expected);
}

#[test]
fn epoch_trail_and_variable_count_invalidations_keep_rebuild_parity() {
    for event in 0..3 {
        let mut s = fixture();
        s.decide(lit(1));
        assert!(s.search_propagate().is_none());
        let mut actual = RelevancyFrontier::default();
        let mut expected = RelevancyFrontier::default();
        actual.sync(&s);
        expected.sync(&s);
        match event {
            0 => {
                let offset = s.arena.indices().next().unwrap();
                s.arena.delete(offset);
            }
            1 => s.backtrack(0),
            _ => {
                s.new_var();
            }
        }
        assert!(actual.needs_rebuild(&s));
        check_prepared_sync(&s, actual, expected);
    }
}

#[test]
fn stopped_new_header_preparation_preserves_logical_cache() {
    let s = fixture();
    let mut baseline = RelevancyFrontier::default();
    let owner = test_owner(10_000_000, 10_000_000);
    baseline.prepare_selection(&s, &owner).unwrap();
    let used = owner.usage().unwrap();
    for storage in [0, used.storage_admitted / 2, used.storage_admitted - 1] {
        let mut actual = RelevancyFrontier::default();
        let before = actual.backtrack_test_snapshot();
        let owner = test_owner(used.work_admitted, storage);
        assert!(actual.prepare_selection(&s, &owner).is_err());
        assert_eq!(actual.backtrack_test_snapshot(), before);
    }
}

#[test]
fn expired_debug_query_quota_does_not_allocate_reference_scratch() {
    let s = fixture();
    let mut frontier = RelevancyFrontier::default();
    frontier.sync(&s);
    #[cfg(all(debug_assertions, not(feature = "relevancy-frontier-invariants")))]
    {
        frontier.debug_checks_done = DEFAULT_DEBUG_CHECKS;
    }
    let owner = test_owner(10_000_000, 10_000_000);
    let storage = frontier.prepare_selection(&s, &owner).unwrap();
    #[cfg(all(debug_assertions, not(feature = "relevancy-frontier-invariants")))]
    assert_eq!(storage.reference.capacity(), 0);
    #[cfg(feature = "relevancy-frontier-invariants")]
    assert!(storage.reference.capacity() >= s.num_vars);
    #[cfg(not(any(debug_assertions, feature = "relevancy-frontier-invariants")))]
    {
        let _ = storage;
    }
}

#[test]
fn occurrence_preallocation_preserves_even_non_power_of_two_capacity() {
    for capacity in 0..10 {
        for required in 0..20 {
            let mut actual = vec![0u32; capacity];
            let mut expected = actual.clone();
            let owner = test_owner(10_000, 10_000);
            reserve_pushes(&mut actual, required, &owner).unwrap();
            let reserved = actual.capacity();
            actual.clear();
            expected.clear();
            for index in 0..required {
                actual.push(index as u32);
                expected.push(index as u32);
                assert_eq!(actual.capacity(), reserved);
            }
            assert_eq!(actual, expected);
            assert_eq!(actual.capacity(), expected.capacity());
        }
    }
}
