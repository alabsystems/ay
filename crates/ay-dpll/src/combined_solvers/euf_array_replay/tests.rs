// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn compact_indices_reject_unrepresentable_capacity() {
    assert_eq!(compact_index(u32::MAX as usize), Some(u32::MAX));
    #[cfg(target_pointer_width = "64")]
    assert_eq!(compact_index(u32::MAX as usize + 1), None);
}

#[test]
fn exact_reason_groups_share_storage_and_preserve_order() {
    let guard = TheoryLit::new(TermId(10), true);
    let mut state = EufArrayNotifyReplayState::default();
    assert!(state.insert(TermId(1), TermId(2), vec![guard]));
    assert!(state.insert(TermId(2), TermId(3), vec![guard]));
    assert!(!state.insert(TermId(1), TermId(2), vec![guard]));
    assert_eq!(state.group_count(), 1);
    assert_eq!(state.len(), 2);
    assert_eq!(
        state
            .to_edges()
            .into_iter()
            .map(|edge| (edge.target, edge.source))
            .collect::<Vec<_>>(),
        vec![(TermId(1), TermId(2)), (TermId(2), TermId(3))]
    );
}

#[test]
fn active_forest_is_stable_minimum_root_and_validates_by_group() {
    let g1 = TheoryLit::new(TermId(20), true);
    let g2 = TheoryLit::new(TermId(21), true);
    let mut imported = EufArrayNotifyReplayState::default();
    imported.insert(TermId(4), TermId(3), vec![g1]);
    imported.insert(TermId(3), TermId(2), vec![g1]);
    let mut local = EufArrayNotifyReplayState::default();
    local.insert(TermId(2), TermId(1), vec![g2]);

    let mut assignments = DetHashMap::default();
    assignments.insert(g1.term, true);
    assignments.insert(g2.term, true);
    let imported_missing = initialize_missing(&imported, &assignments);
    let local_missing = initialize_missing(&local, &assignments);
    let mut parent = DetHashMap::default();
    let mut forest = Vec::new();
    build_active_forest(
        &imported,
        &local,
        &imported_missing,
        &local_missing,
        &mut parent,
        &mut forest,
    );
    assert_eq!(
        forest,
        vec![
            (TermId(3), TermId(4)),
            (TermId(2), TermId(3)),
            (TermId(1), TermId(2)),
        ]
    );

    assignments.insert(g2.term, false);
    forest.clear();
    parent.clear();
    let imported_missing = initialize_missing(&imported, &assignments);
    let local_missing = initialize_missing(&local, &assignments);
    build_active_forest(
        &imported,
        &local,
        &imported_missing,
        &local_missing,
        &mut parent,
        &mut forest,
    );
    assert_eq!(forest, vec![(TermId(3), TermId(4)), (TermId(2), TermId(3))]);
}

#[test]
fn repeated_replay_and_local_tail_do_not_rebuild_imported_forest() {
    let guard = TheoryLit::new(TermId(20), true);
    let mut imported = EufArrayNotifyReplayState::default();
    imported.insert(TermId(1), TermId(2), vec![guard]);
    let mut local = EufArrayNotifyReplayState::default();
    let mut assignments = DetHashMap::default();
    assignments.insert(guard.term, true);
    let mut parent = DetHashMap::default();
    let mut cache = EufArrayNotifyReplayCache::default();

    cache.ensure_forest(&imported, &local, &assignments, &mut parent);
    assert_eq!(cache.forest_rebuilds(), 1);
    assert_eq!(cache.unapplied_forest(), &[(TermId(1), TermId(2))]);
    cache.mark_applied();
    cache.ensure_forest(&imported, &local, &assignments, &mut parent);
    assert_eq!(cache.forest_rebuilds(), 1);
    assert!(!cache.needs_application());

    local.insert(TermId(2), TermId(3), vec![guard]);
    cache.ensure_forest(&imported, &local, &assignments, &mut parent);
    assert_eq!(
        cache.forest_rebuilds(),
        1,
        "a local tail must extend the forest without rescanning imports"
    );
    assert_eq!(cache.unapplied_forest(), &[(TermId(1), TermId(3))]);
}

#[test]
fn literal_incidence_activates_once_and_pop_invalidation_rebuilds() {
    let first = TheoryLit::new(TermId(20), true);
    let second = TheoryLit::new(TermId(21), false);
    let mut imported = EufArrayNotifyReplayState::default();
    imported.insert(TermId(1), TermId(2), vec![first, second]);
    let local = EufArrayNotifyReplayState::default();
    let mut assignments = DetHashMap::default();
    let mut parent = DetHashMap::default();
    let mut cache = EufArrayNotifyReplayCache::default();

    cache.ensure_forest(&imported, &local, &assignments, &mut parent);
    assert!(cache.unapplied_forest().is_empty());
    assignments.insert(first.term, first.value);
    cache.assignment_added(first, &imported, &local, &mut parent);
    assert!(cache.unapplied_forest().is_empty());
    assignments.insert(second.term, second.value);
    cache.assignment_added(second, &imported, &local, &mut parent);
    assert_eq!(cache.unapplied_forest(), &[(TermId(1), TermId(2))]);
    cache.mark_applied();

    assignments.remove(&second.term);
    parent.clear();
    cache.invalidate_assignment();
    cache.ensure_forest(&imported, &local, &assignments, &mut parent);
    assert_eq!(cache.forest_rebuilds(), 2);
    assert!(cache.unapplied_forest().is_empty());
}

#[test]
fn activation_permutations_preserve_connectivity_without_rebuild() {
    let first = TheoryLit::new(TermId(20), true);
    let second = TheoryLit::new(TermId(21), true);
    let mut imported = EufArrayNotifyReplayState::default();
    imported.insert(TermId(1), TermId(2), vec![first]);
    imported.insert(TermId(2), TermId(3), vec![second]);
    let local = EufArrayNotifyReplayState::default();

    let run = |order: [TheoryLit; 2]| {
        let mut assignments = DetHashMap::default();
        let mut parent = DetHashMap::default();
        let mut cache = EufArrayNotifyReplayCache::default();
        let mut notifications = 0;
        for lit in order {
            assignments.insert(lit.term, lit.value);
            cache.assignment_added(lit, &imported, &local, &mut parent);
            cache.ensure_forest(&imported, &local, &assignments, &mut parent);
            notifications += cache.unapplied_forest().len();
            cache.mark_applied();
        }
        cache.ensure_forest(&imported, &local, &assignments, &mut parent);
        assert!(!cache.needs_application());
        let roots = [TermId(1), TermId(2), TermId(3)].map(|term| find(&mut parent, term));
        (
            notifications,
            cache.forest.len(),
            roots,
            cache.forest_rebuilds(),
        )
    };

    let forward = run([first, second]);
    let reverse = run([second, first]);
    assert_eq!(forward.0, 2);
    assert_eq!(reverse.0, 2);
    assert_eq!(forward.1, 2);
    assert_eq!(reverse.1, 2);
    assert_eq!(forward.2, [TermId(1); 3]);
    assert_eq!(reverse.2, forward.2);
    assert_eq!(forward.3, 1);
    assert_eq!(reverse.3, 1);
}
