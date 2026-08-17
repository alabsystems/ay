// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

pub(super) fn assert_imported_replay_survives_soft_reset() {
    let mut terms = TermStore::new();
    let arr_sort = Sort::array(Sort::Int, Sort::Int);

    let a = terms.mk_var("a", arr_sort.clone());
    let b = terms.mk_var("b", arr_sort);
    let guard = terms.mk_var("guard", Sort::Bool);

    let mut first = TheoryCombiner::array_euf(&terms);
    first.assert_literal(guard, true);
    assert_eq!(
        first.notify_arrays_of_euf_equalities(&[DiscoveredEquality::new(
            a,
            b,
            vec![TheoryLit::new(guard, true)],
        )]),
        1
    );
    let edges = first.export_euf_array_notify_replay_edges();
    assert_eq!(edges.len(), 1);

    let mut current = TheoryCombiner::array_euf(&terms);
    current.import_euf_array_notify_replay_edges(&edges);
    current.soft_reset();
    current.assert_literal(guard, true);
    assert!(
        current.euf_array_notify_replay_edge_reasons_hold(&edges[0]),
        "current true guard should make the imported replay edge persistence-eligible"
    );
    assert_eq!(
        current.replay_valid_euf_array_notifications(),
        1,
        "extension soft reset must not discard imported reason-validated replay edges"
    );
    assert_eq!(current.euf_array_notify_parent.get(&b), Some(&a));

    let mut stale = TheoryCombiner::array_euf(&terms);
    stale.import_euf_array_notify_replay_edges(&edges);
    stale.soft_reset();
    stale.assert_literal(guard, false);
    assert!(
        !stale.euf_array_notify_replay_edge_reasons_hold(&edges[0]),
        "current false guard should make the imported replay edge ineligible for persistence"
    );
}

pub(super) fn assert_group_activation_permutation_preserves_connectivity() {
    let mut terms = TermStore::new();
    let arr_sort = Sort::array(Sort::Int, Sort::Int);
    let a = terms.mk_var("perm_a", arr_sort.clone());
    let b = terms.mk_var("perm_b", arr_sort.clone());
    let c = terms.mk_var("perm_c", arr_sort);
    let first_guard = terms.mk_var("perm_first", Sort::Bool);
    let second_guard = terms.mk_var("perm_second", Sort::Bool);
    let edges = [
        EufArrayNotifyReplayEdge::new(a, b, vec![TheoryLit::new(first_guard, true)]),
        EufArrayNotifyReplayEdge::new(b, c, vec![TheoryLit::new(second_guard, true)]),
    ];

    let run = |order: [TermId; 2]| {
        let mut combiner = TheoryCombiner::array_euf(&terms);
        combiner.import_euf_array_notify_replay_edges(&edges);
        let mut notifications = 0;
        for guard in order {
            combiner.assert_literal(guard, true);
            notifications += combiner.replay_valid_euf_array_notifications();
        }
        assert_eq!(
            combiner.replay_valid_euf_array_notifications(),
            0,
            "replaying an unchanged active relation must be a no-op"
        );
        let roots = [a, b, c].map(|term| {
            TheoryCombiner::array_notify_find(&mut combiner.euf_array_notify_parent, term)
        });
        (
            notifications,
            roots,
            combiner.euf_array_notify_replay_cache.forest_rebuilds(),
        )
    };

    let imported_order = run([first_guard, second_guard]);
    let reverse_activation = run([second_guard, first_guard]);
    assert_eq!(imported_order.0, 2);
    assert_eq!(reverse_activation.0, 2);
    assert_eq!(imported_order.1, [a, a, a]);
    assert_eq!(reverse_activation.1, imported_order.1);
    assert_eq!(imported_order.2, 1);
    assert_eq!(
        reverse_activation.2, 1,
        "incremental reason activation must not rebuild the imported forest"
    );
}
