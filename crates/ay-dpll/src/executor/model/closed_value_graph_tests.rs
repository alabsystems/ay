// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn nested_const_array_rechecks_child_stamp_while_root_is_current() {
    let mut terms = TermStore::new();
    let zero = terms.mk_int(BigInt::from(0));
    let inner = terms.mk_const_array(Sort::Bool, zero);
    let outer = terms.mk_const_array(Sort::Int, inner);
    let outer_sort = terms.sort(outer).clone();
    let outer_stamp = terms.entry_stamp(outer).expect("live outer value");
    let mut graph = StampedClosedValueGraph::capture(&terms, outer, &outer_sort)
        .expect("nested const-array is a closed value graph");
    assert_eq!(graph.slots.len(), 3, "root and both descendants are pinned");
    assert!(graph.is_current(&terms, outer, &outer_sort));

    let unrelated = terms.mk_int(BigInt::from(1));
    let unrelated_stamp = terms
        .entry_stamp(unrelated)
        .expect("live unrelated literal");
    let child_slot = graph
        .slots
        .iter()
        .position(|(term, _)| *term == inner)
        .expect("inner const-array is reachable");
    graph.slots[child_slot].1 = unrelated_stamp;

    assert_eq!(terms.entry_stamp(outer), Some(outer_stamp));
    assert!(
        !graph.is_current(&terms, outer, &outer_sort),
        "a root-only currentness check must not accept a stale child slot"
    );
}
