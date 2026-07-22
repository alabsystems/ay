// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

fn mk_fact(predicate: PredicateId, level: usize) -> ReachFact {
    ReachFact {
        id: ReachFactId(0),
        predicate,
        level,
        state: ChcExpr::Bool(true),
        incoming_clause: None,
        premises: Vec::new(),
        instances: FxHashMap::default(),
    }
}

#[test]
fn add_with_cap_marks_store_saturated() {
    let pred = PredicateId(0);
    let mut store = ReachFactStore::new();

    assert_eq!(
        store.add_with_cap(mk_fact(pred, 0), 2),
        Some(ReachFactId(0))
    );
    assert_eq!(
        store.add_with_cap(mk_fact(pred, 0), 2),
        Some(ReachFactId(1))
    );
    assert_eq!(store.add_with_cap(mk_fact(pred, 0), 2), None);
    assert!(store.saturated());

    assert_eq!(
        store.ids_for_predicate_level(pred, 0),
        &[ReachFactId(0), ReachFactId(1)]
    );
}
