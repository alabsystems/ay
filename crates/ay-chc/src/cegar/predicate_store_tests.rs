// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_add_and_retrieve() {
    let mut store = PredicateStore::new();

    let _pred0 = store.add_predicate(PredicateId(0), ChcExpr::Bool(true));
    let _pred1 = store.add_predicate(PredicateId(0), ChcExpr::Bool(false));
    let _pred2 = store.add_predicate(PredicateId(1), ChcExpr::Bool(true));

    assert_eq!(store.len(), 3);
    assert_eq!(store.predicates_for_relation(PredicateId(0)).len(), 2);
    assert_eq!(store.predicates_for_relation(PredicateId(1)).len(), 1);
}
