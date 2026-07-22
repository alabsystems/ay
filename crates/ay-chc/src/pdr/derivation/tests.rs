// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::ChcExpr;

#[test]
fn test_derivation_store_alloc_free() {
    let mut store = DerivationStore::new();

    // Allocate first derivation
    let d1 = Derivation {
        clause_index: 0,
        head_predicate: PredicateId(0),
        head_level: 1,
        head_state: ChcExpr::Bool(true),
        query_clause: None,
        premises: vec![],
        active: 0,
        premise_rfs: vec![],
    };
    let id1 = store.alloc(d1);
    assert_eq!(id1.0, 0);

    // Allocate second derivation
    let d2 = Derivation {
        clause_index: 1,
        head_predicate: PredicateId(1),
        head_level: 2,
        head_state: ChcExpr::Bool(false),
        query_clause: Some(5),
        premises: vec![],
        active: 0,
        premise_rfs: vec![],
    };
    let id2 = store.alloc(d2);
    assert_eq!(id2.0, 1);

    // Free first, then reallocate - should reuse slot
    store.free(id1);
    let d3 = Derivation {
        clause_index: 2,
        head_predicate: PredicateId(2),
        head_level: 3,
        head_state: ChcExpr::Bool(true),
        query_clause: None,
        premises: vec![],
        active: 0,
        premise_rfs: vec![],
    };
    let id3 = store.alloc(d3);
    assert_eq!(id3.0, 0); // Reused slot 0

    // Verify contents
    assert!(store.get(id2).is_some());
    assert_eq!(store.get(id2).unwrap().clause_index, 1);
    assert!(store.get(id3).is_some());
    assert_eq!(store.get(id3).unwrap().clause_index, 2);
}

#[test]
fn test_derivation_progression() {
    let premise1 = Premise {
        predicate: PredicateId(1),
        summary: PremiseSummary::May(ChcExpr::Bool(true)),
    };
    let premise2 = Premise {
        predicate: PredicateId(2),
        summary: PremiseSummary::May(ChcExpr::Bool(true)),
    };

    let mut deriv = Derivation {
        clause_index: 0,
        head_predicate: PredicateId(0),
        head_level: 2,
        head_state: ChcExpr::Bool(true),
        query_clause: None,
        premises: vec![premise1, premise2],
        active: 0,
        premise_rfs: vec![],
    };

    // Initial state
    assert!(!deriv.is_complete());
    assert_eq!(deriv.remaining_premises(), 2);
    assert!(deriv.active_premise().is_some());
    assert_eq!(deriv.active_premise().unwrap().predicate, PredicateId(1));

    // Satisfy first premise
    let rf1 = ReachFactId(10);
    deriv.satisfy_active(rf1);
    assert!(!deriv.is_complete());
    assert_eq!(deriv.remaining_premises(), 1);
    assert_eq!(deriv.active_premise().unwrap().predicate, PredicateId(2));
    assert_eq!(deriv.premise_rfs.len(), 1);

    // Satisfy second premise
    let rf2 = ReachFactId(20);
    deriv.satisfy_active(rf2);
    assert!(deriv.is_complete());
    assert_eq!(deriv.remaining_premises(), 0);
    assert!(deriv.active_premise().is_none());
    assert_eq!(deriv.premise_rfs.len(), 2);
    assert_eq!(deriv.premise_rfs, vec![rf1, rf2]);
}
