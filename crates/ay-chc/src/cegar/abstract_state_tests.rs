// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn test_subsumption_empty() {
    let s1 = AbstractState::new(PredicateId(0), vec![]);
    let s2 = AbstractState::new(PredicateId(0), vec![1, 2]);

    // Empty predicates subsumes any state with same relation
    assert!(s1.subsumes(&s2));
    assert!(!s2.subsumes(&s1));
}

#[test]
fn test_subsumption_subset() {
    let s1 = AbstractState::new(PredicateId(0), vec![1]);
    let s2 = AbstractState::new(PredicateId(0), vec![1, 2]);

    assert!(s1.subsumes(&s2));
    assert!(!s2.subsumes(&s1));
}

#[test]
fn test_subsumption_different_relations() {
    let s1 = AbstractState::new(PredicateId(0), vec![1]);
    let s2 = AbstractState::new(PredicateId(1), vec![1, 2]);

    // Different relations never subsume
    assert!(!s1.subsumes(&s2));
    assert!(!s2.subsumes(&s1));
}
