// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::PredicateId;

#[test]
fn test_priority_ordering() {
    let mut queue = StateQueue::new();

    // Non-query with many predicates
    let s1 = AbstractState::new(PredicateId(0), vec![1, 2, 3]);
    queue.enqueue(vec![s1], 0, false);

    // Query clause (should have highest priority)
    let s2 = AbstractState::new(PredicateId(0), vec![1, 2, 3]);
    queue.enqueue(vec![s2], 1, true);

    // Non-query with few predicates
    let s3 = AbstractState::new(PredicateId(0), vec![]);
    queue.enqueue(vec![s3], 2, false);

    // Query should come first
    let first = queue.dequeue().unwrap();
    assert!(first.is_query);

    // Then empty predicates
    let second = queue.dequeue().unwrap();
    assert_eq!(second.clause_index, 2);

    // Then many predicates
    let third = queue.dequeue().unwrap();
    assert_eq!(third.clause_index, 0);
}

#[test]
fn test_time_increment() {
    let mut queue = StateQueue::new();

    let s1 = AbstractState::new(PredicateId(0), vec![]);
    queue.enqueue(vec![s1], 0, false);
    let first = queue.dequeue().unwrap();
    assert_eq!(first.birth_time, 0);

    queue.inc_time();
    let s2 = AbstractState::new(PredicateId(0), vec![]);
    queue.enqueue(vec![s2], 0, false);
    let second = queue.dequeue().unwrap();
    assert_eq!(second.birth_time, 1);
}
