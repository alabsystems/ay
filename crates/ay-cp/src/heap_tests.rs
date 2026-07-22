// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_empty_heap() {
    let h = VarHeap::new(10);
    assert!(h.is_empty());
    assert_eq!(h.peek(), None);
}

#[test]
fn test_insert_and_pop() {
    let scores = vec![1.0, 5.0, 3.0, 2.0, 4.0];
    let mut h = VarHeap::new(5);
    for var in 0..5u32 {
        h.insert(var, &scores);
    }
    assert_eq!(h.len(), 5);
    // Should pop in descending score order: 1(5.0), 4(4.0), 2(3.0), 3(2.0), 0(1.0)
    assert_eq!(h.pop(&scores), Some(1));
    assert_eq!(h.pop(&scores), Some(4));
    assert_eq!(h.pop(&scores), Some(2));
    assert_eq!(h.pop(&scores), Some(3));
    assert_eq!(h.pop(&scores), Some(0));
    assert_eq!(h.pop(&scores), None);
}

#[test]
fn test_with_all_heapifies_correctly() {
    let scores = vec![1.0, 5.0, 3.0, 2.0, 4.0];
    let mut h = VarHeap::with_all(5, &scores);
    assert_eq!(h.pop(&scores), Some(1));
    assert_eq!(h.pop(&scores), Some(4));
    assert_eq!(h.pop(&scores), Some(2));
}

#[test]
fn test_increase_key() {
    let mut scores = vec![1.0, 2.0, 3.0];
    let mut h = VarHeap::with_all(3, &scores);
    assert_eq!(h.peek(), Some(2)); // score 3.0

    // Bump var 0's score to 10.0
    scores[0] = 10.0;
    h.increase_key(0, &scores);
    assert_eq!(h.peek(), Some(0)); // now var 0 is on top
}

#[test]
fn test_insert_duplicate_is_noop() {
    let scores = vec![1.0, 2.0];
    let mut h = VarHeap::new(2);
    h.insert(0, &scores);
    h.insert(0, &scores);
    assert_eq!(h.len(), 1);
}

#[test]
fn test_contains() {
    let scores = vec![1.0, 2.0, 3.0];
    let mut h = VarHeap::new(3);
    h.insert(1, &scores);
    assert!(!h.contains(0));
    assert!(h.contains(1));
    assert!(!h.contains(2));
}

#[test]
fn test_pop_and_reinsert() {
    let scores = vec![1.0, 5.0, 3.0];
    let mut h = VarHeap::with_all(3, &scores);
    let top = h.pop(&scores).unwrap();
    assert_eq!(top, 1);
    assert!(!h.contains(1));
    // Re-insert
    h.insert(1, &scores);
    assert!(h.contains(1));
    assert_eq!(h.peek(), Some(1));
}

#[test]
fn test_grow() {
    let scores = vec![1.0, 2.0];
    let mut h = VarHeap::new(2);
    h.insert(0, &scores);
    h.grow(5);
    // Should be able to insert var 3 now
    let extended_scores = vec![1.0, 2.0, 0.0, 10.0, 0.0];
    h.insert(3, &extended_scores);
    assert_eq!(h.peek(), Some(3));
}

#[test]
fn test_single_element() {
    let scores = vec![42.0];
    let mut h = VarHeap::new(1);
    h.insert(0, &scores);
    assert_eq!(h.pop(&scores), Some(0));
    assert!(h.is_empty());
}

#[test]
fn test_equal_scores_stable() {
    let scores = vec![1.0; 5];
    let mut h = VarHeap::with_all(5, &scores);
    // With equal scores, all pops should succeed (order is implementation-defined)
    let mut popped = Vec::new();
    while let Some(v) = h.pop(&scores) {
        popped.push(v);
    }
    assert_eq!(popped.len(), 5);
}
