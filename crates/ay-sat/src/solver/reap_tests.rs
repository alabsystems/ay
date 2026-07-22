// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_reap_push_pop_ordered() {
    let mut r = Reap::new();
    r.push(5);
    r.push(3);
    r.push(7);
    r.push(1);
    assert_eq!(r.pop(), 1);
    assert_eq!(r.pop(), 3);
    assert_eq!(r.pop(), 5);
    assert_eq!(r.pop(), 7);
    assert!(r.is_empty());
}

#[test]
fn test_reap_duplicates() {
    let mut r = Reap::new();
    r.push(4);
    r.push(4);
    r.push(4);
    assert_eq!(r.pop(), 4);
    assert_eq!(r.pop(), 4);
    assert_eq!(r.pop(), 4);
    assert!(r.is_empty());
}

#[test]
fn test_reap_single_element() {
    let mut r = Reap::new();
    r.push(42);
    assert_eq!(r.pop(), 42);
    assert!(r.is_empty());
}

#[test]
fn test_reap_clear() {
    let mut r = Reap::new();
    r.push(1);
    r.push(2);
    r.clear();
    assert!(r.is_empty());
    r.push(10);
    assert_eq!(r.pop(), 10);
}

#[test]
fn test_reap_sequential() {
    let mut r = Reap::new();
    for i in (0..100).rev() {
        r.push(i);
    }
    for i in 0..100 {
        assert_eq!(r.pop(), i);
    }
}
