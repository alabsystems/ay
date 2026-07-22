// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_dense_domain_basic() {
    let d = Domain::new(1, 10);
    assert_eq!(d.lb(), 1);
    assert_eq!(d.ub(), 10);
    assert_eq!(d.size(), 10);
    assert!(!d.is_fixed());
    assert!(d.contains(1));
    assert!(d.contains(5));
    assert!(d.contains(10));
    assert!(!d.contains(0));
    assert!(!d.contains(11));
}

#[test]
fn test_singleton() {
    let d = Domain::singleton(42);
    assert!(d.is_fixed());
    assert_eq!(d.size(), 1);
    assert!(d.contains(42));
    assert!(!d.contains(41));
}

#[test]
fn test_from_values_sparse() {
    let d = Domain::from_values(&[1, 3, 5, 7]);
    assert_eq!(d.lb(), 1);
    assert_eq!(d.ub(), 7);
    assert_eq!(d.size(), 4);
    assert!(d.contains(1));
    assert!(!d.contains(2));
    assert!(d.contains(3));
    assert!(!d.contains(4));
    assert!(d.contains(5));
}

#[test]
fn test_set_lb() {
    let mut d = Domain::new(1, 10);
    assert!(d.set_lb(5).unwrap());
    assert_eq!(d.lb(), 5);
    assert!(!d.set_lb(3).unwrap()); // no-op
    assert!(d.set_lb(10).unwrap());
    assert!(d.is_fixed());
    assert!(d.set_lb(11).is_err()); // wipeout
}

#[test]
fn test_set_ub() {
    let mut d = Domain::new(1, 10);
    assert!(d.set_ub(5).unwrap());
    assert_eq!(d.ub(), 5);
    assert!(!d.set_ub(7).unwrap()); // no-op
    assert!(d.set_ub(1).unwrap());
    assert!(d.is_fixed());
    assert!(d.set_ub(0).is_err()); // wipeout
}

#[test]
fn test_remove_endpoint() {
    let mut d = Domain::new(1, 5);
    assert!(d.remove(1).unwrap());
    assert_eq!(d.lb(), 2);
    assert!(d.remove(5).unwrap());
    assert_eq!(d.ub(), 4);
}

#[test]
fn test_fix_variable() {
    let mut d = Domain::new(1, 10);
    assert!(d.fix(5).unwrap());
    assert!(d.is_fixed());
    assert_eq!(d.lb(), 5);
    assert_eq!(d.ub(), 5);
}

#[test]
fn test_fix_out_of_domain() {
    let mut d = Domain::new(1, 10);
    assert!(d.fix(11).is_err());
}

#[test]
fn test_remove_dense_interior_materializes_hole() {
    let mut d = Domain::new(1, 5);
    assert!(d.remove(3).unwrap());
    assert!(d.contains(1));
    assert!(d.contains(2));
    assert!(!d.contains(3));
    assert!(d.contains(4));
    assert!(d.contains(5));
    assert_eq!(d.lb(), 1);
    assert_eq!(d.ub(), 5);
    assert_eq!(d.size(), 4);
}

#[test]
fn test_sparse_bounds_skip_missing_values() {
    let mut d = Domain::from_values(&[1, 3, 5]);
    assert!(d.set_lb(2).unwrap());
    assert_eq!(d.lb(), 3);
    assert!(d.set_ub(4).unwrap());
    assert_eq!(d.ub(), 3);
    assert!(d.is_fixed());
    assert_eq!(d.size(), 1);
}

#[test]
fn test_sparse_fix_clears_stale_membership() {
    let mut d = Domain::from_values(&[1, 3, 5]);
    assert!(d.fix(3).unwrap());
    assert!(d.is_fixed());
    assert_eq!(d.lb(), 3);
    assert_eq!(d.ub(), 3);
    assert_eq!(d.size(), 1);
    assert!(d.contains(3));
    assert!(!d.contains(1));
    assert!(!d.contains(5));
}

#[test]
fn test_sparse_values_follow_current_bounds() {
    let mut d = Domain::from_values(&[1, 100, 200]);
    assert_eq!(d.values(), vec![1, 100, 200]);
    assert!(d.set_lb(50).unwrap());
    assert_eq!(d.values(), vec![100, 200]);
    assert!(d.set_ub(150).unwrap());
    assert_eq!(d.values(), vec![100]);
}
