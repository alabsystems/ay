// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::domain::Domain;

#[test]
fn test_register_and_bounds() {
    let mut trail = IntegerTrail::new();
    let x = trail.register(0, 10);
    assert_eq!(trail.lb(x), 0);
    assert_eq!(trail.ub(x), 10);
    assert!(!trail.is_fixed(x));
}

#[test]
fn test_set_lb_and_backtrack() {
    let mut trail = IntegerTrail::new();
    let x = trail.register(0, 10);
    let lit = Literal::positive(ay_sat::Variable::new(0));

    trail.push_level();
    trail.set_lb(x, 5, lit, None).unwrap();
    assert_eq!(trail.lb(x), 5);

    trail.backtrack_to(0);
    assert_eq!(trail.lb(x), 0);
}

#[test]
fn test_set_ub_wipeout() {
    let mut trail = IntegerTrail::new();
    let x = trail.register(5, 10);
    let lit = Literal::positive(ay_sat::Variable::new(0));

    // Try to set ub below lb
    assert!(trail.set_ub(x, 4, lit, None).is_err());
}

#[test]
fn test_fixed_variable() {
    let mut trail = IntegerTrail::new();
    let x = trail.register(0, 10);
    let lit_lb = Literal::positive(ay_sat::Variable::new(0));
    let lit_ub = Literal::positive(ay_sat::Variable::new(1));

    trail.set_lb(x, 5, lit_lb, None).unwrap();
    trail.set_ub(x, 5, lit_ub, None).unwrap();
    assert!(trail.is_fixed(x));
    assert_eq!(trail.fixed_value(x), Some(5));
}

#[test]
fn test_multilevel_backtrack() {
    let mut trail = IntegerTrail::new();
    let x = trail.register(0, 100);
    let lit = Literal::positive(ay_sat::Variable::new(0));

    trail.push_level(); // level 1
    trail.set_lb(x, 10, lit, None).unwrap();

    trail.push_level(); // level 2
    trail.set_lb(x, 50, lit, None).unwrap();

    trail.push_level(); // level 3
    trail.set_lb(x, 90, lit, None).unwrap();

    assert_eq!(trail.lb(x), 90);
    trail.backtrack_to(1);
    assert_eq!(trail.lb(x), 10);
    trail.backtrack_to(0);
    assert_eq!(trail.lb(x), 0);
}

#[test]
fn test_sparse_domain_register_and_backtrack() {
    let mut trail = IntegerTrail::new();
    let x = trail.register_domain(Domain::from_values(&[1, 3, 5]));
    let lit = Literal::positive(ay_sat::Variable::new(0));

    assert!(trail.contains(x, 1));
    assert!(!trail.contains(x, 2));
    assert!(trail.contains(x, 3));
    assert!(!trail.contains(x, 4));
    assert!(trail.contains(x, 5));

    trail.push_level();
    trail.set_lb(x, 2, lit, None).unwrap();
    assert_eq!(trail.lb(x), 3);

    trail.push_level();
    trail.set_ub(x, 4, lit, None).unwrap();
    assert_eq!(trail.ub(x), 3);
    assert!(trail.is_fixed(x));

    trail.backtrack_to(1);
    assert_eq!(trail.lb(x), 3);
    assert_eq!(trail.ub(x), 5);
    assert!(trail.contains(x, 5));

    trail.backtrack_to(0);
    assert_eq!(trail.lb(x), 1);
    assert_eq!(trail.ub(x), 5);
    assert!(!trail.contains(x, 2));
    assert!(!trail.contains(x, 4));
}

#[test]
fn test_sparse_domain_values_follow_current_bounds() {
    let mut trail = IntegerTrail::new();
    let x = trail.register_domain(Domain::from_values(&[1, 100, 200]));
    let lit = Literal::positive(ay_sat::Variable::new(0));

    assert_eq!(trail.domain_size(x), 3);
    assert_eq!(trail.values(x), vec![1, 100, 200]);

    trail.set_lb(x, 50, lit, None).unwrap();
    assert_eq!(trail.domain_size(x), 2);
    assert_eq!(trail.values(x), vec![100, 200]);

    trail.set_ub(x, 150, lit, None).unwrap();
    assert_eq!(trail.domain_size(x), 1);
    assert_eq!(trail.values(x), vec![100]);
}
