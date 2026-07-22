// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::ChcSort;

fn make_var(name: &str) -> ChcExpr {
    ChcExpr::Var(ChcVar::new(name, ChcSort::Int))
}

fn make_pattern_var(name: &str) -> ChcVar {
    ChcVar::new(name, ChcSort::Int)
}

#[test]
fn test_basic_match_extracts_values() {
    let pv = make_pattern_var("__gg_k0");
    let pattern = ChcExpr::gt(make_var("x"), ChcExpr::Var(pv.clone()));
    let instance = ChcExpr::gt(make_var("x"), ChcExpr::Int(5));

    let mut m = SemanticMatcher::new();
    let (pos, values) = m.matches_signed(&pattern, &[pv], &instance).unwrap();
    assert!(pos);
    assert_eq!(values, vec![5]);
}

#[test]
fn test_arith_equivalence_le_not_gt() {
    let pv = make_pattern_var("__gg_k0");
    let pattern = ChcExpr::le(make_var("x"), ChcExpr::Var(pv.clone()));
    let instance = ChcExpr::not(ChcExpr::gt(make_var("x"), ChcExpr::Int(5)));

    let mut m = SemanticMatcher::new();
    let (pos, values) = m.matches_signed(&pattern, &[pv], &instance).unwrap();
    assert!(pos);
    assert_eq!(values, vec![5]);
}

#[test]
fn test_arith_equivalence_not_gt_le() {
    let pv = make_pattern_var("__gg_k0");
    let pattern = ChcExpr::not(ChcExpr::gt(make_var("x"), ChcExpr::Var(pv.clone())));
    let instance = ChcExpr::le(make_var("x"), ChcExpr::Int(5));

    let mut m = SemanticMatcher::new();
    let (pos, values) = m.matches_signed(&pattern, &[pv], &instance).unwrap();
    assert!(pos);
    assert_eq!(values, vec![5]);
}

#[test]
fn test_linear_solve_binds_pattern_var() {
    let pv = make_pattern_var("__gg_k0");
    let pattern = ChcExpr::add(ChcExpr::Var(pv.clone()), ChcExpr::Int(3));
    let instance = ChcExpr::Int(10);

    let mut m = SemanticMatcher::new();
    let (pos, values) = m.matches_signed(&pattern, &[pv], &instance).unwrap();
    assert!(pos);
    assert_eq!(values, vec![7]);
}

#[test]
fn test_arith_equivalence_ge_not_lt() {
    let pv = make_pattern_var("__gg_k0");
    let pattern = ChcExpr::ge(make_var("x"), ChcExpr::Var(pv.clone()));
    let instance = ChcExpr::not(ChcExpr::lt(make_var("x"), ChcExpr::Int(5)));

    let mut m = SemanticMatcher::new();
    let (pos, values) = m.matches_signed(&pattern, &[pv], &instance).unwrap();
    assert!(pos);
    assert_eq!(values, vec![5]);
}

#[test]
fn test_arith_equivalence_gt_not_le() {
    let pv = make_pattern_var("__gg_k0");
    let pattern = ChcExpr::gt(make_var("x"), ChcExpr::Var(pv.clone()));
    let instance = ChcExpr::not(ChcExpr::le(make_var("x"), ChcExpr::Int(5)));

    let mut m = SemanticMatcher::new();
    let (pos, values) = m.matches_signed(&pattern, &[pv], &instance).unwrap();
    assert!(pos);
    assert_eq!(values, vec![5]);
}

#[test]
fn test_arith_equivalence_lt_not_ge() {
    let pv = make_pattern_var("__gg_k0");
    let pattern = ChcExpr::lt(make_var("x"), ChcExpr::Var(pv.clone()));
    let instance = ChcExpr::not(ChcExpr::ge(make_var("x"), ChcExpr::Int(5)));

    let mut m = SemanticMatcher::new();
    let (pos, values) = m.matches_signed(&pattern, &[pv], &instance).unwrap();
    assert!(pos);
    assert_eq!(values, vec![5]);
}

#[test]
fn test_arith_equivalence_eq_not_ne() {
    let pv = make_pattern_var("__gg_k0");
    let pattern = ChcExpr::eq(make_var("x"), ChcExpr::Var(pv.clone()));
    let instance = ChcExpr::not(ChcExpr::ne(make_var("x"), ChcExpr::Int(5)));

    let mut m = SemanticMatcher::new();
    let (pos, values) = m.matches_signed(&pattern, &[pv], &instance).unwrap();
    assert!(pos);
    assert_eq!(values, vec![5]);
}

#[test]
fn test_top_level_signed_match_strips_not() {
    let pv = make_pattern_var("__gg_k0");
    let pattern = ChcExpr::not(ChcExpr::gt(make_var("x"), ChcExpr::Var(pv.clone())));
    let instance = ChcExpr::gt(make_var("x"), ChcExpr::Int(5));

    let mut m = SemanticMatcher::new();
    let (pos, values) = m.matches_signed(&pattern, &[pv], &instance).unwrap();
    assert!(!pos);
    assert_eq!(values, vec![5]);
}
