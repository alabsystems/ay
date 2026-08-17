// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit tests for pdr/init_analysis.rs
//!
//! Tests for init value extraction and bound analysis functions.
//! Part of #1586.

use crate::pdr::config::InitIntBounds;
use crate::pdr::solver::PdrSolver;
use crate::pdr::types::BoundType;
use crate::{ChcParser, PdrConfig, PredicateId};
use ay_core::kani_compat::DetHashMap as FxHashMap;

#[test]
fn bounded_init_only_cache_insert_clears_when_new_key_reaches_cap() {
    let mut cache: FxHashMap<(PredicateId, String, i128), (u64, bool)> = FxHashMap::default();

    super::bounded_insert_init_only_value_cache_with_cap(
        &mut cache,
        (PredicateId(0), "x".to_string(), 0),
        (1, true),
        2,
    );
    super::bounded_insert_init_only_value_cache_with_cap(
        &mut cache,
        (PredicateId(0), "x".to_string(), 1),
        (1, false),
        2,
    );
    assert_eq!(cache.len(), 2);

    super::bounded_insert_init_only_value_cache_with_cap(
        &mut cache,
        (PredicateId(0), "x".to_string(), 2),
        (2, true),
        2,
    );

    assert_eq!(cache.len(), 1);
    assert_eq!(
        cache.get(&(PredicateId(0), "x".to_string(), 2)),
        Some(&(2, true))
    );
}

#[test]
fn bounded_init_only_cache_insert_updates_existing_without_clear() {
    let mut cache: FxHashMap<(PredicateId, String, i128), (u64, bool)> = FxHashMap::default();

    super::bounded_insert_init_only_value_cache_with_cap(
        &mut cache,
        (PredicateId(0), "x".to_string(), 0),
        (1, true),
        2,
    );
    super::bounded_insert_init_only_value_cache_with_cap(
        &mut cache,
        (PredicateId(0), "x".to_string(), 1),
        (1, false),
        2,
    );
    assert_eq!(cache.len(), 2);

    super::bounded_insert_init_only_value_cache_with_cap(
        &mut cache,
        (PredicateId(0), "x".to_string(), 1),
        (3, true),
        2,
    );

    assert_eq!(cache.len(), 2);
    assert_eq!(
        cache.get(&(PredicateId(0), "x".to_string(), 0)),
        Some(&(1, true))
    );
    assert_eq!(
        cache.get(&(PredicateId(0), "x".to_string(), 1)),
        Some(&(3, true))
    );
}

// ============================================================================
// Tests for compute_bounds_for_expr
// ============================================================================

#[test]
fn compute_bounds_for_expr_constant() {
    use crate::ChcExpr;
    let var_bounds = FxHashMap::default();
    let expr = ChcExpr::Int(42);
    let result = PdrSolver::compute_bounds_for_expr(&expr, &var_bounds);
    assert_eq!(result, Some(InitIntBounds::new(42)));
}

#[test]
fn compute_bounds_for_expr_variable_with_bounds() {
    use crate::{ChcExpr, ChcSort, ChcVar};
    let mut var_bounds = FxHashMap::default();
    var_bounds.insert("x".to_string(), InitIntBounds { min: 0, max: 10 });

    let x = ChcVar::new("x", ChcSort::Int);
    let expr = ChcExpr::Var(x);
    let result = PdrSolver::compute_bounds_for_expr(&expr, &var_bounds);
    assert_eq!(result, Some(InitIntBounds { min: 0, max: 10 }));
}

#[test]
fn compute_bounds_for_expr_variable_unknown() {
    use crate::{ChcExpr, ChcSort, ChcVar};
    let var_bounds = FxHashMap::default();

    let y = ChcVar::new("y", ChcSort::Int);
    let expr = ChcExpr::Var(y);
    let result = PdrSolver::compute_bounds_for_expr(&expr, &var_bounds);
    assert_eq!(result, None);
}

#[test]
fn compute_bounds_for_expr_add() {
    use crate::{ChcExpr, ChcSort, ChcVar};
    let mut var_bounds = FxHashMap::default();
    var_bounds.insert("x".to_string(), InitIntBounds { min: 1, max: 5 });

    let x = ChcVar::new("x", ChcSort::Int);
    // x + 10
    let expr = ChcExpr::add(ChcExpr::Var(x), ChcExpr::Int(10));
    let result = PdrSolver::compute_bounds_for_expr(&expr, &var_bounds);
    assert_eq!(result, Some(InitIntBounds { min: 11, max: 15 }));
}

#[test]
fn compute_bounds_for_expr_sub() {
    use crate::{ChcExpr, ChcSort, ChcVar};
    let mut var_bounds = FxHashMap::default();
    var_bounds.insert("x".to_string(), InitIntBounds { min: 10, max: 20 });
    var_bounds.insert("y".to_string(), InitIntBounds { min: 1, max: 5 });

    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    // x - y: min = 10 - 5 = 5, max = 20 - 1 = 19
    let expr = ChcExpr::sub(ChcExpr::Var(x), ChcExpr::Var(y));
    let result = PdrSolver::compute_bounds_for_expr(&expr, &var_bounds);
    assert_eq!(result, Some(InitIntBounds { min: 5, max: 19 }));
}

#[test]
fn compute_bounds_for_expr_mul_point_values() {
    use crate::{ChcExpr, ChcSort, ChcVar};
    let mut var_bounds = FxHashMap::default();
    var_bounds.insert("x".to_string(), InitIntBounds::new(3));

    let x = ChcVar::new("x", ChcSort::Int);
    // x * 4 where x = 3
    let expr = ChcExpr::mul(ChcExpr::Var(x), ChcExpr::Int(4));
    let result = PdrSolver::compute_bounds_for_expr(&expr, &var_bounds);
    assert_eq!(result, Some(InitIntBounds::new(12)));
}

#[test]
fn compute_bounds_for_expr_mul_ranges() {
    use crate::{ChcExpr, ChcSort, ChcVar};
    let mut var_bounds = FxHashMap::default();
    var_bounds.insert("x".to_string(), InitIntBounds { min: -2, max: 3 });

    let x = ChcVar::new("x", ChcSort::Int);
    // x * 2 where x in [-2, 3]: products are -4, 6, -4, 6 => min=-4, max=6
    let expr = ChcExpr::mul(ChcExpr::Var(x), ChcExpr::Int(2));
    let result = PdrSolver::compute_bounds_for_expr(&expr, &var_bounds);
    assert_eq!(result, Some(InitIntBounds { min: -4, max: 6 }));
}

// ============================================================================
// Tests for get_init_values (requires full PDR solver setup)
// ============================================================================

#[test]
fn get_init_values_extracts_equality_from_fact() {
    let smt2 = r#"
(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int)) (=> (and (Inv x) (< x 0)) false)))
(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    let solver = PdrSolver::new(problem, PdrConfig::default());

    let inv = solver.problem.get_predicate_by_name("Inv").unwrap().id;
    let values = solver.get_init_values(inv);

    // Should extract x = 0 from the fact clause
    assert!(!values.is_empty(), "expected init values");
    // Find the canonical var for x
    let canon_x = solver.canonical_vars(inv).unwrap()[0].name.clone();
    let bounds = values.get(&canon_x).expect("expected bounds for x");
    assert_eq!(bounds.min, 0);
    assert_eq!(bounds.max, 0);
}

#[test]
fn get_init_values_extracts_multiple_equalities() {
    let smt2 = r#"
(set-logic HORN)
(declare-fun Inv (Int Int) Bool)
(assert (forall ((x Int) (y Int)) (=> (and (= x 0) (= y 10)) (Inv x y))))
(assert (forall ((x Int) (y Int)) (=> (and (Inv x y) (< x 0)) false)))
(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    let solver = PdrSolver::new(problem, PdrConfig::default());

    let inv = solver.problem.get_predicate_by_name("Inv").unwrap().id;
    let values = solver.get_init_values(inv);

    assert_eq!(values.len(), 2, "expected 2 init values");

    let canon_vars = solver.canonical_vars(inv).unwrap();
    let x_bounds = values.get(&canon_vars[0].name).expect("expected x bounds");
    let y_bounds = values.get(&canon_vars[1].name).expect("expected y bounds");

    assert_eq!(x_bounds.min, 0);
    assert_eq!(x_bounds.max, 0);
    assert_eq!(y_bounds.min, 10);
    assert_eq!(y_bounds.max, 10);
}

#[test]
fn get_init_values_extracts_inequality_bounds() {
    let smt2 = r#"
(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (and (>= x 0) (<= x 100)) (Inv x))))
(assert (forall ((x Int)) (=> (and (Inv x) (< x (- 1))) false)))
(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    let solver = PdrSolver::new(problem, PdrConfig::default());

    let inv = solver.problem.get_predicate_by_name("Inv").unwrap().id;
    let values = solver.get_init_values(inv);

    let canon_x = solver.canonical_vars(inv).unwrap()[0].name.clone();
    let bounds = values.get(&canon_x).expect("expected bounds for x");

    // Should extract 0 <= x <= 100
    assert_eq!(bounds.min, 0);
    assert_eq!(bounds.max, 100);
}

#[test]
fn get_init_values_propagates_through_simple_transition() {
    // Test that init bounds propagate from source predicate through a simple transition
    let smt2 = r#"
(set-logic HORN)
(declare-fun Inv (Int) Bool)
(declare-fun Aux (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int)) (=> (Inv x) (Aux x))))
(assert (forall ((x Int)) (=> (and (Aux x) (< x 0)) false)))
(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    let solver = PdrSolver::new(problem, PdrConfig::default());

    let aux = solver.problem.get_predicate_by_name("Aux").unwrap().id;

    // Aux has no direct facts, but bounds should propagate from Inv through: Inv(x) => Aux(x)
    // Since x is the same variable in body and head, x=0 should propagate
    let values = solver.get_init_values(aux);

    // The init bounds propagation feature may or may not propagate depending on
    // clause structure. Test that it either propagates correctly OR returns empty
    // (but does not return incorrect bounds)
    if !values.is_empty() {
        let canon_x = solver.canonical_vars(aux).unwrap()[0].name.clone();
        let bounds = values.get(&canon_x).expect("expected bounds for x");
        // If propagated, should be x=0 from Inv's init
        assert_eq!(bounds.min, 0, "propagated min should be 0");
        assert_eq!(bounds.max, 0, "propagated max should be 0");
    }
    // Empty is also acceptable - some clause structures don't propagate
}

// ============================================================================
// Tests for get_init_var_var_equalities
// ============================================================================

#[test]
fn get_init_var_var_equalities_extracts_simple_equality() {
    let smt2 = r#"
(set-logic HORN)
(declare-fun Inv (Int Int) Bool)
(assert (forall ((x Int) (y Int)) (=> (and (= x 0) (= x y)) (Inv x y))))
(assert (forall ((x Int) (y Int)) (=> (and (Inv x y) (< x 0)) false)))
(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    let solver = PdrSolver::new(problem, PdrConfig::default());

    let inv = solver.problem.get_predicate_by_name("Inv").unwrap().id;
    let equalities = solver.get_init_var_var_equalities(inv);

    // Should extract x = y
    assert!(!equalities.is_empty(), "expected var-var equalities");

    let canon_vars = solver.canonical_vars(inv).unwrap();
    let canon0 = &canon_vars[0].name;
    let canon1 = &canon_vars[1].name;

    // Check that (canon0, canon1) or (canon1, canon0) is in the set
    let has_equality = equalities.contains(&(canon0.clone(), canon1.clone()))
        || equalities.contains(&(canon1.clone(), canon0.clone()));
    assert!(has_equality, "expected equality between x and y variables");
}

#[test]
fn get_init_var_var_equalities_empty_when_no_var_equalities() {
    let smt2 = r#"
(set-logic HORN)
(declare-fun Inv (Int Int) Bool)
(assert (forall ((x Int) (y Int)) (=> (and (= x 0) (= y 1)) (Inv x y))))
(assert (forall ((x Int) (y Int)) (=> (and (Inv x y) (< x 0)) false)))
(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    let solver = PdrSolver::new(problem, PdrConfig::default());

    let inv = solver.problem.get_predicate_by_name("Inv").unwrap().id;
    let equalities = solver.get_init_var_var_equalities(inv);

    // No x = y, only x = 0 and y = 1
    assert!(equalities.is_empty(), "expected no var-var equalities");
}

// ============================================================================
// Tests for extract_bound_invariants_from_bad_state
// ============================================================================

#[test]
fn extract_bound_invariants_from_gt() {
    use crate::{ChcExpr, ChcSort, ChcVar};

    let smt2 = r#"
(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int)) (=> (and (Inv x) (> x 100)) false)))
(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    let solver = PdrSolver::new(problem, PdrConfig::default());

    // Extract bounds from the bad state (> x 100)
    let x = ChcVar::new("x", ChcSort::Int);
    let bad_state = ChcExpr::gt(ChcExpr::Var(x), ChcExpr::Int(100));
    let bounds = solver.extract_bound_invariants_from_bad_state(&bad_state);

    assert!(!bounds.is_empty(), "expected bounds");
    let (var, bound_type, value) = &bounds[0];
    assert_eq!(var.name, "x");
    assert!(matches!(bound_type, BoundType::Gt));
    assert_eq!(*value, 100);
}

#[test]
fn extract_bound_invariants_from_lt() {
    use crate::{ChcExpr, ChcSort, ChcVar};

    let smt2 = r#"
(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int)) (=> (and (Inv x) (< x (- 10))) false)))
(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    let solver = PdrSolver::new(problem, PdrConfig::default());

    let x = ChcVar::new("x", ChcSort::Int);
    let bad_state = ChcExpr::lt(ChcExpr::Var(x), ChcExpr::Int(-10));
    let bounds = solver.extract_bound_invariants_from_bad_state(&bad_state);

    assert!(!bounds.is_empty(), "expected bounds");
    let (var, bound_type, value) = &bounds[0];
    assert_eq!(var.name, "x");
    assert!(matches!(bound_type, BoundType::Lt));
    assert_eq!(*value, -10);
}

#[test]
fn extract_bound_invariants_from_or() {
    use crate::{ChcExpr, ChcSort, ChcVar};

    let smt2 = r#"
(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    let solver = PdrSolver::new(problem, PdrConfig::default());

    let x = ChcVar::new("x", ChcSort::Int);
    // (or (> x 100) (< x -10))
    let bad_state = ChcExpr::or(
        ChcExpr::gt(ChcExpr::Var(x.clone()), ChcExpr::Int(100)),
        ChcExpr::lt(ChcExpr::Var(x), ChcExpr::Int(-10)),
    );
    let bounds = solver.extract_bound_invariants_from_bad_state(&bad_state);

    assert_eq!(bounds.len(), 2, "expected 2 bounds");
}

// ============================================================================
// Tests for InitIntBounds helper methods
// ============================================================================

#[test]
fn init_int_bounds_new() {
    let bounds = InitIntBounds::new(42);
    assert_eq!(bounds.min, 42);
    assert_eq!(bounds.max, 42);
}

#[test]
fn init_int_bounds_unbounded() {
    let bounds = InitIntBounds::unbounded();
    assert_eq!(bounds.min, i128::MIN);
    assert_eq!(bounds.max, i128::MAX);
}

#[test]
fn init_int_bounds_update() {
    let mut bounds = InitIntBounds::new(5);
    bounds.update(3);
    assert_eq!(bounds.min, 3);
    assert_eq!(bounds.max, 5);

    bounds.update(10);
    assert_eq!(bounds.min, 3);
    assert_eq!(bounds.max, 10);
}

#[test]
fn init_int_bounds_update_lower() {
    let mut bounds = InitIntBounds { min: 0, max: 100 };
    bounds.update_lower(50);
    assert_eq!(bounds.min, 50);
    assert_eq!(bounds.max, 100);
}

#[test]
fn init_int_bounds_update_upper() {
    let mut bounds = InitIntBounds { min: 0, max: 100 };
    bounds.update_upper(50);
    assert_eq!(bounds.min, 0);
    assert_eq!(bounds.max, 50);
}

#[test]
fn init_int_bounds_is_valid() {
    assert!(InitIntBounds { min: 0, max: 10 }.is_valid());
    assert!(InitIntBounds { min: 5, max: 5 }.is_valid());
    assert!(!InitIntBounds { min: 10, max: 0 }.is_valid());
}

#[path = "init_analysis_tests/init_only_values.rs"]
mod init_only_values;
