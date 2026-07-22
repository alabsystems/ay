// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::{
    discover_divisibility_patterns, extract_variable_values, infer_divisibility,
    DivisibilityConstraint,
};
use crate::{ChcExpr, ChcSort, ChcVar};
use ay_core::kani_compat::DetHashMap as FxHashMap;

#[test]
fn test_infer_divisibility_all_even() {
    let values = vec![0, 2, 4, 6, 100];
    assert_eq!(infer_divisibility(&values, 2), Some(0));
}

#[test]
fn test_infer_divisibility_all_odd() {
    let values = vec![1, 3, 5, 7, 101];
    assert_eq!(infer_divisibility(&values, 2), Some(1));
}

#[test]
fn test_infer_divisibility_mixed_parity() {
    let values = vec![1, 2, 3, 4];
    assert_eq!(infer_divisibility(&values, 2), None);
}

#[test]
fn test_infer_divisibility_mod_3() {
    // All values are 1 mod 3
    let values = vec![1, 4, 7, 10, 13];
    assert_eq!(infer_divisibility(&values, 3), Some(1));
}

#[test]
fn test_infer_divisibility_negative_values() {
    // Euclidean remainder: -3 mod 2 = 1, not -1
    let values = vec![-3, -1, 1, 3, 5];
    assert_eq!(infer_divisibility(&values, 2), Some(1));
}

#[test]
fn test_infer_divisibility_empty() {
    assert_eq!(infer_divisibility(&[], 2), None);
}

#[test]
fn test_infer_divisibility_single_value() {
    // Single value trivially satisfies any divisibility
    let values = vec![5];
    assert_eq!(infer_divisibility(&values, 2), Some(1));
}

#[test]
fn test_discover_patterns_basic() {
    let mut values_per_var = FxHashMap::default();
    // x is always even
    values_per_var.insert("x".to_string(), vec![0, 2, 4, 6]);
    // y has mixed parity
    values_per_var.insert("y".to_string(), vec![1, 2, 3, 4]);

    let patterns = discover_divisibility_patterns(&values_per_var);

    // Should find x mod 2 = 0
    assert!(patterns
        .iter()
        .any(|c| c.var_name == "x" && c.modulus == 2 && c.remainder == 0));
    // Should NOT find any pattern for y with modulus 2
    assert!(!patterns.iter().any(|c| c.var_name == "y" && c.modulus == 2));
}

#[test]
fn test_discover_patterns_skips_constants() {
    let mut values_per_var = FxHashMap::default();
    // x is constant (all same value) - should skip
    values_per_var.insert("x".to_string(), vec![5, 5, 5, 5]);

    let patterns = discover_divisibility_patterns(&values_per_var);

    // Should NOT find divisibility patterns for constant values
    assert!(patterns.is_empty());
}

#[test]
fn test_constraint_to_expr() {
    let constraint = DivisibilityConstraint {
        var_name: "x".to_string(),
        modulus: 2,
        remainder: 0,
    };
    let var = ChcVar::new("x", ChcSort::Int);
    let expr = constraint.to_expr(&var);

    // Should produce (= (mod x 2) 0)
    let expected = ChcExpr::eq(
        ChcExpr::mod_op(ChcExpr::var(var), ChcExpr::Int(2)),
        ChcExpr::Int(0),
    );
    assert_eq!(format!("{expr}"), format!("{}", expected));
}

#[test]
fn test_extract_variable_values() {
    let mut model1 = FxHashMap::default();
    model1.insert("x".to_string(), 10);
    model1.insert("y".to_string(), 5);

    let mut model2 = FxHashMap::default();
    model2.insert("x".to_string(), 20);
    model2.insert("y".to_string(), 15);

    let models = vec![model1, model2];
    let int_vars = vec![
        ChcVar::new("x", ChcSort::Int),
        ChcVar::new("y", ChcSort::Int),
        ChcVar::new("z", ChcSort::Bool), // Should be skipped
    ];

    let result = extract_variable_values(&models, &int_vars);

    assert_eq!(result.get("x"), Some(&vec![10, 20]));
    assert_eq!(result.get("y"), Some(&vec![5, 15]));
    assert!(!result.contains_key("z")); // Bool var skipped
}

#[test]
fn test_discover_patterns_filters_redundant() {
    let mut values_per_var = FxHashMap::default();
    // x: All multiples of 4 (also multiples of 2)
    // Should find mod 2 = 0, but NOT mod 4 = 0 (redundant)
    values_per_var.insert("x".to_string(), vec![0, 4, 8, 12]);

    let patterns = discover_divisibility_patterns(&values_per_var);

    // Should find mod 2 = 0
    assert!(patterns
        .iter()
        .any(|c| c.var_name == "x" && c.modulus == 2 && c.remainder == 0));
    // Should NOT find mod 4 = 0 (redundant, implied by mod 2 = 0)
    assert!(!patterns.iter().any(|c| c.var_name == "x" && c.modulus == 4));
}

#[test]
fn test_discover_patterns_keeps_non_redundant() {
    let mut values_per_var = FxHashMap::default();
    // x: All values are 2 mod 4 (even but not divisible by 4)
    // mod 2 = 0, mod 4 = 2 - mod 4 is NOT redundant here
    values_per_var.insert("x".to_string(), vec![2, 6, 10, 14]);

    let patterns = discover_divisibility_patterns(&values_per_var);

    // Should find mod 2 = 0
    assert!(patterns
        .iter()
        .any(|c| c.var_name == "x" && c.modulus == 2 && c.remainder == 0));
    // Should also find mod 4 = 2 (not redundant - different info)
    assert!(patterns
        .iter()
        .any(|c| c.var_name == "x" && c.modulus == 4 && c.remainder == 2));
}
