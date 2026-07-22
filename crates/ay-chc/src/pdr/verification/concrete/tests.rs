// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

fn int_var(name: &str) -> ChcVar {
    ChcVar::new(name, ChcSort::Int)
}

fn var(name: &str) -> ChcExpr {
    ChcExpr::var(int_var(name))
}

// ========================================================================
// concrete transition_check tests (#5539)
// ========================================================================

#[test]
fn concrete_check_5_vars_with_tight_bounds() {
    let vars: Vec<ChcVar> = (0..5).map(|i| int_var(&format!("x{i}"))).collect();

    let body = ChcExpr::Op(
        ChcOp::And,
        vars.iter()
            .enumerate()
            .flat_map(|(i, v)| {
                let val = i as i64 + 1;
                vec![
                    Arc::new(ChcExpr::ge(ChcExpr::var(v.clone()), ChcExpr::int(val))),
                    Arc::new(ChcExpr::le(ChcExpr::var(v.clone()), ChcExpr::int(val))),
                ]
            })
            .collect(),
    );

    let query = ChcExpr::Op(
        ChcOp::And,
        vars.iter()
            .enumerate()
            .map(|(i, v)| {
                Arc::new(ChcExpr::eq(
                    ChcExpr::var(v.clone()),
                    ChcExpr::int(i as i64 + 1),
                ))
            })
            .collect(),
    );
    let head = ChcExpr::Bool(true);

    let result = transition_check(&body, &head, &query);
    assert!(
        result.is_some(),
        "Tight bounds on 5 variables should make the unique assignment findable"
    );
    let model = result.unwrap();
    for i in 0..5 {
        assert_eq!(
            model.get(&format!("x{i}")),
            Some(&SmtValue::Int(i128::from(i) + 1)),
            "x{i} should be {}",
            i + 1
        );
    }
}

#[test]
fn concrete_check_8_vars_tight_bounds() {
    let vars: Vec<ChcVar> = (0..8).map(|i| int_var(&format!("x{i}"))).collect();

    let body = ChcExpr::Op(
        ChcOp::And,
        vars.iter()
            .flat_map(|v| {
                vec![
                    Arc::new(ChcExpr::ge(ChcExpr::var(v.clone()), ChcExpr::int(0))),
                    Arc::new(ChcExpr::le(ChcExpr::var(v.clone()), ChcExpr::int(0))),
                ]
            })
            .collect(),
    );

    let query = ChcExpr::Op(
        ChcOp::And,
        vars.iter()
            .map(|v| Arc::new(ChcExpr::eq(ChcExpr::var(v.clone()), ChcExpr::int(0))))
            .collect(),
    );
    let head = ChcExpr::Bool(true);

    let result = transition_check(&body, &head, &query);
    assert!(
        result.is_some(),
        "Tight bounds on 8 variables should find all-zeros"
    );
    let model = result.unwrap();
    for i in 0..8 {
        assert_eq!(
            model.get(&format!("x{i}")),
            Some(&SmtValue::Int(0)),
            "x{i} should be 0"
        );
    }
}

#[test]
fn concrete_check_6_vars_wide_range_monte_carlo() {
    let vars: Vec<ChcVar> = (0..6).map(|i| int_var(&format!("x{i}"))).collect();

    let query = ChcExpr::Op(
        ChcOp::And,
        vars.iter()
            .map(|v| Arc::new(ChcExpr::ge(ChcExpr::var(v.clone()), ChcExpr::int(0))))
            .collect(),
    );
    let body = ChcExpr::Bool(true);
    let head = ChcExpr::Bool(true);

    let result = transition_check(&body, &head, &query);
    assert!(
        result.is_some(),
        "6-variable formula with many solutions should find a satisfying assignment via Monte Carlo"
    );
    let model = result.unwrap();
    for i in 0..6 {
        if let Some(SmtValue::Int(v)) = model.get(&format!("x{i}")) {
            assert!(*v >= 0, "x{i}={v} should be >= 0");
        }
    }
}

#[test]
fn concrete_check_handles_bounded_vars() {
    let x = int_var("x");
    let y = int_var("y");
    let z = int_var("z");
    let w = int_var("w");
    let v = int_var("v");

    let body = ChcExpr::Op(
        ChcOp::And,
        vec![
            Arc::new(ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(5))),
            Arc::new(ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::int(5))),
            Arc::new(ChcExpr::ge(ChcExpr::var(y.clone()), ChcExpr::int(3))),
            Arc::new(ChcExpr::le(ChcExpr::var(y.clone()), ChcExpr::int(3))),
            Arc::new(ChcExpr::ge(ChcExpr::var(z.clone()), ChcExpr::int(0))),
            Arc::new(ChcExpr::le(ChcExpr::var(z.clone()), ChcExpr::int(0))),
            Arc::new(ChcExpr::ge(ChcExpr::var(w.clone()), ChcExpr::int(1))),
            Arc::new(ChcExpr::le(ChcExpr::var(w.clone()), ChcExpr::int(1))),
            Arc::new(ChcExpr::ge(ChcExpr::var(v.clone()), ChcExpr::int(-2))),
            Arc::new(ChcExpr::le(ChcExpr::var(v.clone()), ChcExpr::int(-2))),
        ],
    );

    let sum = ChcExpr::Op(
        ChcOp::Add,
        vec![
            Arc::new(ChcExpr::var(x)),
            Arc::new(ChcExpr::var(y)),
            Arc::new(ChcExpr::var(z)),
            Arc::new(ChcExpr::var(w)),
            Arc::new(ChcExpr::var(v)),
        ],
    );
    let query = ChcExpr::eq(sum, ChcExpr::int(7));
    let head = ChcExpr::Bool(true);

    let result = transition_check(&body, &head, &query);
    assert!(
        result.is_some(),
        "Tight bounds should make the unique assignment findable"
    );
}

#[test]
fn concrete_check_returns_none_for_unsat_formula() {
    let x = int_var("x");
    let query = ChcExpr::and(
        ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(1)),
        ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(2)),
    );
    let body = ChcExpr::Bool(true);
    let head = ChcExpr::Bool(true);

    let result = transition_check(&body, &head, &query);
    assert!(result.is_none(), "Unsatisfiable formula should return None");
}

#[test]
fn concrete_check_empty_vars_returns_none() {
    let query = ChcExpr::Bool(true);
    let body = ChcExpr::Bool(true);
    let head = ChcExpr::Bool(true);

    let result = transition_check(&body, &head, &query);
    assert!(
        result.is_none(),
        "Formula with no Int/BV vars should return None"
    );
}

#[test]
fn xorshift64_deterministic() {
    let mut rng1 = Xorshift64::new(42);
    let mut rng2 = Xorshift64::new(42);
    for _ in 0..100 {
        assert_eq!(
            rng1.next(),
            rng2.next(),
            "same seed should produce same sequence"
        );
    }
}

#[test]
fn xorshift64_range_bounded() {
    let mut rng = Xorshift64::new(12345);
    for _ in 0..1000 {
        let v = rng.next_range(-10, 10);
        assert!((-10..=10).contains(&v), "value {v} out of range [-10, 10]");
    }
}

#[test]
fn xorshift64_range_full_i64_no_panic() {
    let mut rng = Xorshift64::new(99);
    for _ in 0..100 {
        let _ = rng.next_range(i64::MIN, i64::MAX);
    }
}

#[test]
fn xorshift64_range_wide_span_bounded() {
    let lo = -1_000_000_000_000i64;
    let hi = i64::MAX - 1;
    let mut rng = Xorshift64::new(42);
    for _ in 0..1000 {
        let v = rng.next_range(lo, hi);
        assert!(v >= lo && v <= hi, "value {v} out of range [{lo}, {hi}]");
    }
}

#[test]
fn xorshift64_range_near_extremes_bounded() {
    let mut rng = Xorshift64::new(7);
    for _ in 0..100 {
        let v = rng.next_range(0, i64::MAX);
        assert!(v >= 0, "value {v} should be non-negative");
    }
    for _ in 0..100 {
        let v = rng.next_range(i64::MIN, 0);
        assert!(v <= 0, "value {v} should be non-positive");
    }
}

#[test]
fn concrete_check_10_vars_monte_carlo_detects_large_sat_region() {
    let vars: Vec<ChcVar> = (0..10).map(|i| int_var(&format!("v{i}"))).collect();

    let query = ChcExpr::Op(
        ChcOp::And,
        vars.iter()
            .map(|v| Arc::new(ChcExpr::ge(ChcExpr::var(v.clone()), ChcExpr::int(0))))
            .collect(),
    );
    let body = ChcExpr::Bool(true);
    let head = ChcExpr::Bool(true);

    let result = transition_check(&body, &head, &query);
    assert!(
        result.is_some(),
        "10-variable formula with ~0.1% satisfying region should be found by Monte Carlo"
    );
    let model = result.unwrap();
    for i in 0..10 {
        if let Some(SmtValue::Int(v)) = model.get(&format!("v{i}")) {
            assert!(*v >= 0, "v{i}={v} should be >= 0");
        } else {
            panic!("v{i} missing from model");
        }
    }
}

#[test]
fn concrete_check_12_vars_boundary_detection() {
    let vars: Vec<ChcVar> = (0..12).map(|i| int_var(&format!("b{i}"))).collect();

    let body = ChcExpr::Op(
        ChcOp::And,
        vars.iter()
            .flat_map(|v| {
                vec![
                    Arc::new(ChcExpr::ge(ChcExpr::var(v.clone()), ChcExpr::int(0))),
                    Arc::new(ChcExpr::le(ChcExpr::var(v.clone()), ChcExpr::int(10))),
                ]
            })
            .collect(),
    );

    let query = ChcExpr::Op(
        ChcOp::And,
        vars.iter()
            .map(|v| Arc::new(ChcExpr::eq(ChcExpr::var(v.clone()), ChcExpr::int(0))))
            .collect(),
    );
    let head = ChcExpr::Bool(true);

    let result = transition_check(&body, &head, &query);
    assert!(
        result.is_some(),
        "12-variable all-zeros should be found by boundary sampling (0 is a boundary value)"
    );
    let model = result.unwrap();
    for i in 0..12 {
        assert_eq!(
            model.get(&format!("b{i}")),
            Some(&SmtValue::Int(0)),
            "b{i} should be 0"
        );
    }
}

#[test]
fn extract_int_bounds_no_overflow_on_min_int() {
    let expr = ChcExpr::lt(var("x"), ChcExpr::int(i64::MIN));
    let bounds = extract_int_bounds_from_conjuncts(&expr);
    if let Some((lo, hi)) = bounds.get("x") {
        assert!(*hi == i64::MIN, "upper bound should be clamped at i64::MIN");
        assert!(*lo <= *hi || *lo == i64::MIN, "bounds should be consistent");
    }
}

#[test]
fn concrete_check_extreme_bounds_no_overflow() {
    let x = int_var("x");
    let body = ChcExpr::and(
        ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(i64::MIN)),
        ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::int(i64::MAX)),
    );
    let query = ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(0));
    let head = ChcExpr::Bool(true);

    let result = transition_check(&body, &head, &query);
    assert!(result.is_some(), "x=0 satisfies the formula");
}

#[test]
fn hash_expr_structure_varies_across_formulas() {
    let e1 = ChcExpr::eq(var("x"), ChcExpr::int(1));
    let e2 = ChcExpr::eq(var("x"), ChcExpr::int(2));
    let e3 = ChcExpr::eq(var("y"), ChcExpr::int(1));
    let e4 = ChcExpr::ge(var("x"), ChcExpr::int(1));

    let h1 = hash_expr_structure(&e1);
    let h2 = hash_expr_structure(&e2);
    let h3 = hash_expr_structure(&e3);
    let h4 = hash_expr_structure(&e4);

    assert_ne!(h1, h2, "different constants should hash differently");
    assert_ne!(h1, h3, "different variable names should hash differently");
    assert_ne!(h1, h4, "different operators should hash differently");
}

#[test]
fn hash_expr_structure_deterministic() {
    let e = ChcExpr::and(
        ChcExpr::ge(var("x"), ChcExpr::int(0)),
        ChcExpr::le(var("y"), ChcExpr::int(10)),
    );
    let h1 = hash_expr_structure(&e);
    let h2 = hash_expr_structure(&e);
    assert_eq!(h1, h2, "same expression should produce same hash");
}

#[test]
fn extract_int_constants_from_formula() {
    let e = ChcExpr::and(
        ChcExpr::ge(var("x"), ChcExpr::int(5)),
        ChcExpr::le(var("y"), ChcExpr::int(42)),
    );
    let constants = extract_int_constants(&e);
    assert!(constants.contains(&5), "should extract 5");
    assert!(constants.contains(&42), "should extract 42");
}

#[test]
fn extract_int_constants_deduplicates() {
    let e = ChcExpr::and(
        ChcExpr::ge(var("x"), ChcExpr::int(7)),
        ChcExpr::ge(var("y"), ChcExpr::int(7)),
    );
    let constants = extract_int_constants(&e);
    assert_eq!(
        constants.iter().filter(|&&c| c == 7).count(),
        1,
        "constant 7 should appear exactly once"
    );
}

#[test]
fn monte_carlo_different_formulas_get_different_seeds() {
    let vars: Vec<ChcVar> = (0..6).map(|i| int_var(&format!("x{i}"))).collect();

    let q1 = ChcExpr::Op(
        ChcOp::And,
        vars.iter()
            .map(|v| Arc::new(ChcExpr::ge(ChcExpr::var(v.clone()), ChcExpr::int(0))))
            .collect(),
    );
    let q2 = ChcExpr::Op(
        ChcOp::And,
        vars.iter()
            .map(|v| Arc::new(ChcExpr::ge(ChcExpr::var(v.clone()), ChcExpr::int(5))))
            .collect(),
    );

    let h1 = hash_expr_structure(&q1);
    let h2 = hash_expr_structure(&q2);
    assert_ne!(
        h1, h2,
        "different formulas with same shape should produce different hashes"
    );
}

#[test]
fn concrete_check_formula_constants_as_boundary() {
    let x = int_var("x");
    let y = int_var("y");

    let query = ChcExpr::and(
        ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(37)),
        ChcExpr::eq(ChcExpr::var(y), ChcExpr::int(-23)),
    );
    let body = ChcExpr::Bool(true);
    let head = ChcExpr::Bool(true);

    let result = transition_check(&body, &head, &query);
    assert!(
        result.is_some(),
        "formula-constant extraction should make x=37, y=-23 findable as boundary values"
    );
    let model = result.unwrap();
    assert_eq!(model.get("x"), Some(&SmtValue::Int(37)));
    assert_eq!(model.get("y"), Some(&SmtValue::Int(-23)));
}

#[test]
fn concrete_check_20_vars_no_panic() {
    let vars: Vec<ChcVar> = (0..20).map(|i| int_var(&format!("w{i}"))).collect();

    let query = ChcExpr::Op(
        ChcOp::And,
        vars.iter()
            .map(|v| Arc::new(ChcExpr::ge(ChcExpr::var(v.clone()), ChcExpr::int(-100))))
            .collect(),
    );
    let body = ChcExpr::Bool(true);
    let head = ChcExpr::Bool(true);

    let result = transition_check(&body, &head, &query);
    assert!(
        result.is_some(),
        "20-variable trivially satisfiable formula must not crash"
    );
}

#[test]
fn saturating_fold_no_panic_on_large_domain() {
    let vars: Vec<ChcVar> = (0..15).map(|i| int_var(&format!("s{i}"))).collect();

    let query = ChcExpr::Op(
        ChcOp::And,
        vars.iter()
            .map(|v| Arc::new(ChcExpr::ge(ChcExpr::var(v.clone()), ChcExpr::int(0))))
            .collect(),
    );
    let body = ChcExpr::Bool(true);
    let head = ChcExpr::Bool(true);

    let _result = transition_check(&body, &head, &query);
}
