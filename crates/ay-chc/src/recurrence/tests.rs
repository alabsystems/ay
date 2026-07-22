// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::{ChcSort, ChcVar};
use std::sync::Arc;

#[test]
fn test_analyze_transition_constant_delta() {
    let i = ChcVar::new("i", ChcSort::Int);
    let i_prime = ChcVar::new("i'", ChcSort::Int);

    let transition = ChcExpr::eq(
        ChcExpr::var(i_prime),
        ChcExpr::add(ChcExpr::var(i), ChcExpr::int(1)),
    );

    let state_vars = vec!["i".to_string()];
    let result = analyze_transition(&transition, &state_vars);

    assert!(result.is_some());
    let system = result.unwrap();
    assert_eq!(system.order.len(), 1);
    assert!(matches!(
        system.get_solution("i"),
        Some(ClosedForm::ConstantDelta { delta: 1, .. })
    ));
}

#[test]
fn test_analyze_transition_triangular() {
    let i = ChcVar::new("i", ChcSort::Int);
    let i_prime = ChcVar::new("i'", ChcSort::Int);
    let s = ChcVar::new("s", ChcSort::Int);
    let s_prime = ChcVar::new("s'", ChcSort::Int);

    let transition = ChcExpr::and(
        ChcExpr::eq(
            ChcExpr::var(i_prime),
            ChcExpr::add(ChcExpr::var(i.clone()), ChcExpr::int(1)),
        ),
        ChcExpr::eq(
            ChcExpr::var(s_prime),
            ChcExpr::add(ChcExpr::var(s), ChcExpr::var(i)),
        ),
    );

    let state_vars = vec!["i".to_string(), "s".to_string()];
    let result = analyze_transition(&transition, &state_vars);

    assert!(result.is_some());
    let system = result.unwrap();
    assert_eq!(system.solutions.len(), 2);
    assert!(matches!(
        system.get_solution("i"),
        Some(ClosedForm::ConstantDelta { delta: 1, .. })
    ));
    assert!(matches!(
        system.get_solution("s"),
        Some(ClosedForm::Polynomial { .. })
    ));
}

#[test]
fn test_extract_updates_next_convention() {
    let i = ChcVar::new("i", ChcSort::Int);
    let i_next = ChcVar::new("i_next", ChcSort::Int);

    let transition = ChcExpr::eq(
        ChcExpr::var(i_next),
        ChcExpr::add(ChcExpr::var(i), ChcExpr::int(1)),
    );

    let state_vars = vec!["i".to_string()];
    let updates = extract_updates(&transition, &state_vars);
    assert!(updates.is_some());
    assert!(updates.unwrap().contains_key("i"));
}

#[test]
fn test_negative_delta_subtraction() {
    // i' = i - 3 should yield ConstantDelta { delta: -3 }
    let i = ChcVar::new("i", ChcSort::Int);
    let i_prime = ChcVar::new("i'", ChcSort::Int);

    let transition = ChcExpr::eq(
        ChcExpr::var(i_prime),
        ChcExpr::sub(ChcExpr::var(i), ChcExpr::int(3)),
    );

    let state_vars = vec!["i".to_string()];
    let result = analyze_transition(&transition, &state_vars);
    assert!(result.is_some());
    let system = result.unwrap();
    assert!(matches!(
        system.get_solution("i"),
        Some(ClosedForm::ConstantDelta { delta: -3, .. })
    ));
}

#[test]
fn test_constant_reset() {
    // i' = 42 should yield Polynomial with constant term 42
    let i_prime = ChcVar::new("i'", ChcSort::Int);

    let transition = ChcExpr::eq(ChcExpr::var(i_prime), ChcExpr::int(42));

    let state_vars = vec!["i".to_string()];
    let result = analyze_transition(&transition, &state_vars);
    assert!(result.is_some());
    let system = result.unwrap();
    match system.get_solution("i") {
        Some(ClosedForm::Polynomial { coeffs, .. }) => {
            assert_eq!(coeffs.len(), 1);
            let constant = coeffs[0]
                .get("")
                .copied()
                .unwrap_or(Rational64::from_integer(0));
            assert_eq!(constant, Rational64::from_integer(42));
        }
        other => panic!("Expected Polynomial, got {other:?}"),
    }
}

#[test]
fn test_unchanged_variable() {
    // i' = i should yield ConstantDelta { delta: 0 }
    let i = ChcVar::new("i", ChcSort::Int);
    let i_prime = ChcVar::new("i'", ChcSort::Int);

    let transition = ChcExpr::eq(ChcExpr::var(i_prime), ChcExpr::var(i));

    let state_vars = vec!["i".to_string()];
    let result = analyze_transition(&transition, &state_vars);
    assert!(result.is_some());
    let system = result.unwrap();
    assert!(matches!(
        system.get_solution("i"),
        Some(ClosedForm::ConstantDelta { delta: 0, .. })
    ));
}

#[test]
fn test_cyclic_dependency_returns_none() {
    // x' = y + 1, y' = x + 1 forms a cycle => topological_order returns None
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let x_prime = ChcVar::new("x'", ChcSort::Int);
    let y_prime = ChcVar::new("y'", ChcSort::Int);

    let transition = ChcExpr::and(
        ChcExpr::eq(
            ChcExpr::var(x_prime),
            ChcExpr::add(ChcExpr::var(y), ChcExpr::int(1)),
        ),
        ChcExpr::eq(
            ChcExpr::var(y_prime),
            ChcExpr::add(ChcExpr::var(x), ChcExpr::int(1)),
        ),
    );

    let state_vars = vec!["x".to_string(), "y".to_string()];
    let result = analyze_transition(&transition, &state_vars);
    // Cyclic dependency: x depends on y and y depends on x
    assert!(result.is_none());
}

#[test]
fn test_no_updates_returns_none() {
    // Transition with no recognized update pattern
    let transition = ChcExpr::Bool(true);
    let state_vars = vec!["i".to_string()];
    let result = analyze_transition(&transition, &state_vars);
    assert!(result.is_none());
}

#[test]
fn test_multiple_independent_vars() {
    // i' = i + 1, j' = j + 2: two independent counters
    let i = ChcVar::new("i", ChcSort::Int);
    let j = ChcVar::new("j", ChcSort::Int);
    let i_prime = ChcVar::new("i'", ChcSort::Int);
    let j_prime = ChcVar::new("j'", ChcSort::Int);

    let transition = ChcExpr::and(
        ChcExpr::eq(
            ChcExpr::var(i_prime),
            ChcExpr::add(ChcExpr::var(i), ChcExpr::int(1)),
        ),
        ChcExpr::eq(
            ChcExpr::var(j_prime),
            ChcExpr::add(ChcExpr::var(j), ChcExpr::int(2)),
        ),
    );

    let state_vars = vec!["i".to_string(), "j".to_string()];
    let result = analyze_transition(&transition, &state_vars);
    assert!(result.is_some());
    let system = result.unwrap();
    assert_eq!(system.solutions.len(), 2);
    assert!(matches!(
        system.get_solution("i"),
        Some(ClosedForm::ConstantDelta { delta: 1, .. })
    ));
    assert!(matches!(
        system.get_solution("j"),
        Some(ClosedForm::ConstantDelta { delta: 2, .. })
    ));
}

#[test]
fn test_topological_order_deterministic() {
    // Verify that topological_order produces deterministic results
    // regardless of HashMap iteration order
    let mut updates = FxHashMap::default();
    let a = ChcVar::new("a", ChcSort::Int);
    let b = ChcVar::new("b", ChcSort::Int);
    let c = ChcVar::new("c", ChcSort::Int);
    // a' = a + 1, b' = b + a, c' = c + b
    // Dependencies: b depends on a, c depends on b
    // Expected order: a, b, c
    updates.insert(
        "a".to_string(),
        ChcExpr::add(ChcExpr::var(a.clone()), ChcExpr::int(1)),
    );
    updates.insert(
        "b".to_string(),
        ChcExpr::add(ChcExpr::var(b.clone()), ChcExpr::var(a)),
    );
    updates.insert(
        "c".to_string(),
        ChcExpr::add(ChcExpr::var(c), ChcExpr::var(b)),
    );

    let order = topological_order(&updates);
    assert!(order.is_some());
    let order = order.unwrap();
    assert_eq!(order.len(), 3);
    // a must come before b, b must come before c
    let pos_a = order.iter().position(|v| v == "a").unwrap();
    let pos_b = order.iter().position(|v| v == "b").unwrap();
    let pos_c = order.iter().position(|v| v == "c").unwrap();
    assert!(pos_a < pos_b);
    assert!(pos_b < pos_c);
}

#[test]
fn test_commuted_add_delta() {
    // i' = 5 + i (constant on the left side of addition)
    let i = ChcVar::new("i", ChcSort::Int);
    let i_prime = ChcVar::new("i'", ChcSort::Int);

    let transition = ChcExpr::eq(
        ChcExpr::var(i_prime),
        ChcExpr::add(ChcExpr::int(5), ChcExpr::var(i)),
    );

    let state_vars = vec!["i".to_string()];
    let result = analyze_transition(&transition, &state_vars);
    assert!(result.is_some());
    let system = result.unwrap();
    assert!(matches!(
        system.get_solution("i"),
        Some(ClosedForm::ConstantDelta { delta: 5, .. })
    ));
}

#[test]
fn test_quadratic_sum_coefficients() {
    // s' = s + i, i' = i + 1
    // Verify the quadratic polynomial structure:
    //   s_n = s_0 + n*i_0 + n*(n-1)/2
    let i = ChcVar::new("i", ChcSort::Int);
    let i_prime = ChcVar::new("i'", ChcSort::Int);
    let s = ChcVar::new("s", ChcSort::Int);
    let s_prime = ChcVar::new("s'", ChcSort::Int);

    let transition = ChcExpr::and(
        ChcExpr::eq(
            ChcExpr::var(i_prime),
            ChcExpr::add(ChcExpr::var(i.clone()), ChcExpr::int(1)),
        ),
        ChcExpr::eq(
            ChcExpr::var(s_prime),
            ChcExpr::add(ChcExpr::var(s), ChcExpr::var(i)),
        ),
    );

    let state_vars = vec!["i".to_string(), "s".to_string()];
    let system = analyze_transition(&transition, &state_vars).unwrap();
    match system.get_solution("s") {
        Some(ClosedForm::Polynomial { coeffs, .. }) => {
            // Degree 2 polynomial: coeffs[0] (n^0), coeffs[1] (n^1), coeffs[2] (n^2)
            assert_eq!(coeffs.len(), 3);
            // coeffs[0] should have s_0 with coefficient 1
            assert_eq!(coeffs[0].get("s"), Some(&Rational64::from_integer(1)));
            // coeffs[1] should have i_0 with coefficient 1 and constant -1/2
            assert_eq!(coeffs[1].get("i"), Some(&Rational64::from_integer(1)));
            assert_eq!(coeffs[1].get(""), Some(&Rational64::new(-1, 2)));
            // coeffs[2] should have constant 1/2
            assert_eq!(coeffs[2].get(""), Some(&Rational64::new(1, 2)));
        }
        other => panic!("Expected Polynomial, got {other:?}"),
    }
}

// --- BvToInt stripping tests (#7931) ---

#[test]
fn test_strip_bv_wrapping_bvadd() {
    // BvToInt encodes bvadd as: ite(a+b < 256, a+b, a+b - 256) for BV8
    let i = ChcVar::new("i", ChcSort::Int);
    let sum = ChcExpr::add(ChcExpr::var(i.clone()), ChcExpr::int(1));
    let bound = ChcExpr::int(256); // 2^8
    let wrapped = ChcExpr::ite(
        ChcExpr::lt(sum.clone(), bound.clone()),
        sum.clone(),
        ChcExpr::sub(sum.clone(), bound),
    );
    let stripped = strip_bv_wrapping(&wrapped);
    assert_eq!(stripped, sum);
}

#[test]
fn test_strip_bv_wrapping_bvsub() {
    // BvToInt encodes bvsub as: ite(a-b >= 0, a-b, a-b + 256) for BV8
    let i = ChcVar::new("i", ChcSort::Int);
    let diff = ChcExpr::sub(ChcExpr::var(i.clone()), ChcExpr::int(1));
    let bound = ChcExpr::int(256); // 2^8
    let wrapped = ChcExpr::ite(
        ChcExpr::ge(diff.clone(), ChcExpr::int(0)),
        diff.clone(),
        ChcExpr::add(diff.clone(), bound),
    );
    let stripped = strip_bv_wrapping(&wrapped);
    assert_eq!(stripped, diff);
}

#[test]
fn test_strip_bv_wrapping_mod() {
    // BvToInt encodes bvmul and large-width ops as: mod(expr, 2^w)
    let i = ChcVar::new("i", ChcSort::Int);
    let product = ChcExpr::Op(
        ChcOp::Mul,
        vec![Arc::new(ChcExpr::var(i.clone())), Arc::new(ChcExpr::int(3))],
    );
    let wrapped = ChcExpr::mod_op(product.clone(), ChcExpr::int(4294967296_i64)); // 2^32
    let stripped = strip_bv_wrapping(&wrapped);
    assert_eq!(stripped, product);
}

#[test]
fn test_strip_bv_wrapping_non_power_of_2_preserved() {
    // Non-power-of-2 mod should NOT be stripped
    let i = ChcVar::new("i", ChcSort::Int);
    let expr = ChcExpr::mod_op(ChcExpr::var(i), ChcExpr::int(7));
    let stripped = strip_bv_wrapping(&expr);
    assert_eq!(stripped, expr);
}

#[test]
fn test_bv_wrapped_transition_constant_delta() {
    // BvToInt-wrapped transition: i' = ite(i+1 < 256, i+1, i+1-256)
    // After stripping, should be recognized as i' = i + 1 (ConstantDelta)
    let i = ChcVar::new("i", ChcSort::Int);
    let i_prime = ChcVar::new("i'", ChcSort::Int);
    let sum = ChcExpr::add(ChcExpr::var(i), ChcExpr::int(1));
    let bound = ChcExpr::int(256);
    let wrapped_rhs = ChcExpr::ite(
        ChcExpr::lt(sum.clone(), bound.clone()),
        sum.clone(),
        ChcExpr::sub(sum, bound),
    );
    let transition = ChcExpr::eq(ChcExpr::var(i_prime), wrapped_rhs);

    let state_vars = vec!["i".to_string()];
    let result = analyze_transition(&transition, &state_vars);
    assert!(
        result.is_some(),
        "BvToInt-wrapped transition should be analyzable"
    );
    let system = result.unwrap();
    assert!(matches!(
        system.get_solution("i"),
        Some(ClosedForm::ConstantDelta { delta: 1, .. })
    ));
}

#[test]
fn test_bv_wrapped_transition_triangular() {
    // BvToInt-wrapped triangular transition:
    //   i' = ite(i+1 < 2^32, i+1, i+1-2^32)
    //   s' = ite(s+i < 2^32, s+i, s+i-2^32)
    // After stripping: i' = i+1, s' = s+i (standard accumulator)
    let i = ChcVar::new("i", ChcSort::Int);
    let i_prime = ChcVar::new("i'", ChcSort::Int);
    let s = ChcVar::new("s", ChcSort::Int);
    let s_prime = ChcVar::new("s'", ChcSort::Int);
    let bound = ChcExpr::int(4294967296_i64); // 2^32

    let i_sum = ChcExpr::add(ChcExpr::var(i.clone()), ChcExpr::int(1));
    let i_rhs = ChcExpr::ite(
        ChcExpr::lt(i_sum.clone(), bound.clone()),
        i_sum.clone(),
        ChcExpr::sub(i_sum, bound.clone()),
    );

    let s_sum = ChcExpr::add(ChcExpr::var(s), ChcExpr::var(i));
    let s_rhs = ChcExpr::ite(
        ChcExpr::lt(s_sum.clone(), bound.clone()),
        s_sum.clone(),
        ChcExpr::sub(s_sum, bound),
    );

    let transition = ChcExpr::and(
        ChcExpr::eq(ChcExpr::var(i_prime), i_rhs),
        ChcExpr::eq(ChcExpr::var(s_prime), s_rhs),
    );

    let state_vars = vec!["i".to_string(), "s".to_string()];
    let result = analyze_transition(&transition, &state_vars);
    assert!(
        result.is_some(),
        "BvToInt-wrapped triangular system should be analyzable"
    );
    let system = result.unwrap();
    assert_eq!(system.solutions.len(), 2);
    assert!(matches!(
        system.get_solution("i"),
        Some(ClosedForm::ConstantDelta { delta: 1, .. })
    ));
    assert!(matches!(
        system.get_solution("s"),
        Some(ClosedForm::Polynomial { .. })
    ));
}
