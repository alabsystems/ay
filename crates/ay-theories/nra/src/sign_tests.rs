// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Unit tests for NRA sign lemma helpers.
// Referenced from sign.rs via `#[path = "sign_tests.rs"]`.

use super::*;
use crate::monomial::Monomial;
// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::TermId;

#[test]
fn test_product_sign() {
    assert_eq!(product_sign(&[1, 1]), 1);
    assert_eq!(product_sign(&[1, -1]), -1);
    assert_eq!(product_sign(&[-1, 1]), -1);
    assert_eq!(product_sign(&[-1, -1]), 1);
    assert_eq!(product_sign(&[1, 0]), 0);
    assert_eq!(product_sign(&[0, -1]), 0);
}

#[test]
fn test_sign_conflict_returns_minimal_clause() {
    // Set up: monomial m = x * y with vars [x, y]
    let x = TermId::new(1);
    let y = TermId::new(2);
    let aux = TermId::new(3);
    let vars = vec![x, y];

    let mon = Monomial::new(vars.clone(), aux);
    let mut monomials = HashMap::default();
    monomials.insert(vars.clone(), mon);

    // x > 0 (positive), asserted by term 10
    let assert_x_pos = TermId::new(10);
    // y > 0 (positive), asserted by term 11
    let assert_y_pos = TermId::new(11);
    // m < 0 (negative) -- contradicts x>0 * y>0 = positive
    let assert_m_neg = TermId::new(12);
    // Unrelated assertion
    let assert_unrelated = TermId::new(13);

    let mut var_sign_constraints: HashMap<TermId, Vec<(SignConstraint, TermId)>> =
        HashMap::default();
    var_sign_constraints
        .entry(x)
        .or_default()
        .push((SignConstraint::Positive, assert_x_pos));
    var_sign_constraints
        .entry(y)
        .or_default()
        .push((SignConstraint::Positive, assert_y_pos));

    let mut sign_constraints: HashMap<Vec<TermId>, Vec<(SignConstraint, TermId)>> =
        HashMap::default();
    sign_constraints
        .entry(vars)
        .or_default()
        .push((SignConstraint::Negative, assert_m_neg));

    // 4 asserted literals, but only 3 are relevant
    let asserted = vec![
        (assert_x_pos, true),
        (assert_y_pos, true),
        (assert_m_neg, true),
        (assert_unrelated, true),
    ];

    let conflict = check_sign_consistency(
        &monomials,
        &sign_constraints,
        &var_sign_constraints,
        &asserted,
        false,
    );

    let conflict = conflict.expect("should detect sign conflict");
    // Must return exactly 3 literals (x_pos, y_pos, m_neg), not all 4
    assert_eq!(
        conflict.len(),
        3,
        "conflict clause should contain only the 3 relevant assertions, got {}",
        conflict.len()
    );
    let terms: Vec<TermId> = conflict.iter().map(|l| l.term).collect();
    assert!(terms.contains(&assert_x_pos));
    assert!(terms.contains(&assert_y_pos));
    assert!(terms.contains(&assert_m_neg));
    assert!(!terms.contains(&assert_unrelated));
}

#[test]
fn test_even_degree_non_negativity_conflict() {
    // Monomial x*x (vars = [x, x]) is always >= 0.
    // Constraint: x*x < 0 (Negative) -> tautological conflict.
    let x = TermId::new(1);
    let aux = TermId::new(3);
    let vars = vec![x, x]; // x*x

    let mon = Monomial::new(vars.clone(), aux);
    let mut monomials = HashMap::default();
    monomials.insert(vars.clone(), mon);

    // The assertion that says x*x < 0
    let assert_neg = TermId::new(10);

    let var_sign_constraints: HashMap<TermId, Vec<(SignConstraint, TermId)>> = HashMap::default();
    let mut sign_constraints: HashMap<Vec<TermId>, Vec<(SignConstraint, TermId)>> =
        HashMap::default();
    sign_constraints
        .entry(vars)
        .or_default()
        .push((SignConstraint::Negative, assert_neg));

    let asserted = vec![(assert_neg, true)];

    let conflict = check_sign_consistency(
        &monomials,
        &sign_constraints,
        &var_sign_constraints,
        &asserted,
        false,
    );

    let conflict = conflict.expect("should detect even-degree non-negativity conflict");
    assert_eq!(
        conflict.len(),
        1,
        "conflict should contain only the negativity assertion"
    );
    assert_eq!(conflict[0].term, assert_neg);
}

#[test]
fn test_even_degree_non_negativity_allows_non_positive() {
    // Monomial x*x (vars = [x, x]) is always >= 0.
    // Constraint: x*x <= 0 (NonPositive) is NOT a tautological conflict --
    // x*x = 0 when x = 0 is valid. Only strict Negative triggers.
    let x = TermId::new(1);
    let aux = TermId::new(3);
    let vars = vec![x, x];

    let mon = Monomial::new(vars.clone(), aux);
    let mut monomials = HashMap::default();
    monomials.insert(vars.clone(), mon);

    let assert_np = TermId::new(10);

    let var_sign_constraints: HashMap<TermId, Vec<(SignConstraint, TermId)>> = HashMap::default();
    let mut sign_constraints: HashMap<Vec<TermId>, Vec<(SignConstraint, TermId)>> =
        HashMap::default();
    sign_constraints
        .entry(vars)
        .or_default()
        .push((SignConstraint::NonPositive, assert_np));

    let asserted = vec![(assert_np, true)];

    let conflict = check_sign_consistency(
        &monomials,
        &sign_constraints,
        &var_sign_constraints,
        &asserted,
        false,
    );

    // NonPositive is compatible with zero, so no conflict
    assert!(
        conflict.is_none(),
        "NonPositive constraint on x*x should not conflict (x=0 is valid)"
    );
}

#[test]
fn test_even_degree_higher_order() {
    // Monomial x*x*y*y (vars = [x, x, y, y]) -- all even counts -> always >= 0
    let x = TermId::new(1);
    let y = TermId::new(2);
    let aux = TermId::new(5);
    let vars = vec![x, x, y, y];

    let mon = Monomial::new(vars.clone(), aux);
    let mut monomials = HashMap::default();
    monomials.insert(vars.clone(), mon);

    let assert_neg = TermId::new(10);

    let var_sign_constraints: HashMap<TermId, Vec<(SignConstraint, TermId)>> = HashMap::default();
    let mut sign_constraints: HashMap<Vec<TermId>, Vec<(SignConstraint, TermId)>> =
        HashMap::default();
    sign_constraints
        .entry(vars)
        .or_default()
        .push((SignConstraint::Negative, assert_neg));

    let asserted = vec![(assert_neg, true)];

    let conflict = check_sign_consistency(
        &monomials,
        &sign_constraints,
        &var_sign_constraints,
        &asserted,
        false,
    );

    let conflict = conflict.expect("should detect x^2*y^2 non-negativity conflict");
    assert_eq!(conflict.len(), 1);
}

#[test]
fn test_odd_degree_no_tautological_conflict() {
    // Monomial x*x*y (vars = [x, x, y]) -- y has odd count -> can be negative
    let x = TermId::new(1);
    let y = TermId::new(2);
    let aux = TermId::new(5);
    let vars = vec![x, x, y];

    let mon = Monomial::new(vars.clone(), aux);
    let mut monomials = HashMap::default();
    monomials.insert(vars.clone(), mon);

    let assert_neg = TermId::new(10);

    let var_sign_constraints: HashMap<TermId, Vec<(SignConstraint, TermId)>> = HashMap::default();
    let mut sign_constraints: HashMap<Vec<TermId>, Vec<(SignConstraint, TermId)>> =
        HashMap::default();
    sign_constraints
        .entry(vars)
        .or_default()
        .push((SignConstraint::Negative, assert_neg));

    let asserted = vec![(assert_neg, true)];

    let conflict = check_sign_consistency(
        &monomials,
        &sign_constraints,
        &var_sign_constraints,
        &asserted,
        false,
    );

    // x^2*y can be negative (when y < 0), so no tautological conflict
    assert!(
        conflict.is_none(),
        "x^2*y Negative constraint should not trigger tautological conflict"
    );
}

#[test]
fn test_sign_contradicts() {
    assert!(sign_contradicts(SignConstraint::Positive, 0));
    assert!(sign_contradicts(SignConstraint::Positive, -1));
    assert!(!sign_contradicts(SignConstraint::Positive, 1));
    assert!(sign_contradicts(SignConstraint::Negative, 0));
    assert!(sign_contradicts(SignConstraint::Negative, 1));
    assert!(!sign_contradicts(SignConstraint::Negative, -1));
    assert!(sign_contradicts(SignConstraint::Zero, 1));
    assert!(!sign_contradicts(SignConstraint::Zero, 0));
    assert!(sign_contradicts(SignConstraint::NonNegative, -1));
    assert!(!sign_contradicts(SignConstraint::NonNegative, 0));
    assert!(!sign_contradicts(SignConstraint::NonNegative, 1));
    assert!(sign_contradicts(SignConstraint::NonPositive, 1));
    assert!(!sign_contradicts(SignConstraint::NonPositive, 0));
    assert!(!sign_contradicts(SignConstraint::NonPositive, -1));
}

/// Zero constraint: only 0 satisfies it.
#[test]
fn test_sign_contradicts_zero_constraint() {
    assert!(sign_contradicts(SignConstraint::Zero, 1));
    assert!(sign_contradicts(SignConstraint::Zero, -1));
    assert!(!sign_contradicts(SignConstraint::Zero, 0));
}

/// No sign constraints means no conflict.
#[test]
fn test_no_sign_constraints_no_conflict() {
    let monomials: HashMap<Vec<TermId>, Monomial> = HashMap::default();
    let sign_constraints: HashMap<Vec<TermId>, Vec<(SignConstraint, TermId)>> = HashMap::default();
    let var_sign_constraints: HashMap<TermId, Vec<(SignConstraint, TermId)>> = HashMap::default();
    let asserted: Vec<(TermId, bool)> = Vec::new();

    let conflict = check_sign_consistency(
        &monomials,
        &sign_constraints,
        &var_sign_constraints,
        &asserted,
        false,
    );
    assert!(conflict.is_none(), "no constraints should mean no conflict");
}

/// Multiple sign constraints on the same monomial that are compatible
/// should not trigger a conflict.
#[test]
fn test_compatible_sign_constraints_no_conflict() {
    let x = TermId::new(1);
    let y = TermId::new(2);
    let aux = TermId::new(3);
    let vars = vec![x, y];

    let mon = Monomial::new(vars.clone(), aux);
    let mut monomials = HashMap::default();
    monomials.insert(vars.clone(), mon);

    // x > 0, y > 0, monomial > 0 -- all consistent
    let assert_x_pos = TermId::new(10);
    let assert_y_pos = TermId::new(11);
    let assert_m_pos = TermId::new(12);

    let mut var_sign_constraints: HashMap<TermId, Vec<(SignConstraint, TermId)>> =
        HashMap::default();
    var_sign_constraints
        .entry(x)
        .or_default()
        .push((SignConstraint::Positive, assert_x_pos));
    var_sign_constraints
        .entry(y)
        .or_default()
        .push((SignConstraint::Positive, assert_y_pos));

    let mut sign_constraints: HashMap<Vec<TermId>, Vec<(SignConstraint, TermId)>> =
        HashMap::default();
    sign_constraints
        .entry(vars)
        .or_default()
        .push((SignConstraint::Positive, assert_m_pos));

    let asserted = vec![
        (assert_x_pos, true),
        (assert_y_pos, true),
        (assert_m_pos, true),
    ];

    let conflict = check_sign_consistency(
        &monomials,
        &sign_constraints,
        &var_sign_constraints,
        &asserted,
        false,
    );

    assert!(
        conflict.is_none(),
        "positive * positive = positive is consistent, no conflict expected"
    );
}

/// Two negative factors: product should be positive.
/// Conflict: two negative factors but monomial claimed negative.
#[test]
fn test_two_negatives_product_positive_conflict() {
    let x = TermId::new(1);
    let y = TermId::new(2);
    let aux = TermId::new(3);
    let vars = vec![x, y];

    let mon = Monomial::new(vars.clone(), aux);
    let mut monomials = HashMap::default();
    monomials.insert(vars.clone(), mon);

    let assert_x_neg = TermId::new(10);
    let assert_y_neg = TermId::new(11);
    let assert_m_neg = TermId::new(12); // claims product is negative

    let mut var_sign_constraints: HashMap<TermId, Vec<(SignConstraint, TermId)>> =
        HashMap::default();
    var_sign_constraints
        .entry(x)
        .or_default()
        .push((SignConstraint::Negative, assert_x_neg));
    var_sign_constraints
        .entry(y)
        .or_default()
        .push((SignConstraint::Negative, assert_y_neg));

    let mut sign_constraints: HashMap<Vec<TermId>, Vec<(SignConstraint, TermId)>> =
        HashMap::default();
    sign_constraints
        .entry(vars)
        .or_default()
        .push((SignConstraint::Negative, assert_m_neg));

    let asserted = vec![
        (assert_x_neg, true),
        (assert_y_neg, true),
        (assert_m_neg, true),
    ];

    let conflict = check_sign_consistency(
        &monomials,
        &sign_constraints,
        &var_sign_constraints,
        &asserted,
        false,
    );

    assert!(
        conflict.is_some(),
        "negative * negative = positive, claiming negative should conflict"
    );
}
