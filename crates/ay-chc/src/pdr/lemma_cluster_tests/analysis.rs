// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// ============================================================================
// Mono-var literal detection tests (conjecture mechanism, #698)
// ============================================================================

/// Test find_mono_var_literal with a simple pattern: (>= x __gg_k0) ∧ (= y 5)
/// Should return (>= x __gg_k0) as the mono-var literal.
#[test]
fn test_find_mono_var_literal_simple() {
    let pred = PredicateId::new(0);
    let pv = ChcVar::new("__gg_k0", ChcSort::Int);
    // Pattern: (>= x __gg_k0) ∧ (= y 5)
    // The (= y 5) is a ground literal (no pattern var)
    let pattern = ChcExpr::and(
        ChcExpr::ge(make_var("x"), ChcExpr::var(pv.clone())),
        ChcExpr::eq(make_var("y"), ChcExpr::Int(5)),
    );
    let cluster = LemmaCluster::new(pred, pattern, vec![pv]);

    let mono_lit = cluster.find_mono_var_literal();
    assert!(mono_lit.is_some(), "should find mono-var literal");

    // The mono-var literal should be the (>= x __gg_k0) part
    let found = mono_lit.unwrap();
    assert!(
        found.to_string().contains("__gg_k0"),
        "mono-var literal should contain pattern var"
    );
}

/// Test find_mono_var_literal with equality pattern.
#[test]
fn test_find_mono_var_literal_equality() {
    let pred = PredicateId::new(0);
    let pv = ChcVar::new("__gg_k0", ChcSort::Int);
    // Pattern: (= x __gg_k0) - single literal with equality
    let pattern = ChcExpr::eq(make_var("x"), ChcExpr::var(pv.clone()));
    let cluster = LemmaCluster::new(pred, pattern, vec![pv]);

    let mono_lit = cluster.find_mono_var_literal();
    assert!(mono_lit.is_some(), "equality is a valid mono-var literal");
}

/// Test find_mono_var_literal returns None when multiple pattern vars exist.
#[test]
fn test_find_mono_var_literal_rejects_multi_var() {
    let pred = PredicateId::new(0);
    let pv0 = ChcVar::new("__gg_k0", ChcSort::Int);
    let pv1 = ChcVar::new("__gg_k1", ChcSort::Int);
    // Pattern: (>= x __gg_k0) ∧ (<= y __gg_k1) - 2 pattern vars
    let pattern = ChcExpr::and(
        ChcExpr::ge(make_var("x"), ChcExpr::var(pv0.clone())),
        ChcExpr::le(make_var("y"), ChcExpr::var(pv1.clone())),
    );
    let cluster = LemmaCluster::new(pred, pattern, vec![pv0, pv1]);

    let mono_lit = cluster.find_mono_var_literal();
    assert!(
        mono_lit.is_none(),
        "should reject patterns with multiple pattern vars"
    );
}

/// Test find_mono_var_literal returns None when multiple mono-var literals exist.
#[test]
fn test_find_mono_var_literal_rejects_multiple_arith_lits() {
    let pred = PredicateId::new(0);
    let pv = ChcVar::new("__gg_k0", ChcSort::Int);
    // Pattern: (>= x __gg_k0) ∧ (<= x __gg_k0) - same pattern var in multiple arith literals
    // This is actually syntactically different from the Z3 check since we have 1 pattern var
    // but it appears in two different arithmetic literals.
    let pattern = ChcExpr::and(
        ChcExpr::ge(make_var("x"), ChcExpr::var(pv.clone())),
        ChcExpr::le(make_var("x"), ChcExpr::var(pv.clone())),
    );
    let cluster = LemmaCluster::new(pred, pattern, vec![pv]);

    let mono_lit = cluster.find_mono_var_literal();
    assert!(
        mono_lit.is_none(),
        "should reject patterns with multiple arithmetic literals"
    );
}

/// Test find_mono_var_literal returns None for purely ground pattern (no pattern vars).
#[test]
fn test_find_mono_var_literal_rejects_ground() {
    let pred = PredicateId::new(0);
    // Pattern with no pattern variables
    let pattern = ChcExpr::ge(make_var("x"), ChcExpr::Int(5));
    let cluster = LemmaCluster::new(pred, pattern, vec![]);

    let mono_lit = cluster.find_mono_var_literal();
    assert!(
        mono_lit.is_none(),
        "should reject patterns with no pattern vars"
    );
}

/// Test is_mono_var_lit helper with various literal types.
#[test]
fn test_is_mono_var_lit_helper() {
    let pv_name = "__gg_k0";
    let pv = ChcVar::new(pv_name, ChcSort::Int);

    // Valid mono-var literals
    let ge_lit = ChcExpr::ge(make_var("x"), ChcExpr::var(pv.clone()));
    assert!(is_mono_var_lit(&ge_lit, pv_name), ">= is valid");

    let le_lit = ChcExpr::le(make_var("x"), ChcExpr::var(pv.clone()));
    assert!(is_mono_var_lit(&le_lit, pv_name), "<= is valid");

    let gt_lit = make_gt(make_var("x"), ChcExpr::var(pv.clone()));
    assert!(is_mono_var_lit(&gt_lit, pv_name), "> is valid");

    let lt_lit = ChcExpr::lt(make_var("x"), ChcExpr::var(pv.clone()));
    assert!(is_mono_var_lit(&lt_lit, pv_name), "< is valid");

    let eq_lit = ChcExpr::eq(make_var("x"), ChcExpr::var(pv.clone()));
    assert!(is_mono_var_lit(&eq_lit, pv_name), "= is valid");

    // Negated literals should also be valid (!(x > k) is equivalent to (x <= k))
    let not_gt_lit = ChcExpr::not(make_gt(make_var("x"), ChcExpr::var(pv.clone())));
    assert!(is_mono_var_lit(&not_gt_lit, pv_name), "!(>) is valid");

    // Invalid: pattern var not present
    let no_pv_lit = ChcExpr::ge(make_var("x"), ChcExpr::Int(5));
    assert!(
        !is_mono_var_lit(&no_pv_lit, pv_name),
        "no pattern var is invalid"
    );

    // Invalid: non-arithmetic operation
    let and_lit = ChcExpr::and(ChcExpr::Bool(true), ChcExpr::var(pv));
    assert!(
        !is_mono_var_lit(&and_lit, pv_name),
        "AND is not arithmetic comparison"
    );
}

/// Test has_nonlinear_var_mul helper.
#[test]
fn test_has_nonlinear_var_mul() {
    let pv_name = "__gg_k0";
    let pv = ChcVar::new(pv_name, ChcSort::Int);

    // Linear: k * constant
    let linear = ChcExpr::mul(ChcExpr::var(pv.clone()), ChcExpr::Int(2));
    assert!(
        !has_nonlinear_var_mul(&linear, pv_name),
        "k * const is linear"
    );

    // Linear: single var in expression
    let single_var = ChcExpr::ge(
        make_var("x"),
        ChcExpr::add(ChcExpr::var(pv.clone()), ChcExpr::Int(1)),
    );
    assert!(
        !has_nonlinear_var_mul(&single_var, pv_name),
        "x >= k + 1 is linear"
    );

    // Nonlinear: k * k
    let k_squared = ChcExpr::mul(ChcExpr::var(pv.clone()), ChcExpr::var(pv.clone()));
    assert!(
        has_nonlinear_var_mul(&k_squared, pv_name),
        "k * k is nonlinear"
    );

    // Nonlinear: k * (k + 1)
    let k_times_expr = ChcExpr::mul(
        ChcExpr::var(pv.clone()),
        ChcExpr::add(ChcExpr::var(pv), ChcExpr::Int(1)),
    );
    assert!(
        has_nonlinear_var_mul(&k_times_expr, pv_name),
        "k * (k + 1) is nonlinear"
    );
}

// ============================================================================
// filter_out_lit tests (conjecture mechanism, #698)
// ============================================================================

/// Test filter_out_lit removes matching literal from conjuncts.
#[test]
fn test_filter_out_lit_removes_matching() {
    let pv = ChcVar::new("__gg_k0", ChcSort::Int);

    // Pattern: (>= x __gg_k0)
    let mono_var_pattern = ChcExpr::ge(make_var("x"), ChcExpr::var(pv.clone()));

    // Conjuncts: (>= x 5), (= y 0)
    let conjuncts = vec![
        ChcExpr::ge(make_var("x"), ChcExpr::Int(5)),
        ChcExpr::eq(make_var("y"), ChcExpr::Int(0)),
    ];

    let result = filter_out_lit(&conjuncts, &mono_var_pattern, &pv);
    assert!(result.is_some(), "should find and remove matching literal");

    let remaining = result.unwrap();
    assert_eq!(remaining.len(), 1, "should have 1 remaining literal");
    assert!(
        remaining[0].to_string().contains("y"),
        "remaining should be the (= y 0) literal"
    );
}

/// Test filter_out_lit returns None when no match.
#[test]
fn test_filter_out_lit_no_match() {
    let pv = ChcVar::new("__gg_k0", ChcSort::Int);

    // Pattern: (>= x __gg_k0)
    let mono_var_pattern = ChcExpr::ge(make_var("x"), ChcExpr::var(pv.clone()));

    // Conjuncts with no matching literal (y instead of x)
    let conjuncts = vec![
        ChcExpr::ge(make_var("y"), ChcExpr::Int(5)),
        ChcExpr::eq(make_var("z"), ChcExpr::Int(0)),
    ];

    let result = filter_out_lit(&conjuncts, &mono_var_pattern, &pv);
    assert!(
        result.is_none(),
        "should return None when no literal matches"
    );
}

/// Test filter_out_lit handles semantic equivalence (!(x > k) matches (x <= k)).
#[test]
fn test_filter_out_lit_semantic_equivalence() {
    let pv = ChcVar::new("__gg_k0", ChcSort::Int);

    // Pattern: (le x __gg_k0) which is semantically equivalent to !(x > k)
    let mono_var_pattern = ChcExpr::le(make_var("x"), ChcExpr::var(pv.clone()));

    // Conjuncts: !(x > 5) (semantically equivalent to x <= 5), (= y 0)
    let conjuncts = vec![
        ChcExpr::not(make_gt(make_var("x"), ChcExpr::Int(5))),
        ChcExpr::eq(make_var("y"), ChcExpr::Int(0)),
    ];

    let result = filter_out_lit(&conjuncts, &mono_var_pattern, &pv);
    assert!(
        result.is_some(),
        "should match semantically equivalent literal"
    );

    let remaining = result.unwrap();
    assert_eq!(remaining.len(), 1, "should have 1 remaining literal");
}

/// Test filter_out_lit removes multiple matching literals.
#[test]
fn test_filter_out_lit_multiple_matches() {
    let pv = ChcVar::new("__gg_k0", ChcSort::Int);

    // Pattern: (= x __gg_k0)
    let mono_var_pattern = ChcExpr::eq(make_var("x"), ChcExpr::var(pv.clone()));

    // Conjuncts: (= x 5), (= x 7), (= y 0)
    // Both (= x 5) and (= x 7) match the pattern (different values for k)
    let conjuncts = vec![
        ChcExpr::eq(make_var("x"), ChcExpr::Int(5)),
        ChcExpr::eq(make_var("x"), ChcExpr::Int(7)),
        ChcExpr::eq(make_var("y"), ChcExpr::Int(0)),
    ];

    let result = filter_out_lit(&conjuncts, &mono_var_pattern, &pv);
    assert!(result.is_some(), "should match multiple literals");

    let remaining = result.unwrap();
    assert_eq!(
        remaining.len(),
        1,
        "should have 1 remaining literal (only y)"
    );
}

/// Test filter_out_lit produces empty result when all match.
#[test]
fn test_filter_out_lit_all_match() {
    let pv = ChcVar::new("__gg_k0", ChcSort::Int);

    // Pattern: (>= x __gg_k0)
    let mono_var_pattern = ChcExpr::ge(make_var("x"), ChcExpr::var(pv.clone()));

    // Single conjunct that matches
    let conjuncts = vec![ChcExpr::ge(make_var("x"), ChcExpr::Int(5))];

    let result = filter_out_lit(&conjuncts, &mono_var_pattern, &pv);
    assert!(result.is_some(), "should find match");

    let remaining = result.unwrap();
    assert!(
        remaining.is_empty(),
        "should have empty remaining when all literals match"
    );
}

/// Regression: conjecture drop retries `=` when `<=`/`>=` fails to match.
#[test]
fn test_filter_out_lit_with_eq_retry_drops_eq_instance_for_ge_pattern() {
    let pv = ChcVar::new("__gg_k0", ChcSort::Int);

    // Pattern: (>= x __gg_k0)
    let mono_var_pattern = ChcExpr::ge(make_var("x"), ChcExpr::var(pv.clone()));

    // Conjuncts: (= x 5), (= y 0)
    let conjuncts = vec![
        ChcExpr::eq(make_var("x"), ChcExpr::Int(5)),
        ChcExpr::eq(make_var("y"), ChcExpr::Int(0)),
    ];

    let result = filter_out_lit_with_eq_retry(&conjuncts, &mono_var_pattern, &pv);
    assert!(result.is_some(), "should drop equality instance via retry");

    let remaining = result.unwrap();
    assert_eq!(remaining.len(), 1, "should have 1 remaining literal");
    assert_eq!(remaining[0], ChcExpr::eq(make_var("y"), ChcExpr::Int(0)));
}
