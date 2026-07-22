// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// =========================================================================
// Tests for has_equality_recursive (#1989)
// =========================================================================

#[test]
fn test_has_equality_simple() {
    // Simple (= A B)
    let a = ChcVar::new("A", ChcSort::Int);
    let b = ChcVar::new("B", ChcSort::Int);
    let eq_ab = ChcExpr::eq(ChcExpr::var(a), ChcExpr::var(b));

    assert!(PdrSolver::has_equality_recursive(&eq_ab, "A", "B"));
    // Order shouldn't matter
    assert!(PdrSolver::has_equality_recursive(&eq_ab, "B", "A"));
    // Non-matching variable names
    assert!(!PdrSolver::has_equality_recursive(&eq_ab, "A", "C"));
    assert!(!PdrSolver::has_equality_recursive(&eq_ab, "C", "D"));
}

#[test]
fn test_has_equality_nested_in_and() {
    // (and (= A B) (> A 0))
    let a = ChcVar::new("A", ChcSort::Int);
    let b = ChcVar::new("B", ChcSort::Int);
    let eq_ab = ChcExpr::eq(ChcExpr::var(a.clone()), ChcExpr::var(b));
    let gt_a_0 = ChcExpr::gt(ChcExpr::var(a), ChcExpr::int(0));
    let and_expr = ChcExpr::and(eq_ab, gt_a_0);

    // Equality found in a conjunct
    assert!(PdrSolver::has_equality_recursive(&and_expr, "A", "B"));
}

#[test]
fn test_has_equality_in_all_or_disjuncts() {
    // (or (and (= A B) true) (and (= A B) false))
    // Equality in ALL disjuncts → should return true
    let a = ChcVar::new("A", ChcSort::Int);
    let b = ChcVar::new("B", ChcSort::Int);
    let eq_ab = ChcExpr::eq(ChcExpr::var(a), ChcExpr::var(b));

    let branch1 = ChcExpr::and(eq_ab.clone(), ChcExpr::Bool(true));
    let branch2 = ChcExpr::and(eq_ab, ChcExpr::Bool(false));
    let or_expr = ChcExpr::or(branch1, branch2);

    assert!(PdrSolver::has_equality_recursive(&or_expr, "A", "B"));
}

#[test]
fn test_has_equality_in_some_but_not_all_or_disjuncts() {
    // (or (= A B) (> A 0))
    // Equality only in SOME disjuncts → should return false
    let a = ChcVar::new("A", ChcSort::Int);
    let b = ChcVar::new("B", ChcSort::Int);
    let eq_ab = ChcExpr::eq(ChcExpr::var(a.clone()), ChcExpr::var(b));
    let gt_a_0 = ChcExpr::gt(ChcExpr::var(a), ChcExpr::int(0));
    let or_expr = ChcExpr::or(eq_ab, gt_a_0);

    // Equality NOT in all disjuncts
    assert!(!PdrSolver::has_equality_recursive(&or_expr, "A", "B"));
}

// =========================================================================
// Tests for extract_constant_equality_recursive (#1989)
// =========================================================================

#[test]
fn test_extract_constant_equality_simple() {
    // (= A 5)
    let a = ChcVar::new("A", ChcSort::Int);
    let eq_a5 = ChcExpr::eq(ChcExpr::var(a), ChcExpr::int(5));

    assert_eq!(
        PdrSolver::extract_constant_equality_recursive(&eq_a5, "A"),
        Some(5)
    );
    // Wrong variable
    assert_eq!(
        PdrSolver::extract_constant_equality_recursive(&eq_a5, "B"),
        None
    );
}

#[test]
fn test_extract_constant_equality_reversed() {
    // (= 5 A) - reversed order
    let a = ChcVar::new("A", ChcSort::Int);
    let eq_5a = ChcExpr::eq(ChcExpr::int(5), ChcExpr::var(a));

    assert_eq!(
        PdrSolver::extract_constant_equality_recursive(&eq_5a, "A"),
        Some(5)
    );
}

#[test]
fn test_extract_constant_equality_negative() {
    // (= A -7) - negative constant
    let a = ChcVar::new("A", ChcSort::Int);
    let eq_neg = ChcExpr::eq(ChcExpr::var(a), ChcExpr::int(-7));

    assert_eq!(
        PdrSolver::extract_constant_equality_recursive(&eq_neg, "A"),
        Some(-7)
    );
}

#[test]
fn test_extract_constant_equality_nested_in_and() {
    // (and (= A 5) (> B 0))
    let a = ChcVar::new("A", ChcSort::Int);
    let b = ChcVar::new("B", ChcSort::Int);
    let eq_a5 = ChcExpr::eq(ChcExpr::var(a), ChcExpr::int(5));
    let gt_b0 = ChcExpr::gt(ChcExpr::var(b), ChcExpr::int(0));
    let and_expr = ChcExpr::and(eq_a5, gt_b0);

    assert_eq!(
        PdrSolver::extract_constant_equality_recursive(&and_expr, "A"),
        Some(5)
    );
    // B has no constant equality
    assert_eq!(
        PdrSolver::extract_constant_equality_recursive(&and_expr, "B"),
        None
    );
}

// =========================================================================
// Tests for extract_upper_bound_recursive_impl (#1989)
// =========================================================================

#[test]
fn test_extract_upper_bound_le_pattern() {
    // (<= A 5)
    let a = ChcVar::new("A", ChcSort::Int);
    let le_a5 = ChcExpr::le(ChcExpr::var(a), ChcExpr::int(5));

    assert_eq!(
        PdrSolver::extract_upper_bound_recursive_impl(&le_a5, "A"),
        Some(5)
    );
}

#[test]
fn test_extract_upper_bound_lt_pattern() {
    // (< A 5) means A <= 4
    let a = ChcVar::new("A", ChcSort::Int);
    let lt_a5 = ChcExpr::lt(ChcExpr::var(a), ChcExpr::int(5));

    assert_eq!(
        PdrSolver::extract_upper_bound_recursive_impl(&lt_a5, "A"),
        Some(4)
    );
}

#[test]
fn test_extract_upper_bound_not_ge_pattern() {
    // (not (>= A 5)) means A < 5, so upper bound is 4
    let a = ChcVar::new("A", ChcSort::Int);
    let ge_a5 = ChcExpr::ge(ChcExpr::var(a), ChcExpr::int(5));
    let not_ge = ChcExpr::not(ge_a5);

    assert_eq!(
        PdrSolver::extract_upper_bound_recursive_impl(&not_ge, "A"),
        Some(4)
    );
}

#[test]
fn test_extract_upper_bound_not_gt_pattern() {
    // (not (> A 5)) means A <= 5
    let a = ChcVar::new("A", ChcSort::Int);
    let gt_a5 = ChcExpr::gt(ChcExpr::var(a), ChcExpr::int(5));
    let not_gt = ChcExpr::not(gt_a5);

    assert_eq!(
        PdrSolver::extract_upper_bound_recursive_impl(&not_gt, "A"),
        Some(5)
    );
}

#[test]
fn test_extract_upper_bound_not_le_reversed_pattern() {
    // (not (<= 5 A)) means A < 5, so upper bound is 4
    // This is the s_mutants_16_m pattern from #1684
    let a = ChcVar::new("A", ChcSort::Int);
    let le_5a = ChcExpr::le(ChcExpr::int(5), ChcExpr::var(a));
    let not_le = ChcExpr::not(le_5a);

    assert_eq!(
        PdrSolver::extract_upper_bound_recursive_impl(&not_le, "A"),
        Some(4)
    );
}

#[test]
fn test_extract_upper_bound_not_lt_reversed_pattern() {
    // (not (< 5 A)) means A <= 5, so upper bound is 5
    let a = ChcVar::new("A", ChcSort::Int);
    let lt_5a = ChcExpr::lt(ChcExpr::int(5), ChcExpr::var(a));
    let not_lt = ChcExpr::not(lt_5a);

    assert_eq!(
        PdrSolver::extract_upper_bound_recursive_impl(&not_lt, "A"),
        Some(5)
    );
}

#[test]
fn test_extract_upper_bound_nested_in_and() {
    // (and (<= A 5) (> B 0))
    let a = ChcVar::new("A", ChcSort::Int);
    let b = ChcVar::new("B", ChcSort::Int);
    let le_a5 = ChcExpr::le(ChcExpr::var(a), ChcExpr::int(5));
    let gt_b0 = ChcExpr::gt(ChcExpr::var(b), ChcExpr::int(0));
    let and_expr = ChcExpr::and(le_a5, gt_b0);

    assert_eq!(
        PdrSolver::extract_upper_bound_recursive_impl(&and_expr, "A"),
        Some(5)
    );
    // B has no upper bound in this formula
    assert_eq!(
        PdrSolver::extract_upper_bound_recursive_impl(&and_expr, "B"),
        None
    );
}

// =========================================================================
// Tests for OR handling in extraction helpers (#1987, #1988)
// =========================================================================

#[test]
fn test_extract_constant_equality_or_same_value() {
    // (or (= A 5) (= A 5)) - same constant in all disjuncts
    let a = ChcVar::new("A", ChcSort::Int);
    let eq1 = ChcExpr::eq(ChcExpr::var(a.clone()), ChcExpr::int(5));
    let eq2 = ChcExpr::eq(ChcExpr::var(a), ChcExpr::int(5));
    let or_expr = ChcExpr::or(eq1, eq2);

    assert_eq!(
        PdrSolver::extract_constant_equality_recursive(&or_expr, "A"),
        Some(5)
    );
}

#[test]
fn test_extract_constant_equality_or_different_values() {
    // (or (= A 5) (= A 7)) - different constants
    let a = ChcVar::new("A", ChcSort::Int);
    let eq1 = ChcExpr::eq(ChcExpr::var(a.clone()), ChcExpr::int(5));
    let eq2 = ChcExpr::eq(ChcExpr::var(a), ChcExpr::int(7));
    let or_expr = ChcExpr::or(eq1, eq2);

    // Should return None because constants don't match
    assert_eq!(
        PdrSolver::extract_constant_equality_recursive(&or_expr, "A"),
        None
    );
}

#[test]
fn test_extract_constant_equality_or_missing_in_one() {
    // (or (= A 5) (> A 0)) - second disjunct has no equality
    let a = ChcVar::new("A", ChcSort::Int);
    let eq = ChcExpr::eq(ChcExpr::var(a.clone()), ChcExpr::int(5));
    let gt = ChcExpr::gt(ChcExpr::var(a), ChcExpr::int(0));
    let or_expr = ChcExpr::or(eq, gt);

    // Should return None because not all disjuncts have equality
    assert_eq!(
        PdrSolver::extract_constant_equality_recursive(&or_expr, "A"),
        None
    );
}

#[test]
fn test_extract_upper_bound_or_all_have_bounds() {
    // (or (<= A 5) (<= A 3)) - all disjuncts have upper bounds
    let a = ChcVar::new("A", ChcSort::Int);
    let le5 = ChcExpr::le(ChcExpr::var(a.clone()), ChcExpr::int(5));
    let le3 = ChcExpr::le(ChcExpr::var(a), ChcExpr::int(3));
    let or_expr = ChcExpr::or(le5, le3);

    // Should return min(5, 3) = 3
    assert_eq!(
        PdrSolver::extract_upper_bound_recursive_impl(&or_expr, "A"),
        Some(3)
    );
}

#[test]
fn test_extract_upper_bound_or_missing_in_one() {
    // (or (<= A 5) (> A 0)) - second disjunct has no upper bound
    let a = ChcVar::new("A", ChcSort::Int);
    let le = ChcExpr::le(ChcExpr::var(a.clone()), ChcExpr::int(5));
    let gt = ChcExpr::gt(ChcExpr::var(a), ChcExpr::int(0));
    let or_expr = ChcExpr::or(le, gt);

    // Should return None because not all disjuncts have upper bounds
    assert_eq!(
        PdrSolver::extract_upper_bound_recursive_impl(&or_expr, "A"),
        None
    );
}

#[test]
fn test_extract_upper_bound_or_three_disjuncts() {
    // (or (<= A 5) (<= A 3) (<= A 7)) - three disjuncts
    let a = ChcVar::new("A", ChcSort::Int);
    let le5 = ChcExpr::le(ChcExpr::var(a.clone()), ChcExpr::int(5));
    let le3 = ChcExpr::le(ChcExpr::var(a.clone()), ChcExpr::int(3));
    let le7 = ChcExpr::le(ChcExpr::var(a), ChcExpr::int(7));
    let or_expr = ChcExpr::or_vec(vec![le5, le3, le7]);

    // Should return min(5, 3, 7) = 3 (tightest common bound)
    assert_eq!(
        PdrSolver::extract_upper_bound_recursive_impl(&or_expr, "A"),
        Some(3)
    );
}

#[test]
fn test_extract_constant_equality_or_three_disjuncts_same() {
    // (or (= A 5) (= A 5) (= A 5)) - three disjuncts, same value
    let a = ChcVar::new("A", ChcSort::Int);
    let eq1 = ChcExpr::eq(ChcExpr::var(a.clone()), ChcExpr::int(5));
    let eq2 = ChcExpr::eq(ChcExpr::var(a.clone()), ChcExpr::int(5));
    let eq3 = ChcExpr::eq(ChcExpr::var(a), ChcExpr::int(5));
    let or_expr = ChcExpr::or_vec(vec![eq1, eq2, eq3]);

    assert_eq!(
        PdrSolver::extract_constant_equality_recursive(&or_expr, "A"),
        Some(5)
    );
}

#[test]
fn test_extract_upper_bound_nested_or_in_and() {
    // (and (or (<= A 5) (<= A 3)) (<= B 10))
    // The OR has a valid upper bound (min=3), so it should be found
    let a = ChcVar::new("A", ChcSort::Int);
    let b = ChcVar::new("B", ChcSort::Int);
    let le5 = ChcExpr::le(ChcExpr::var(a.clone()), ChcExpr::int(5));
    let le3 = ChcExpr::le(ChcExpr::var(a), ChcExpr::int(3));
    let or_a = ChcExpr::or(le5, le3);
    let le_b = ChcExpr::le(ChcExpr::var(b), ChcExpr::int(10));
    let and_expr = ChcExpr::and(or_a, le_b);

    assert_eq!(
        PdrSolver::extract_upper_bound_recursive_impl(&and_expr, "A"),
        Some(3)
    );
    assert_eq!(
        PdrSolver::extract_upper_bound_recursive_impl(&and_expr, "B"),
        Some(10)
    );
}
