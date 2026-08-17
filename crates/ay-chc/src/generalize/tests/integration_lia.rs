// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// =========================================================================
// DropLiteralGeneralizer Integration Tests
// =========================================================================

#[test]
fn test_drop_literal_removes_redundant_conjunct() {
    let g = DropLiteralGeneralizer::new();
    let mut ts = MockTransitionSystem::new();

    // Lemma: x = 5 AND y = 3
    let x = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
    let y = ChcExpr::var(ChcVar::new("y", ChcSort::Int));
    let lemma = ChcExpr::and(
        ChcExpr::eq(x.clone(), ChcExpr::int(5)),
        ChcExpr::eq(y, ChcExpr::int(3)),
    );

    // Mark "x = 5" alone as inductive (dropping y = 3 is valid)
    ts.mark_inductive(&format!("{:?}", ChcExpr::eq(x.clone(), ChcExpr::int(5))));

    let result = g.generalize(&lemma, 1, &mut ts);

    // Should have reduced to just x = 5
    assert_eq!(result, ChcExpr::eq(x, ChcExpr::int(5)));
}

#[test]
fn test_drop_literal_preserves_when_all_required() {
    let g = DropLiteralGeneralizer::new();
    let mut ts = MockTransitionSystem::new();

    // Lemma: x >= 0 AND x <= 10
    let x = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
    let lemma = ChcExpr::and(
        ChcExpr::ge(x.clone(), ChcExpr::int(0)),
        ChcExpr::le(x, ChcExpr::int(10)),
    );

    // Neither conjunct alone is inductive - only the full formula
    ts.mark_inductive(&format!("{lemma:?}"));

    let result = g.generalize(&lemma, 1, &mut ts);

    // Should preserve original (nothing can be dropped)
    assert_eq!(result, lemma);
}

#[test]
fn test_drop_literal_failure_limit_is_consecutive() {
    let g = DropLiteralGeneralizer::with_failure_limit(2);
    let mut ts = MockTransitionSystem::new();

    let a = ChcExpr::var(ChcVar::new("a", ChcSort::Bool));
    let b = ChcExpr::var(ChcVar::new("b", ChcSort::Bool));
    let c = ChcExpr::var(ChcVar::new("c", ChcSort::Bool));
    let d = ChcExpr::var(ChcVar::new("d", ChcSort::Bool));
    let lemma = ChcExpr::and_all([a.clone(), b, c.clone(), d.clone()]);

    // Dropping `b` succeeds, resetting failures back to 0.
    let drop_b_candidate = ChcExpr::and_all([a.clone(), c.clone(), d]);
    ts.mark_inductive(&format!("{drop_b_candidate:?}"));

    // Without the reset, we'd hit the failure limit before trying `d`.
    let drop_d_candidate = ChcExpr::and_all([a.clone(), c.clone()]);
    ts.mark_inductive(&format!("{drop_d_candidate:?}"));

    let result = g.generalize(&lemma, 1, &mut ts);
    let expected = ChcExpr::and_all([a, c]);
    assert_eq!(result, expected);
}

// =========================================================================
// UnsatCoreGeneralizer Integration Tests
// =========================================================================

#[test]
fn test_unsat_core_generalizer_reduces_to_core() {
    let g = UnsatCoreGeneralizer::new();
    let mut ts = MockTransitionSystem::new();

    // Lemma: a AND b AND c
    let a = ChcExpr::var(ChcVar::new("a", ChcSort::Bool));
    let b = ChcExpr::var(ChcVar::new("b", ChcSort::Bool));
    let c = ChcExpr::var(ChcVar::new("c", ChcSort::Bool));
    let lemma = ChcExpr::and(ChcExpr::and(a, b), c);

    // Full lemma is inductive (will return core of first conjuncts)
    ts.mark_inductive(&format!("{lemma:?}"));

    let result = g.generalize(&lemma, 1, &mut ts);

    // UnsatCoreGeneralizer should reduce based on the core returned
    // Since mock returns first half, expect reduction
    assert_ne!(format!("{result:?}"), format!("{:?}", lemma));
}

// =========================================================================
// LiteralWeakeningGeneralizer Integration Tests
// =========================================================================

#[test]
fn test_literal_weakening_weakens_equality() {
    let g = LiteralWeakeningGeneralizer::new();
    let mut ts = MockTransitionSystem::new();

    // Lemma: x = 5
    let x = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
    let lemma = ChcExpr::eq(x.clone(), ChcExpr::int(5));

    // Mark x <= 5 as inductive (weakening from equality is valid)
    ts.mark_inductive(&format!("{:?}", ChcExpr::le(x.clone(), ChcExpr::int(5))));

    let result = g.generalize(&lemma, 1, &mut ts);

    // Should weaken to x <= 5
    assert_eq!(result, ChcExpr::le(x, ChcExpr::int(5)));
}

#[test]
fn test_literal_weakening_preserves_non_arithmetic() {
    let g = LiteralWeakeningGeneralizer::new();
    let mut ts = MockTransitionSystem::new();

    // Lemma: b = true (boolean, not arithmetic)
    let b = ChcExpr::var(ChcVar::new("b", ChcSort::Bool));
    let lemma = b;

    let result = g.generalize(&lemma, 1, &mut ts);

    // Should preserve (no arithmetic weakening for booleans)
    assert_eq!(result, lemma);
}

// =========================================================================
// BoundExpansionGeneralizer Integration Tests
// =========================================================================

#[test]
fn test_bound_expansion_expands_upper_bound() {
    let g = BoundExpansionGeneralizer::new();
    let mut ts = MockTransitionSystem::new();

    // Lemma: x <= 5
    let x = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
    let lemma = ChcExpr::le(x.clone(), ChcExpr::int(5));

    // Mark x <= 6 as inductive (expanding bound is valid)
    ts.mark_inductive(&format!("{:?}", ChcExpr::le(x.clone(), ChcExpr::int(6))));

    let result = g.generalize(&lemma, 1, &mut ts);

    // Should expand to x <= 6
    assert_eq!(result, ChcExpr::le(x, ChcExpr::int(6)));
}

#[test]
fn test_bound_expansion_expands_lower_bound() {
    let g = BoundExpansionGeneralizer::new();
    let mut ts = MockTransitionSystem::new();

    // Lemma: x >= 5
    let x = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
    let lemma = ChcExpr::ge(x.clone(), ChcExpr::int(5));

    // Mark x >= 4 as inductive (relaxing lower bound is valid)
    ts.mark_inductive(&format!("{:?}", ChcExpr::ge(x.clone(), ChcExpr::int(4))));

    let result = g.generalize(&lemma, 1, &mut ts);

    // Should relax to x >= 4
    assert_eq!(result, ChcExpr::ge(x, ChcExpr::int(4)));
}

// =========================================================================
// InitBoundWeakeningGeneralizer Integration Tests
// =========================================================================

#[test]
fn test_init_bound_weakening_uses_init_bounds() {
    let g = InitBoundWeakeningGeneralizer::new();

    // Set up init bounds: x is initially in [5, 10]
    let mut bounds = HashMap::default();
    bounds.insert("x".to_string(), InitBounds::range(5, 10));
    let mut ts = MockTransitionSystem::new().with_init_bounds(bounds);

    // Lemma: x = -3 (value BELOW init_min of 5)
    // InitBoundWeakening only weakens when val < init_min
    let x = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
    let lemma = ChcExpr::eq(x.clone(), ChcExpr::int(-3));

    // Mark x < 5 as inductive (weakening from x = -3 to x < init_min)
    ts.mark_inductive(&format!("{:?}", ChcExpr::lt(x.clone(), ChcExpr::int(5))));

    let result = g.generalize(&lemma, 1, &mut ts);

    // Should weaken to x < 5 (x < init_min)
    assert_eq!(result, ChcExpr::lt(x, ChcExpr::int(5)));
}

#[test]
fn test_init_bound_weakening_preserves_in_bounds() {
    let g = InitBoundWeakeningGeneralizer::new();

    // Set up init bounds: x is initially in [0, 10]
    let mut bounds = HashMap::default();
    bounds.insert("x".to_string(), InitBounds::range(0, 10));
    let mut ts = MockTransitionSystem::new().with_init_bounds(bounds);

    // Lemma: x = 5 (value WITHIN bounds, should not be weakened)
    let x = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
    let lemma = ChcExpr::eq(x, ChcExpr::int(5));

    let result = g.generalize(&lemma, 1, &mut ts);

    // Should preserve original (5 is within [0, 10])
    assert_eq!(result, lemma);
}

// =========================================================================
// SingleVariableRangeGeneralizer Integration Tests
// =========================================================================

#[test]
fn test_single_variable_range_discovers_range() {
    let g = SingleVariableRangeGeneralizer::new();

    // Set up init bounds: x starts at [10, 100]
    let mut bounds = HashMap::default();
    bounds.insert("x".to_string(), InitBounds::range(10, 100));
    let mut ts = MockTransitionSystem::new().with_init_bounds(bounds);

    // Lemma: x = -5 AND y = 3 (x is below init_min of 10)
    let x = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
    let y = ChcExpr::var(ChcVar::new("y", ChcSort::Int));
    let lemma = ChcExpr::and(
        ChcExpr::eq(x.clone(), ChcExpr::int(-5)),
        ChcExpr::eq(y, ChcExpr::int(3)),
    );

    // Mark x < 10 as inductive (range invariant replacing entire lemma)
    ts.mark_inductive(&format!("{:?}", ChcExpr::lt(x.clone(), ChcExpr::int(10))));

    let result = g.generalize(&lemma, 1, &mut ts);

    // Should replace with x < 10 (strong range invariant)
    assert_eq!(result, ChcExpr::lt(x, ChcExpr::int(10)));
}

#[test]
fn test_single_variable_range_no_bounds_returns_unchanged() {
    let g = SingleVariableRangeGeneralizer::new();
    let mut ts = MockTransitionSystem::new();
    // No init_bounds set

    let x = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
    let lemma = ChcExpr::eq(x, ChcExpr::int(5));

    let result = g.generalize(&lemma, 1, &mut ts);

    // Should preserve (no init bounds available)
    assert_eq!(result, lemma);
}

// =========================================================================
// FarkasGeneralizer Integration Tests
// =========================================================================

#[test]
fn test_farkas_generalizer_with_combinable_constraints() {
    let g = FarkasGeneralizer::new();
    let mut ts = MockTransitionSystem::new();

    // Lemma: x <= 5 AND x >= 3 (can be combined by equal weights)
    let x = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
    let lemma = ChcExpr::and(
        ChcExpr::le(x.clone(), ChcExpr::int(5)),
        ChcExpr::ge(x, ChcExpr::int(3)),
    );

    // The Farkas combination would produce a combined constraint
    // Mark any such combination as inductive
    ts.mark_inductive(&format!(
        "{:?}",
        ChcExpr::le(ChcExpr::int(0), ChcExpr::int(0))
    ));

    let _result = g.generalize(&lemma, 1, &mut ts);

    // FarkasGeneralizer should attempt combination if farkas_combine succeeds
    // The key test is that it doesn't crash and produces valid output
}

#[test]
fn test_farkas_generalizer_needs_multiple_constraints() {
    let g = FarkasGeneralizer::new();
    let mut ts = MockTransitionSystem::new();

    // Single constraint - Farkas needs at least 2
    let x = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
    let lemma = ChcExpr::ge(x, ChcExpr::int(0));

    let result = g.generalize(&lemma, 1, &mut ts);

    // Should return unchanged (need >= 2 constraints)
    assert_eq!(result, lemma);
}

#[test]
fn test_denominator_simplification_generalizer_reduces_coefficients() {
    let g = DenominatorSimplificationGeneralizer::new();
    let mut ts = MockTransitionSystem::new();

    let x = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
    let lemma = ChcExpr::le(ChcExpr::mul(ChcExpr::int(2), x.clone()), ChcExpr::int(4));
    let expected = ChcExpr::le(x, ChcExpr::int(2));
    ts.mark_inductive(&format!("{expected:?}"));

    let result = g.generalize(&lemma, 1, &mut ts);
    assert_eq!(result, expected);
}

#[test]
fn test_denominator_simplification_generalizer_preserves_original_when_not_inductive() {
    let g = DenominatorSimplificationGeneralizer::new();
    let mut ts = MockTransitionSystem::new();

    let x = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
    let lemma = ChcExpr::le(ChcExpr::mul(ChcExpr::int(2), x), ChcExpr::int(4));

    let result = g.generalize(&lemma, 1, &mut ts);
    assert_eq!(result, lemma);
}

// =========================================================================
// ConstantSumGeneralizer Integration Tests
// =========================================================================

#[test]
fn test_constant_sum_discovers_sum_invariant() {
    let g = ConstantSumGeneralizer::new();

    // Set up EXACT init bounds (required for ConstantSum)
    // init: x = 0, y = 100 => init_sum = 100
    let mut bounds = HashMap::default();
    bounds.insert("x".to_string(), InitBounds::exact(0));
    bounds.insert("y".to_string(), InitBounds::exact(100));
    let mut ts = MockTransitionSystem::new().with_init_bounds(bounds);

    // Lemma: x = 50 AND y = 60 (state_sum = 110, DIFFERENT from init_sum = 100)
    // This is what triggers the generalizer
    let x = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
    let y = ChcExpr::var(ChcVar::new("y", ChcSort::Int));
    let lemma = ChcExpr::and(
        ChcExpr::eq(x.clone(), ChcExpr::int(50)),
        ChcExpr::eq(y.clone(), ChcExpr::int(60)),
    );

    // Mark (x + y) != 100 as inductive (sum invariant violation blocking)
    let sum_ne = ChcExpr::ne(
        ChcExpr::add(x, y),
        ChcExpr::int(100), // init_sum
    );
    ts.mark_inductive(&format!("{sum_ne:?}"));

    let result = g.generalize(&lemma, 1, &mut ts);

    // Should generalize to (x + y) != 100
    assert_eq!(result, sum_ne);
}

#[test]
fn test_constant_sum_no_bounds_returns_unchanged() {
    let g = ConstantSumGeneralizer::new();
    let mut ts = MockTransitionSystem::new();
    // No init_bounds set

    let x = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
    let y = ChcExpr::var(ChcVar::new("y", ChcSort::Int));
    let lemma = ChcExpr::and(
        ChcExpr::eq(x, ChcExpr::int(3)),
        ChcExpr::eq(y, ChcExpr::int(7)),
    );

    let result = g.generalize(&lemma, 1, &mut ts);

    // Should preserve (no init bounds available)
    assert_eq!(result, lemma);
}

// =========================================================================
// RelationalEqualityGeneralizer Integration Tests
// =========================================================================

#[test]
fn test_relational_equality_discovers_equality() {
    let g = RelationalEqualityGeneralizer::new();
    let mut ts = MockTransitionSystem::new();

    // Lemma: x = 5 AND y = 3 (values DIFFER)
    // RelationalEquality looks for states where v1 != v2 and checks if NOT(v1 = v2) is inductive
    let x = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
    let y = ChcExpr::var(ChcVar::new("y", ChcSort::Int));
    let lemma = ChcExpr::and(
        ChcExpr::eq(x.clone(), ChcExpr::int(5)),
        ChcExpr::eq(y.clone(), ChcExpr::int(3)),
    );

    // Mark NOT(x = y) as inductive (the disequality blocking formula)
    let disequality = ChcExpr::not(ChcExpr::eq(x, y));
    ts.mark_inductive(&format!("{disequality:?}"));

    let result = g.generalize(&lemma, 1, &mut ts);

    // Should discover NOT(x = y)
    assert_eq!(result, disequality);
}

#[test]
fn test_relational_equality_needs_multiple_equalities() {
    let g = RelationalEqualityGeneralizer::new();
    let mut ts = MockTransitionSystem::new();

    // Single equality - RelationalEquality needs at least 2
    let x = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
    let lemma = ChcExpr::eq(x, ChcExpr::int(5));

    let result = g.generalize(&lemma, 1, &mut ts);

    // Should return unchanged (need >= 2 equalities)
    assert_eq!(result, lemma);
}

// =========================================================================
// ImplicationGeneralizer Integration Tests
// =========================================================================

#[test]
fn test_implication_discovers_conditional() {
    let g = ImplicationGeneralizer::new();
    let mut ts = MockTransitionSystem::new();

    // Lemma: pc = 2 AND lock = 1
    let pc = ChcExpr::var(ChcVar::new("pc", ChcSort::Int));
    let lock = ChcExpr::var(ChcVar::new("lock", ChcSort::Int));
    let lemma = ChcExpr::and(
        ChcExpr::eq(pc.clone(), ChcExpr::int(2)),
        ChcExpr::eq(lock.clone(), ChcExpr::int(1)),
    );

    // Mark implication as inductive: (pc = 2) => (lock = 1)
    // In CNF: NOT(pc = 2) OR NOT(lock != 1) = (pc != 2) OR (lock = 1)
    let impl_cnf = ChcExpr::or(
        ChcExpr::ne(pc, ChcExpr::int(2)),
        ChcExpr::eq(lock, ChcExpr::int(1)),
    );
    ts.mark_inductive(&format!("{impl_cnf:?}"));

    let _result = g.generalize(&lemma, 1, &mut ts);

    // ImplicationGeneralizer should discover conditional pattern
    // Verify queries were made
    assert!(!ts.queries.borrow().is_empty());
}

mod pipeline;
