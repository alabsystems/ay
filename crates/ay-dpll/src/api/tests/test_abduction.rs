// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the abduction API: abduce() and synthesize_patch().

use crate::api::types::Logic;
use crate::api::{PatchStrength, Solver, Sort};

// ============================================================================
// abduce() tests
// ============================================================================

/// Test: goal already implied by assertions => abduce returns None.
#[test]
fn test_abduce_goal_already_implied() {
    let mut solver = Solver::try_new(Logic::QfLia).expect("QF_LIA supported");

    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let ten = solver.int_const(10);

    // Assert: x > 0 AND x < 10
    let x_gt_0 = solver.try_gt(x, zero).expect("int > int");
    let x_lt_10 = solver.try_lt(x, ten).expect("int < int");
    solver.try_assert_term(x_gt_0).expect("ok");
    solver.try_assert_term(x_lt_10).expect("ok");

    // Goal: x >= 0 (already implied by x > 0)
    let goal = solver.try_ge(x, zero).expect("int >= int");

    // Vocabulary: some irrelevant conditions
    let hundred = solver.int_const(100);
    let x_lt_100 = solver.try_lt(x, hundred).expect("ok");
    let vocab = vec![x_lt_100];

    let result = solver
        .abduce(goal, &vocab)
        .expect("abduce should not error");
    assert!(
        result.is_none(),
        "goal already implied, abduce should return None"
    );
}

/// Test: single vocabulary term suffices as guard.
#[test]
fn test_abduce_single_guard() {
    let mut solver = Solver::try_new(Logic::QfLia).expect("QF_LIA supported");

    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);

    // No assertions constraining x — it can be anything.
    // Goal: x >= 0
    let goal = solver.try_ge(x, zero).expect("int >= int");

    // Vocabulary: x >= 0 (the guard itself is exactly the goal)
    let guard = solver.try_ge(x, zero).expect("int >= int");
    let vocab = vec![guard];

    let result = solver
        .abduce(goal, &vocab)
        .expect("abduce should not error");
    assert!(result.is_some(), "single guard should suffice for the goal");
}

/// Test: no vocabulary term is sufficient.
#[test]
fn test_abduce_no_sufficient_guard() {
    let mut solver = Solver::try_new(Logic::QfLia).expect("QF_LIA supported");

    let x = solver.declare_const("x", Sort::Int);
    let y = solver.declare_const("y", Sort::Int);
    let zero = solver.int_const(0);

    // Goal: x >= 0 AND y >= 0 (need both)
    let x_ge_0 = solver.try_ge(x, zero).expect("ok");
    let y_ge_0 = solver.try_ge(y, zero).expect("ok");
    let goal = solver.try_and(x_ge_0, y_ge_0).expect("ok");

    // Vocabulary: only x > 5 (does not cover y)
    let five = solver.int_const(5);
    let x_gt_5 = solver.try_gt(x, five).expect("ok");
    let vocab = vec![x_gt_5];

    let result = solver
        .abduce(goal, &vocab)
        .expect("abduce should not error");
    assert!(
        result.is_none(),
        "single guard on x cannot imply x >= 0 AND y >= 0"
    );
}

/// Test: pairwise combination suffices.
#[test]
fn test_abduce_pairwise_guard() {
    let mut solver = Solver::try_new(Logic::QfLia).expect("QF_LIA supported");

    let x = solver.declare_const("x", Sort::Int);
    let y = solver.declare_const("y", Sort::Int);
    let zero = solver.int_const(0);

    // Goal: x >= 0 AND y >= 0
    let x_ge_0 = solver.try_ge(x, zero).expect("ok");
    let y_ge_0 = solver.try_ge(y, zero).expect("ok");
    let goal = solver.try_and(x_ge_0, y_ge_0).expect("ok");

    // Vocabulary: x >= 0, y >= 0 (each alone is insufficient, pair works)
    let vocab = vec![x_ge_0, y_ge_0];

    let result = solver
        .abduce(goal, &vocab)
        .expect("abduce should not error");
    assert!(
        result.is_some(),
        "pairwise combination should suffice for goal"
    );
}

/// Test: empty vocabulary returns None.
#[test]
fn test_abduce_empty_vocabulary() {
    let mut solver = Solver::try_new(Logic::QfLia).expect("QF_LIA supported");
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let goal = solver.try_ge(x, zero).expect("ok");

    let result = solver.abduce(goal, &[]).expect("abduce should not error");
    assert!(
        result.is_none(),
        "empty vocabulary means no guard can be found"
    );
}

// ============================================================================
// synthesize_patch() tests
// ============================================================================

/// Test: single patch point eliminates vulnerability.
#[test]
fn test_synthesize_patch_single_point() {
    let mut solver = Solver::try_new(Logic::QfLia).expect("QF_LIA supported");

    let buf_size = solver.declare_const("buf_size", Sort::Int);
    let idx = solver.declare_const("idx", Sort::Int);

    // Assert: buf_size = 10
    let ten = solver.int_const(10);
    let buf_eq_10 = solver.try_eq(buf_size, ten).expect("ok");
    solver.try_assert_term(buf_eq_10).expect("ok");

    // Vulnerability: idx >= buf_size (buffer overflow)
    let vuln = solver.try_ge(idx, buf_size).expect("ok");

    // Patch point: idx < buf_size (bounds check)
    let bounds_check = solver.try_lt(idx, buf_size).expect("ok");

    // Also need idx >= 0 to fully prevent negative index issues,
    // but for this test, just the upper bound is sufficient since the
    // vulnerability is idx >= buf_size.
    let patch_points = vec![bounds_check];

    let result = solver
        .synthesize_patch(vuln, &patch_points)
        .expect("should not error");
    assert!(result.is_some(), "bounds check should eliminate overflow");
    let suggestion = result.unwrap();
    assert_eq!(suggestion.location, 0);
    assert_eq!(suggestion.strength, PatchStrength::Minimal);
}

/// Test: multiple candidates — pick weakest (first valid single).
#[test]
fn test_synthesize_patch_picks_weakest() {
    let mut solver = Solver::try_new(Logic::QfLia).expect("QF_LIA supported");

    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let ten = solver.int_const(10);
    let hundred = solver.int_const(100);

    // Vulnerability: x < 0
    let vuln = solver.try_lt(x, zero).expect("ok");

    // Patch points:
    //   0: x >= 0 (weakest sufficient)
    //   1: x >= 10 (stronger than needed)
    //   2: x >= 100 (even stronger)
    let guard0 = solver.try_ge(x, zero).expect("ok");
    let guard1 = solver.try_ge(x, ten).expect("ok");
    let guard2 = solver.try_ge(x, hundred).expect("ok");

    let patch_points = vec![guard0, guard1, guard2];

    let result = solver
        .synthesize_patch(vuln, &patch_points)
        .expect("should not error");
    assert!(result.is_some(), "guards should eliminate vulnerability");
    let suggestion = result.unwrap();
    // Should pick the first valid single patch (index 0).
    assert_eq!(suggestion.location, 0);
    assert_eq!(suggestion.strength, PatchStrength::Minimal);
}

/// Test: no valid patch exists.
#[test]
fn test_synthesize_patch_none_valid() {
    let mut solver = Solver::try_new(Logic::QfLia).expect("QF_LIA supported");

    let x = solver.declare_const("x", Sort::Int);
    let y = solver.declare_const("y", Sort::Int);
    let zero = solver.int_const(0);

    // Vulnerability: x < 0 (x is unconstrained)
    let vuln = solver.try_lt(x, zero).expect("ok");

    // Patch points: only constraining y (irrelevant to vuln)
    let y_pos = solver.try_gt(y, zero).expect("ok");
    let hundred = solver.int_const(100);
    let y_big = solver.try_gt(y, hundred).expect("ok");

    let result = solver
        .synthesize_patch(vuln, &[y_pos, y_big])
        .expect("should not error");
    assert!(
        result.is_none(),
        "y-constraints cannot eliminate x<0 vulnerability"
    );
}

/// Test: vulnerability already unreachable => returns None.
#[test]
fn test_synthesize_patch_already_safe() {
    let mut solver = Solver::try_new(Logic::QfLia).expect("QF_LIA supported");

    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);

    // Assert: x >= 5 (x is always positive)
    let five = solver.int_const(5);
    let x_ge_5 = solver.try_ge(x, five).expect("ok");
    solver.try_assert_term(x_ge_5).expect("ok");

    // Vulnerability: x < 0 (impossible given x >= 5)
    let vuln = solver.try_lt(x, zero).expect("ok");

    let guard = solver.try_ge(x, zero).expect("ok");

    let result = solver
        .synthesize_patch(vuln, &[guard])
        .expect("should not error");
    assert!(
        result.is_none(),
        "vulnerability already unreachable, no patch needed"
    );
}

/// Test: empty patch points returns None.
#[test]
fn test_synthesize_patch_empty_points() {
    let mut solver = Solver::try_new(Logic::QfLia).expect("QF_LIA supported");
    let x = solver.declare_const("x", Sort::Int);
    let zero = solver.int_const(0);
    let vuln = solver.try_lt(x, zero).expect("ok");

    let result = solver
        .synthesize_patch(vuln, &[])
        .expect("should not error");
    assert!(result.is_none(), "no patch points means no patch");
}

/// Test: BV-specific buffer overflow with bounds check patch.
#[test]
fn test_synthesize_patch_bv_buffer_overflow() {
    let mut solver = Solver::try_new(Logic::QfBv).expect("QF_BV supported");

    let bv32 = Sort::bitvec(32);

    let buf_size = solver.declare_const("buf_size", bv32.clone());
    let idx = solver.declare_const("idx", bv32.clone());

    // Assert: buf_size = 64 (fixed buffer size)
    let sixty_four = solver.bv_const(64i64, 32);
    let buf_eq = solver.try_eq(buf_size, sixty_four).expect("ok");
    solver.try_assert_term(buf_eq).expect("ok");

    // Vulnerability: idx >=_u buf_size (unsigned overflow)
    let vuln = solver.try_bvuge(idx, buf_size).expect("ok");

    // Patch: idx <_u buf_size (unsigned bounds check)
    let bounds_check = solver.try_bvult(idx, buf_size).expect("ok");

    let result = solver
        .synthesize_patch(vuln, &[bounds_check])
        .expect("should not error");
    assert!(
        result.is_some(),
        "BV bounds check should eliminate overflow"
    );
    let suggestion = result.unwrap();
    assert_eq!(suggestion.location, 0);
    assert_eq!(suggestion.strength, PatchStrength::Minimal);
}

/// Test: pairwise patch needed (moderate strength).
#[test]
fn test_synthesize_patch_pairwise() {
    let mut solver = Solver::try_new(Logic::QfLia).expect("QF_LIA supported");

    let x = solver.declare_const("x", Sort::Int);
    let y = solver.declare_const("y", Sort::Int);
    let zero = solver.int_const(0);

    // Vulnerability: x < 0 OR y < 0
    let x_neg = solver.try_lt(x, zero).expect("ok");
    let y_neg = solver.try_lt(y, zero).expect("ok");
    let vuln = solver.try_or(x_neg, y_neg).expect("ok");

    // Patch points: x >= 0 and y >= 0 (each alone insufficient,
    // but together they eliminate the vulnerability).
    let x_guard = solver.try_ge(x, zero).expect("ok");
    let y_guard = solver.try_ge(y, zero).expect("ok");

    let result = solver
        .synthesize_patch(vuln, &[x_guard, y_guard])
        .expect("should not error");
    assert!(
        result.is_some(),
        "pairwise guards should eliminate the vulnerability"
    );
    let suggestion = result.unwrap();
    assert_eq!(suggestion.strength, PatchStrength::Moderate);
}

/// Test: PatchStrength Display impl.
#[test]
fn test_patch_strength_display() {
    assert_eq!(PatchStrength::Minimal.to_string(), "minimal");
    assert_eq!(PatchStrength::Moderate.to_string(), "moderate");
    assert_eq!(PatchStrength::Aggressive.to_string(), "aggressive");
}
