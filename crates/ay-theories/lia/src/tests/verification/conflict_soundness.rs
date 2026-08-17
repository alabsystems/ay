// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Conflict-explanation soundness regressions.

use super::*;

// ========================================================================
// Phase 2 Verification Tests - LIA Conflict Soundness (#298)
// ========================================================================
//
// These tests verify that LIA conflict explanations are semantically sound.
// They catch bugs like #294 where a theory returns a conflict that doesn't
// actually conflict.

/// Verify simple integer bounds conflict explanations are sound.
#[test]
fn test_lia_bounds_conflict_soundness() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));
    let ten = terms.mk_int(BigInt::from(10));

    // x <= 5 AND x >= 10 is UNSAT
    let le_5 = terms.mk_le(x, five);
    let ge_10 = terms.mk_ge(x, ten);

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(le_5, true);
    solver.assert_literal(ge_10, true);

    let result = solver.check();
    assert_conflict_soundness(result, LiaSolver::new(&terms));
}

/// Verify integer gap conflict explanations are sound.
/// x > 5 AND x < 6 is UNSAT for integers (no integer in (5, 6)).
#[test]
fn test_lia_integer_gap_conflict_soundness() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));
    let six = terms.mk_int(BigInt::from(6));

    // x > 5 AND x < 6 is UNSAT for integers
    let gt_5 = terms.mk_gt(x, five);
    let lt_6 = terms.mk_lt(x, six);

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(gt_5, true);
    solver.assert_literal(lt_6, true);

    let result = solver.check();
    assert_conflict_soundness(result, LiaSolver::new(&terms));
}

/// Verify GCD test failure conflict explanations are sound.
/// 4*x + 4*y + 4*z - 2*w = 49 is UNSAT because GCD(4,4,4,2)=2 doesn't divide 49.
#[test]
#[allow(clippy::many_single_char_names)]
fn test_lia_gcd_conflict_soundness() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let z = terms.mk_var("z", Sort::Int);
    let w = terms.mk_var("w", Sort::Int);

    let four = terms.mk_int(BigInt::from(4));
    let minus_two = terms.mk_int(BigInt::from(-2));
    let forty_nine = terms.mk_int(BigInt::from(49));

    let four_x = terms.mk_mul(vec![four, x]);
    let four_y = terms.mk_mul(vec![four, y]);
    let four_z = terms.mk_mul(vec![four, z]);
    let minus_two_w = terms.mk_mul(vec![minus_two, w]);

    let lhs = terms.mk_add(vec![four_x, four_y, four_z, minus_two_w]);
    let eq = terms.mk_eq(lhs, forty_nine);

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(eq, true);

    let result = solver.check();
    assert_conflict_soundness(result, LiaSolver::new(&terms));
}

/// Verify linear combination conflict explanations are sound.
#[test]
fn test_lia_linear_combination_conflict_soundness() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let c5 = terms.mk_int(BigInt::from(5));
    let c6 = terms.mk_int(BigInt::from(6));
    let c10 = terms.mk_int(BigInt::from(10));

    // x + y <= 10 AND x >= 5 AND y >= 6 is UNSAT (5 + 6 = 11 > 10)
    let sum = terms.mk_add(vec![x, y]);
    let sum_le = terms.mk_le(sum, c10);
    let x_ge = terms.mk_ge(x, c5);
    let y_ge = terms.mk_ge(y, c6);

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(sum_le, true);
    solver.assert_literal(x_ge, true);
    solver.assert_literal(y_ge, true);

    let result = solver.check();
    assert_conflict_soundness(result, LiaSolver::new(&terms));
}

/// Ensure no bogus conflicts for SAT cases.
#[test]
fn test_lia_no_bogus_conflict_on_sat() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let c3 = terms.mk_int(BigInt::from(3));
    let c4 = terms.mk_int(BigInt::from(4));
    let c10 = terms.mk_int(BigInt::from(10));

    // x + y <= 10 AND x >= 3 AND y >= 4 is SAT (3 + 4 = 7 <= 10)
    let sum = terms.mk_add(vec![x, y]);
    let sum_le = terms.mk_le(sum, c10);
    let x_ge = terms.mk_ge(x, c3);
    let y_ge = terms.mk_ge(y, c4);

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(sum_le, true);
    solver.assert_literal(x_ge, true);
    solver.assert_literal(y_ge, true);

    // Should be SAT (or NeedSplit for branch-and-bound)
    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat | TheoryResult::NeedSplit(_)),
        "Should be SAT or NeedSplit, not a bogus conflict: {result:?}"
    );
}

/// Verify equality + bound conflict explanations are sound.
#[test]
fn test_lia_equality_bound_conflict_soundness() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));

    // x = 5 AND x > 5 is UNSAT
    let eq_5 = terms.mk_eq(x, five);
    let gt_5 = terms.mk_gt(x, five);

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(eq_5, true);
    solver.assert_literal(gt_5, true);

    let result = solver.check();
    assert_conflict_soundness(result, LiaSolver::new(&terms));
}
