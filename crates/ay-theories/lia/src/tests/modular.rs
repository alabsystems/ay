// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// === Cube test edge case tests (Z3: int_cube.cpp) ===
//
// These tests exercise the cube test path in the LIA solver's check().
// The cube test tightens LP bounds and rounds to integers.

/// Cube test with only unbounded variables: no bounds to tighten, so the cube
/// test should gracefully return false and fall through to other techniques.
/// The solver must still produce a correct result.
#[test]
fn test_cube_test_unbounded_vars_still_solves() {
    let mut terms = TermStore::new();

    // x + y = 10 with no bounds on x or y.
    // LP relaxation immediately gives integer solution (x=10, y=0 or similar).
    // Cube test may or may not fire; solver must return SAT regardless.
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let ten = terms.mk_int(BigInt::from(10));

    let lhs = terms.mk_add(vec![x, y]);
    let eq = terms.mk_eq(lhs, ten);

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(eq, true);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat | TheoryResult::NeedSplit(_)),
        "x + y = 10 over integers must be SAT: {result:?}"
    );
}

/// Cube test with strict inequalities: x > 0, x < 2 (only x=1 is integer).
/// The LP relaxation gives a fractional optimum in (0,2). The cube test
/// (or other techniques) must find x=1.
#[test]
fn test_cube_test_strict_inequalities_single_solution() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let two = terms.mk_int(BigInt::from(2));

    let gt_zero = terms.mk_gt(x, zero); // x > 0
    let lt_two = terms.mk_lt(x, two); // x < 2

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(gt_zero, true);
    solver.assert_literal(lt_two, true);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat | TheoryResult::NeedSplit(_)),
        "x > 0, x < 2 has integer solution x=1: {result:?}"
    );

    // If SAT, verify the model gives x=1
    if matches!(result, TheoryResult::Sat) {
        let model = solver
            .extract_model()
            .expect("SAT result must produce a model");
        let val = model
            .values
            .get(&x)
            .expect("model must contain value for x");
        assert_eq!(*val, BigInt::from(1), "only integer in (0,2) is 1");
    }
}

/// Cube test with same-sign unit coefficient row: x + y = 3 with 1 <= x <= 2, 1 <= y <= 2.
/// This exercises the delta=1 case (AY bug #2669: should be epsilon, not 1).
/// The LP relaxation may give fractional values; the cube test should
/// find the integer solution.
#[test]
fn test_cube_test_same_sign_unit_coefficients() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let one = terms.mk_int(BigInt::from(1));
    let two = terms.mk_int(BigInt::from(2));
    let three = terms.mk_int(BigInt::from(3));

    let lhs = terms.mk_add(vec![x, y]);
    let eq = terms.mk_eq(lhs, three); // x + y = 3
    let x_ge = terms.mk_ge(x, one); // x >= 1
    let x_le = terms.mk_le(x, two); // x <= 2
    let y_ge = terms.mk_ge(y, one); // y >= 1
    let y_le = terms.mk_le(y, two); // y <= 2

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(eq, true);
    solver.assert_literal(x_ge, true);
    solver.assert_literal(x_le, true);
    solver.assert_literal(y_ge, true);
    solver.assert_literal(y_le, true);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat | TheoryResult::NeedSplit(_)),
        "x + y = 3 with 1<=x<=2, 1<=y<=2 has solutions (1,2) and (2,1): {result:?}"
    );
}

/// Cube test with tight bounds that leave exactly one integer feasible.
/// x >= 0.5 and x <= 1.5 (via 2*x >= 1 and 2*x <= 3) with integer x.
/// After LP relaxation, the cube test must find x=1.
/// This stresses the rounding path: if rounding goes to 0 or 2, bounds are violated.
#[test]
fn test_cube_test_rounding_must_respect_bounds() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Int);
    let two = terms.mk_int(BigInt::from(2));
    let one = terms.mk_int(BigInt::from(1));
    let three = terms.mk_int(BigInt::from(3));

    let two_x = terms.mk_mul(vec![two, x]);
    let ge = terms.mk_ge(two_x, one); // 2*x >= 1, i.e., x >= 0.5
    let le = terms.mk_le(two_x, three); // 2*x <= 3, i.e., x <= 1.5

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(ge, true);
    solver.assert_literal(le, true);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat | TheoryResult::NeedSplit(_)),
        "2*x >= 1 and 2*x <= 3 has integer solution x=1: {result:?}"
    );

    if matches!(result, TheoryResult::Sat) {
        let model = solver
            .extract_model()
            .expect("SAT result must produce a model");
        let val = model
            .values
            .get(&x)
            .expect("model must contain value for x");
        assert_eq!(*val, BigInt::from(1), "only integer in [0.5, 1.5] is 1");
    }
}

/// Difference constraint row: x - y = 0, x >= 0, x <= 10.
/// The cube_delta_for_row should return 0 for this row (no tightening needed).
/// The solver should find an integer solution trivially.
#[test]
fn test_cube_test_difference_constraint_delta_zero() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let ten = terms.mk_int(BigInt::from(10));

    let eq = terms.mk_eq(x, y); // x - y = 0
    let x_ge = terms.mk_ge(x, zero);
    let x_le = terms.mk_le(x, ten);

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(eq, true);
    solver.assert_literal(x_ge, true);
    solver.assert_literal(x_le, true);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat | TheoryResult::NeedSplit(_)),
        "x = y with 0 <= x <= 10 must be SAT: {result:?}"
    );
}

/// Test that cube test one-shot guard prevents infinite loop.
/// This is a regression test for the system_11 non-progress loop (#2475).
/// Use a problem where the cube test fails (infeasible with tightened bounds)
/// but the solver should still terminate (via Gomory cuts or branching).
#[test]
fn test_cube_test_one_shot_prevents_loop() {
    let mut terms = TermStore::new();

    // 3*x + 5*y = 7, 0 <= x <= 10, 0 <= y <= 10.
    // LP relaxation gives fractional solution. Cube test likely fails
    // due to large coefficients. Solver must still terminate.
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let three = terms.mk_int(BigInt::from(3));
    let five = terms.mk_int(BigInt::from(5));
    let seven = terms.mk_int(BigInt::from(7));
    let zero = terms.mk_int(BigInt::from(0));
    let ten = terms.mk_int(BigInt::from(10));

    let three_x = terms.mk_mul(vec![three, x]);
    let five_y = terms.mk_mul(vec![five, y]);
    let lhs = terms.mk_add(vec![three_x, five_y]);
    let eq = terms.mk_eq(lhs, seven); // 3x + 5y = 7

    let x_ge = terms.mk_ge(x, zero);
    let x_le = terms.mk_le(x, ten);
    let y_ge = terms.mk_ge(y, zero);
    let y_le = terms.mk_le(y, ten);

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(eq, true);
    solver.assert_literal(x_ge, true);
    solver.assert_literal(x_le, true);
    solver.assert_literal(y_ge, true);
    solver.assert_literal(y_le, true);

    // Must terminate (not loop forever).
    // 3x+5y=7 has no non-negative integer solution:
    //   x=0: 5y=7, no integer y.  x=1: 5y=4, no.  x=2: 5y=1, no.
    // So this is UNSAT over x,y >= 0. The solver may return UNSAT directly
    // or NeedSplit (requesting DPLL-level branching). Either is correct
    // termination behavior — the key property is that it terminates, not loops.
    let result = solver.check();
    assert!(
        !matches!(result, TheoryResult::Sat),
        "3x+5y=7 with x,y in [0,10] has no non-negative integer solution, \
         should not be SAT: {result:?}"
    );
}

#[test]
fn test_should_try_gomory_before_cube_attempt() {
    let terms = TermStore::new();
    let solver = LiaSolver::new(&terms);
    assert!(
        solver.should_try_gomory(false),
        "Gomory should be available before cube test is attempted"
    );
}

#[test]
fn test_should_not_try_gomory_after_cube_attempt() {
    let terms = TermStore::new();
    let solver = LiaSolver::new(&terms);
    assert!(
        !solver.should_try_gomory(true),
        "Gomory must be blocked once cube test has been attempted"
    );
}

#[test]
fn test_should_not_try_gomory_after_iteration_budget_exhausted() {
    let terms = TermStore::new();
    let mut solver = LiaSolver::new(&terms);
    solver.gomory_iterations = solver.max_gomory_iterations;
    assert!(
        !solver.should_try_gomory(false),
        "Gomory should stop when max iteration budget is exhausted"
    );
}

/// Verify that GCD-based bound tightening carries equality reasons.
///
/// Setup: x = 3*y (GCD = 3, so x ≡ 0 mod 3)
///        x <= 5 → tightened to x <= 3 (largest multiple of 3 ≤ 5)
///        x >= 4 → tightened to x >= 6 (smallest multiple of 3 ≥ 4)
///
/// After tightening: x ∈ [6, 3] which is infeasible.
/// The conflict must include the equality (x = 3*y) as a reason.
#[test]
fn test_gcd_tightening_carries_equality_reasons() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let three = terms.mk_int(BigInt::from(3));
    let four = terms.mk_int(BigInt::from(4));
    let five = terms.mk_int(BigInt::from(5));

    let three_y = terms.mk_mul(vec![three, y]);
    let eq = terms.mk_eq(x, three_y); // x = 3*y
    let x_ge_4 = terms.mk_ge(x, four); // x >= 4
    let x_le_5 = terms.mk_le(x, five); // x <= 5

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(eq, true);
    solver.assert_literal(x_ge_4, true);
    solver.assert_literal(x_le_5, true);

    let result = solver.check();
    // x ≡ 0 (mod 3), x in [4, 5] → GCD tightens to [6, 3] → UNSAT
    assert!(
        matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "x=3y with x in [4,5] should be UNSAT (no multiple of 3 in [4,5]): {result:?}"
    );

    // Extract the conflict literals
    let conflict_lits = match &result {
        TheoryResult::Unsat(lits) => lits.clone(),
        TheoryResult::UnsatWithFarkas(conflict) => conflict.literals.clone(),
        _ => unreachable!(),
    };

    // Conflict reasons must include both tightened bounds and the equality
    // that introduced the divisibility (mod-3) restriction.
    assert!(
        conflict_lits.iter().any(|lit| lit.term == eq && lit.value),
        "GCD tightening conflict must include equality x=3y as a reason. \
         Got conflict: {conflict_lits:?}"
    );
    assert!(
        conflict_lits
            .iter()
            .any(|lit| lit.term == x_ge_4 && lit.value),
        "GCD tightening conflict must include lower bound x>=4. \
         Got conflict: {conflict_lits:?}"
    );
    assert!(
        conflict_lits
            .iter()
            .any(|lit| lit.term == x_le_5 && lit.value),
        "GCD tightening conflict must include upper bound x<=5. \
         Got conflict: {conflict_lits:?}"
    );
}

/// Test that Diophantine substitution-based GCD tightening detects
/// integer infeasibility that the LRA relaxation misses.
///
/// Setup: x = 3*y (equality), 10 <= x <= 11, y >= 0.
/// LRA relaxation: x ∈ [10, 11], y = x/3 ∈ [10/3, 11/3] ≈ [3.33, 3.67]. SAT.
/// Integer: x = 3*y ⟹ x ≡ 0 (mod 3). No multiple of 3 in [10, 11]. UNSAT.
///
/// The Dioph solver produces substitution x = 3*y, which the per-variable
/// GCD tightening (and potentially `tighten_tableau_rows_via_dioph()`) uses
/// to tighten x's bounds, detecting the conflict.
#[test]
fn test_tableau_row_gcd_tightening_via_dioph_substitution() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let three = terms.mk_int(BigInt::from(3));
    let ten = terms.mk_int(BigInt::from(10));
    let eleven = terms.mk_int(BigInt::from(11));

    // x = 3*y
    let three_y = terms.mk_mul(vec![three, y]);
    let eq = terms.mk_eq(x, three_y);

    // 10 <= x <= 11
    let x_ge_10 = terms.mk_ge(x, ten);
    let x_le_11 = terms.mk_le(x, eleven);

    // y >= 0
    let y_ge_0 = terms.mk_ge(y, zero);

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(eq, true);
    solver.assert_literal(x_ge_10, true);
    solver.assert_literal(x_le_11, true);
    solver.assert_literal(y_ge_0, true);

    let result = solver.check();

    // LRA relaxation is SAT (x=10.5, y=3.5), but x = 3y means x ≡ 0 (mod 3).
    // No multiple of 3 in [10, 11] → UNSAT via Dioph GCD tightening.
    assert!(
        matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "Dioph GCD tightening should detect UNSAT: x=3y, 10<=x<=11. Got: {result:?}"
    );
}

// ── Modular constraint unit tests (#3198) ──────────────────────────────────

/// GCD-based bound tightening with non-coprime coefficients.
///
/// r = 4*x + 6*y => GCD(4,6)=2, so r ≡ 0 (mod 2). With r in [3, 7],
/// the GCD tightening should narrow to r in [4, 6] (nearest even values).
/// The system is SAT (e.g., x=1, y=0 gives r=4).
#[test]
fn test_modular_gcd_tightening_non_coprime_sat() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let r = terms.mk_var("r", Sort::Int);
    let four = terms.mk_int(BigInt::from(4));
    let six = terms.mk_int(BigInt::from(6));
    let three = terms.mk_int(BigInt::from(3));
    let seven = terms.mk_int(BigInt::from(7));

    let four_x = terms.mk_mul(vec![four, x]);
    let six_y = terms.mk_mul(vec![six, y]);
    let sum = terms.mk_add(vec![four_x, six_y]);
    let eq = terms.mk_eq(r, sum);
    let r_ge_3 = terms.mk_ge(r, three);
    let r_le_7 = terms.mk_le(r, seven);

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(eq, true);
    solver.assert_literal(r_ge_3, true);
    solver.assert_literal(r_le_7, true);

    let result = solver.check();
    // NeedSplit is valid: LIA may require branch-and-bound. The key is it's NOT Unsat.
    assert!(
        !matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "r = 4x + 6y with 3 <= r <= 7 should NOT be UNSAT (e.g., x=1,y=0 gives r=4). Got: {result:?}"
    );
}

/// GCD tightening detects modular infeasibility.
///
/// r = 4*x + 6*y => r ≡ 0 (mod 2). With r = 3 (odd), this is UNSAT.
#[test]
fn test_modular_gcd_tightening_non_coprime_unsat() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let r = terms.mk_var("r", Sort::Int);
    let four = terms.mk_int(BigInt::from(4));
    let six = terms.mk_int(BigInt::from(6));
    let three = terms.mk_int(BigInt::from(3));

    let four_x = terms.mk_mul(vec![four, x]);
    let six_y = terms.mk_mul(vec![six, y]);
    let sum = terms.mk_add(vec![four_x, six_y]);
    let eq = terms.mk_eq(r, sum);
    let r_ge_3 = terms.mk_ge(r, three);
    let r_le_3 = terms.mk_le(r, three);

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(eq, true);
    solver.assert_literal(r_ge_3, true);
    solver.assert_literal(r_le_3, true);

    let result = solver.check();
    assert!(
        matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "r = 4x + 6y with r = 3 is UNSAT (3 is odd, r must be even). Got: {result:?}"
    );
}

/// Coprime coefficients: GCD = 1, no modular tightening possible.
///
/// r = 3*x + 5*y => GCD(3,5)=1. With r = 7, solutions exist (x=4,y=-1).
#[test]
fn test_modular_coprime_coefficients_no_tightening() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let r = terms.mk_var("r", Sort::Int);
    let three = terms.mk_int(BigInt::from(3));
    let five = terms.mk_int(BigInt::from(5));
    let seven = terms.mk_int(BigInt::from(7));

    let three_x = terms.mk_mul(vec![three, x]);
    let five_y = terms.mk_mul(vec![five, y]);
    let sum = terms.mk_add(vec![three_x, five_y]);
    let eq = terms.mk_eq(r, sum);
    let r_ge_7 = terms.mk_ge(r, seven);
    let r_le_7 = terms.mk_le(r, seven);

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(eq, true);
    solver.assert_literal(r_ge_7, true);
    solver.assert_literal(r_le_7, true);

    let result = solver.check();
    // NeedSplit is valid: LIA may require branch-and-bound. The key is it's NOT Unsat.
    assert!(
        !matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "r = 3x + 5y with r = 7 should NOT be UNSAT (GCD=1, e.g. x=4,y=-1). Got: {result:?}"
    );
}

/// Modular constraint conflict: mod 3 with tight bounds.
///
/// r = 3*x with r in [1, 2]. Since r ≡ 0 (mod 3), there is no multiple
/// of 3 in [1, 2], so this is UNSAT.
#[test]
fn test_modular_constraint_conflict_tight_bounds() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let r = terms.mk_var("r", Sort::Int);
    let three = terms.mk_int(BigInt::from(3));
    let one = terms.mk_int(BigInt::from(1));
    let two = terms.mk_int(BigInt::from(2));

    let three_x = terms.mk_mul(vec![three, x]);
    let eq = terms.mk_eq(r, three_x);
    let r_ge_1 = terms.mk_ge(r, one);
    let r_le_2 = terms.mk_le(r, two);

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(eq, true);
    solver.assert_literal(r_ge_1, true);
    solver.assert_literal(r_le_2, true);

    let result = solver.check();
    assert!(
        matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "r = 3x with 1 <= r <= 2 is UNSAT (no multiple of 3 in [1,2]). Got: {result:?}"
    );
}

/// Modular constraint satisfiable: mod 3 with wider bounds.
///
/// r = 3*x with r in [1, 4]. r = 3 is valid (x = 1).
#[test]
fn test_modular_constraint_satisfiable_wider_bounds() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let r = terms.mk_var("r", Sort::Int);
    let three = terms.mk_int(BigInt::from(3));
    let one = terms.mk_int(BigInt::from(1));
    let four = terms.mk_int(BigInt::from(4));

    let three_x = terms.mk_mul(vec![three, x]);
    let eq = terms.mk_eq(r, three_x);
    let r_ge_1 = terms.mk_ge(r, one);
    let r_le_4 = terms.mk_le(r, four);

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(eq, true);
    solver.assert_literal(r_ge_1, true);
    solver.assert_literal(r_le_4, true);

    let result = solver.check();
    // NeedSplit is valid: branch-and-bound may be needed. Not Unsat is the check.
    assert!(
        !matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "r = 3x with 1 <= r <= 4 should NOT be UNSAT (r=3, x=1). Got: {result:?}"
    );
}

/// Interval bound propagation: positive coefficient direction.
///
/// r = 2*x + 1 with 0 <= x <= 5 implies 1 <= r <= 11.
/// Assert r >= 12 to create a conflict via propagation.
#[test]
fn test_modular_interval_propagation_positive_coeff_conflict() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let r = terms.mk_var("r", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let two = terms.mk_int(BigInt::from(2));
    let five = terms.mk_int(BigInt::from(5));
    let one = terms.mk_int(BigInt::from(1));
    let twelve = terms.mk_int(BigInt::from(12));

    let two_x = terms.mk_mul(vec![two, x]);
    let sum = terms.mk_add(vec![two_x, one]);
    let eq = terms.mk_eq(r, sum);
    let x_ge_0 = terms.mk_ge(x, zero);
    let x_le_5 = terms.mk_le(x, five);
    let r_ge_12 = terms.mk_ge(r, twelve);

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(eq, true);
    solver.assert_literal(x_ge_0, true);
    solver.assert_literal(x_le_5, true);
    solver.assert_literal(r_ge_12, true);

    let result = solver.check();
    assert!(
        matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "r = 2x+1, 0<=x<=5 implies r<=11, so r>=12 is UNSAT. Got: {result:?}"
    );
}

/// Interval propagation with negative coefficient.
///
/// r = -3*x + 10 with 0 <= x <= 4 implies -2 <= r <= 10.
/// Assert r >= 11 to create a conflict.
#[test]
fn test_modular_interval_propagation_negative_coeff_conflict() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let r = terms.mk_var("r", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let neg3 = terms.mk_int(BigInt::from(-3));
    let four = terms.mk_int(BigInt::from(4));
    let ten = terms.mk_int(BigInt::from(10));
    let eleven = terms.mk_int(BigInt::from(11));

    let neg3_x = terms.mk_mul(vec![neg3, x]);
    let sum = terms.mk_add(vec![neg3_x, ten]);
    let eq = terms.mk_eq(r, sum);
    let x_ge_0 = terms.mk_ge(x, zero);
    let x_le_4 = terms.mk_le(x, four);
    let r_ge_11 = terms.mk_ge(r, eleven);

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(eq, true);
    solver.assert_literal(x_ge_0, true);
    solver.assert_literal(x_le_4, true);
    solver.assert_literal(r_ge_11, true);

    let result = solver.check();
    assert!(
        matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "r = -3x+10, 0<=x<=4 implies r<=10, so r>=11 is UNSAT. Got: {result:?}"
    );
}

/// Boundary condition: empty interval from strict bounds.
///
/// x > 5 and x < 6 for integer x has no solution (5.something is not integer).
/// The modular check should handle strict bounds correctly.
#[test]
fn test_modular_boundary_strict_bounds_empty_interval() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));
    let six = terms.mk_int(BigInt::from(6));

    let gt_5 = terms.mk_gt(x, five);
    let lt_6 = terms.mk_lt(x, six);

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(gt_5, true);
    solver.assert_literal(lt_6, true);

    let result = solver.check();
    assert!(
        matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "x > 5 and x < 6 for integer x is UNSAT. Got: {result:?}"
    );
}

/// Large coefficient values: GCD tightening with big numbers.
///
/// r = 1000000*x + 1000000*y => GCD = 1000000. With r = 500001, UNSAT
/// (500001 mod 1000000 = 500001 != 0).
#[test]
fn test_modular_large_coefficients_gcd_tightening() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let r = terms.mk_var("r", Sort::Int);
    let million = terms.mk_int(BigInt::from(1_000_000));
    let million2 = terms.mk_int(BigInt::from(1_000_000));
    let target = terms.mk_int(BigInt::from(500_001));

    let mx = terms.mk_mul(vec![million, x]);
    let my = terms.mk_mul(vec![million2, y]);
    let sum = terms.mk_add(vec![mx, my]);
    let eq = terms.mk_eq(r, sum);
    let r_ge = terms.mk_ge(r, target);
    let r_le = terms.mk_le(r, target);

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(eq, true);
    solver.assert_literal(r_ge, true);
    solver.assert_literal(r_le, true);

    let result = solver.check();
    assert!(
        matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "r = 10^6*x + 10^6*y with r = 500001 is UNSAT (GCD=10^6). Got: {result:?}"
    );
}

// ── check_disequality_vs_modular coverage tests (proof_coverage) ────────────

/// When r = 2*x (so r is even), bounds 0 <= r <= 1, and disequality r != 0,
/// the only even value in [0,1] is 0, and excluding it leaves no valid integer.
/// check_disequality_vs_modular should detect this and return UNSAT.
///
/// This exercises the dioph_cached_substitutions path in check_disequality_vs_modular.
#[test]
fn test_disequality_vs_modular_unique_value_excluded_unsat() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let r = terms.mk_var("r", Sort::Int);
    let two = terms.mk_int(BigInt::from(2));
    let zero = terms.mk_int(BigInt::from(0));
    let one = terms.mk_int(BigInt::from(1));
    let zero_b = terms.mk_int(BigInt::from(0));

    // r = 2*x
    let two_x = terms.mk_mul(vec![two, x]);
    let eq = terms.mk_eq(r, two_x);
    // 0 <= r <= 1
    let r_ge_0 = terms.mk_ge(r, zero);
    let r_le_1 = terms.mk_le(r, one);
    // r != 0  (asserted as (= r 0) = false)
    let r_eq_0 = terms.mk_eq(r, zero_b);

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(eq, true);
    solver.assert_literal(r_ge_0, true);
    solver.assert_literal(r_le_1, true);
    solver.assert_literal(r_eq_0, false); // r != 0

    let result = solver.check();
    // r = 2x means r is even. In [0,1] the only even value is 0.
    // r != 0 excludes it. Must be UNSAT.
    assert!(
        matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "r = 2x, 0 <= r <= 1, r != 0: only even value in [0,1] is 0, excluded. \
         Should be UNSAT. Got: {result:?}"
    );
}

// ── cell/03_as_slice_of_cells: modular disequality conflict must carry the
//    remainder bounds (#cell03) ────────────────────────────────────────────
//
// `s[i]@ % 2 == 1` elimination introduces `x = 2q + r`, `0 <= r`, `r < 2`.
// When the search excludes the unique valid residue (`r != 1`), the modular
// disequality check returns a conflict. That conflict's UNSAT conclusion (the
// only residue in [0,1] satisfying `r ≡ residue (mod 2)` is 1, which is
// excluded) DEPENDS on the bounds `0 <= r` and `r < 2`. If the conflict drops
// them, the minimal `[2q+r=1, r!=1]` clause is SAT in isolation (q=-1, r=3) and
// the runtime conflict verifier rejects it as spurious, forcing Unknown
// (the original cell/03 blocker). This test pins that the produced conflict
// is sound *in isolation* — exactly the property the verifier checks.
#[test]
fn test_disequality_vs_modular_conflict_includes_remainder_bounds_cell03() {
    let mut terms = TermStore::new();
    let q = terms.mk_var("_mod_q", Sort::Int);
    let r = terms.mk_var("_mod_r", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let one = terms.mk_int(BigInt::from(1));
    let two = terms.mk_int(BigInt::from(2));

    // 2*q + r = 1   (the `x = 2q + r` decomposition with x pinned to 1)
    let two_q = terms.mk_mul(vec![two, q]);
    let sum = terms.mk_add(vec![two_q, r]);
    let eq = terms.mk_eq(one, sum);
    // 0 <= r  and  r < 2   (remainder bounds from mod-2 elimination)
    let r_ge_0 = terms.mk_ge(r, zero);
    let r_lt_2 = terms.mk_lt(r, two);
    // r != 1  (asserted as (= r 1) = false)
    let r_eq_1 = terms.mk_eq(r, one);

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(eq, true);
    solver.assert_literal(r_ge_0, true);
    solver.assert_literal(r_lt_2, true);
    solver.assert_literal(r_eq_1, false);

    let result = solver.check();
    assert!(
        matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "2q+r=1, 0<=r<2, r!=1: r is forced to 1 (excluded) -> UNSAT. Got: {result:?}"
    );

    let conflict_lits = match &result {
        TheoryResult::Unsat(lits) => lits.clone(),
        TheoryResult::UnsatWithFarkas(conflict) => conflict.literals.clone(),
        _ => unreachable!(),
    };

    // Soundness of the explanation: re-solving with ONLY the conflict literals
    // must still be UNSAT. This is exactly what verify_lia_conflict_semantic
    // does at runtime; before the fix the conflict dropped the remainder bounds
    // and this isolated re-check came back SAT (q=-1, r=3).
    let verify = LiaSolver::new(&terms);
    assert_conflict_soundness(TheoryResult::Unsat(conflict_lits.clone()), verify);

    // And the bounds must literally be present (the direct cause of the bug):
    // at least one remainder bound is required to make the residue interval
    // finite; we require BOTH for the `[0,1]` interval the conclusion uses.
    assert!(
        conflict_lits.iter().any(|l| l.term == r_ge_0 && l.value),
        "modular disequality conflict must include lower remainder bound 0<=r: {conflict_lits:?}"
    );
    assert!(
        conflict_lits.iter().any(|l| l.term == r_lt_2 && l.value),
        "modular disequality conflict must include upper remainder bound r<2: {conflict_lits:?}"
    );
}

/// SAT-preservation guard for the cell/03 fix: when the disequality does NOT
/// make the system UNSAT (the excluded value is not the unique valid residue),
/// the modular machinery must NOT manufacture a conflict. With `0 <= r < 4` and
/// `2q + r = 1`, residues {1, 3} are valid; excluding r=1 still leaves r=3, so
/// the system is satisfiable and must not be reported UNSAT.
#[test]
fn test_disequality_vs_modular_does_not_overtrigger_when_satisfiable_cell03() {
    let mut terms = TermStore::new();
    let q = terms.mk_var("_mod_q", Sort::Int);
    let r = terms.mk_var("_mod_r", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let one = terms.mk_int(BigInt::from(1));
    let two = terms.mk_int(BigInt::from(2));
    let four = terms.mk_int(BigInt::from(4));

    let two_q = terms.mk_mul(vec![two, q]);
    let sum = terms.mk_add(vec![two_q, r]);
    let eq = terms.mk_eq(one, sum);
    let r_ge_0 = terms.mk_ge(r, zero);
    let r_lt_4 = terms.mk_lt(r, four); // r in {0,1,2,3}
    let r_eq_1 = terms.mk_eq(r, one);

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(eq, true);
    solver.assert_literal(r_ge_0, true);
    solver.assert_literal(r_lt_4, true);
    solver.assert_literal(r_eq_1, false);

    let result = solver.check();
    assert!(
        !matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "2q+r=1, 0<=r<4, r!=1: r=3 (q=-1) is still valid -> NOT UNSAT. Got: {result:?}"
    );
}

/// When r = 2*x, bounds 0 <= r <= 2, and disequality r != 0,
/// r can still be 2 (which is even). So the result should NOT be UNSAT.
#[test]
fn test_disequality_vs_modular_second_value_exists_sat() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let r = terms.mk_var("r", Sort::Int);
    let two = terms.mk_int(BigInt::from(2));
    let zero = terms.mk_int(BigInt::from(0));
    let two_b = terms.mk_int(BigInt::from(2));
    let zero_b = terms.mk_int(BigInt::from(0));

    // r = 2*x
    let two_x = terms.mk_mul(vec![two, x]);
    let eq = terms.mk_eq(r, two_x);
    // 0 <= r <= 2
    let r_ge_0 = terms.mk_ge(r, zero);
    let r_le_2 = terms.mk_le(r, two_b);
    // r != 0
    let r_eq_0 = terms.mk_eq(r, zero_b);

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(eq, true);
    solver.assert_literal(r_ge_0, true);
    solver.assert_literal(r_le_2, true);
    solver.assert_literal(r_eq_0, false); // r != 0

    let result = solver.check();
    // r = 2x, 0 <= r <= 2: even values are 0 and 2. r != 0 leaves r=2.
    // Should NOT be UNSAT (could be Sat or NeedSplit).
    assert!(
        !matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "r = 2x, 0 <= r <= 2, r != 0: r=2 is still valid. \
         Should NOT be UNSAT. Got: {result:?}"
    );
}

/// assert_shared_equality with multiple reason literals: verify the reasons
/// are accessible (or truncated, documenting the current behavior for #4891).
///
/// This test documents the CURRENT behavior where LIA truncates multi-reason
/// shared equalities to a single reason. When #4891 is fixed, this test
/// should be updated to verify all reasons are preserved.
#[test]
fn test_assert_shared_equality_multi_reason_behavior() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));
    let ten = terms.mk_int(BigInt::from(10));

    // Set up contradictory state: x = 5, y = 10
    let x_eq_5 = terms.mk_eq(x, five);
    let y_eq_10 = terms.mk_eq(y, ten);

    // Create reason literals (simulating EUF transitivity chain)
    let r1 = terms.mk_var("r1", Sort::Bool);
    let r2 = terms.mk_var("r2", Sort::Bool);

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(x_eq_5, true); // x = 5
    solver.assert_literal(y_eq_10, true); // y = 10

    // Now tell LIA that x = y (with two reason literals from EUF)
    // This should create a contradiction: x=5, y=10, but x=y
    let reason = vec![TheoryLit::new(r1, true), TheoryLit::new(r2, true)];
    solver.assert_shared_equality(x, y, &reason);

    let result = solver.check();
    // Must detect UNSAT: x=5, y=10, x=y is contradictory
    assert!(
        matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "x=5, y=10, x=y should be UNSAT. Got: {result:?}"
    );

    // Extract conflict reasons
    let conflict_lits = match &result {
        TheoryResult::Unsat(lits) => lits.clone(),
        TheoryResult::UnsatWithFarkas(farkas) => farkas.literals.clone(),
        _ => unreachable!(),
    };

    // The conflict should reference the reason literals.
    // Current known issue (#4891): LIA truncates to first reason only.
    // This documents the current behavior — when fixed, both r1 and r2
    // should appear in the conflict.
    let has_r1 = conflict_lits.iter().any(|l| l.term == r1);
    let has_r2 = conflict_lits.iter().any(|l| l.term == r2);

    if has_r1 && has_r2 {
        // Full reasons preserved — #4891 fix is in place
    } else if has_r1 || has_r2 {
        // Only one reason — documents current truncation behavior
        eprintln!(
            "NOTE: assert_shared_equality reason truncation (#4891): \
             only {} of 2 reason literals in conflict. \
             has_r1={has_r1}, has_r2={has_r2}",
            if has_r1 { 1 } else { 0 } + if has_r2 { 1 } else { 0 }
        );
    }
    // Either way, the conflict must include the asserted bounds
    assert!(
        !conflict_lits.is_empty(),
        "Conflict reasons must not be empty"
    );
}

/// GCD test: 5x + 7y = 11 has integer solutions (x=5, y=-2).
///
/// After the #5648 fix, the basic variable's coefficient (lcm_den) is included
/// in the GCD: GCD(5,7) = 1 divides 11. The pre-fix code computed GCD on
/// non-basic coefficients only, which could falsely report UNSAT when the basic
/// variable's coefficient was coprime with other coefficients.
#[test]
fn test_gcd_coprime_5x_7y_eq_11() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let r = terms.mk_var("r", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));
    let seven = terms.mk_int(BigInt::from(7));
    let eleven = terms.mk_int(BigInt::from(11));

    let five_x = terms.mk_mul(vec![five, x]);
    let seven_y = terms.mk_mul(vec![seven, y]);
    let sum = terms.mk_add(vec![five_x, seven_y]);
    let eq = terms.mk_eq(r, sum);
    let r_ge = terms.mk_ge(r, eleven);
    let r_le = terms.mk_le(r, eleven);

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(eq, true);
    solver.assert_literal(r_ge, true);
    solver.assert_literal(r_le, true);

    let result = solver.check();
    assert!(
        !matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "5x + 7y = 11 should NOT be UNSAT (GCD(5,7)=1, e.g. x=5,y=-2). Got: {result:?}"
    );
}

/// GCD test: 4x + 6y = 3 is genuinely UNSAT because GCD(4,6) = 2 does not divide 3.
///
/// Regression guard: the #5648 fix must not weaken the GCD test. When ALL
/// coefficients (including the basic variable's lcm_den) share a common factor
/// that doesn't divide the constant, the solver must still detect UNSAT.
#[test]
fn test_gcd_non_coprime_4x_6y_eq_3_unsat() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let r = terms.mk_var("r", Sort::Int);
    let four = terms.mk_int(BigInt::from(4));
    let six = terms.mk_int(BigInt::from(6));
    let three = terms.mk_int(BigInt::from(3));

    let four_x = terms.mk_mul(vec![four, x]);
    let six_y = terms.mk_mul(vec![six, y]);
    let sum = terms.mk_add(vec![four_x, six_y]);
    let eq = terms.mk_eq(r, sum);
    let r_ge = terms.mk_ge(r, three);
    let r_le = terms.mk_le(r, three);

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(eq, true);
    solver.assert_literal(r_ge, true);
    solver.assert_literal(r_le, true);

    let result = solver.check();
    // 4x + 6y = 3 has no integer solutions: GCD(4,6)=2 does not divide 3.
    // The solver may return Unsat directly (GCD test) or NeedSplit (before
    // branch-and-bound detects infeasibility). Both are acceptable for the
    // GCD test guard — the key is it must NOT return Sat.
    assert!(
        !matches!(result, TheoryResult::Sat),
        "4x + 6y = 3 must NOT be SAT (GCD(4,6)=2 does not divide 3). Got: {result:?}"
    );
}

/// GCD test with three variables, one fixed: 2x + 3y + 5z = 1, z = 0.
///
/// With z fixed at 0, the equation becomes 2x + 3y = 1 which has integer
/// solutions (e.g., x=2, y=-1). Tests interaction between fixed-variable
/// constant accumulation and the basic variable coefficient inclusion (#5648).
#[test]
fn test_gcd_three_var_one_fixed_2x_3y_5z_eq_1() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let z = terms.mk_var("z", Sort::Int);
    let r = terms.mk_var("r", Sort::Int);
    let two = terms.mk_int(BigInt::from(2));
    let three = terms.mk_int(BigInt::from(3));
    let five = terms.mk_int(BigInt::from(5));
    let one = terms.mk_int(BigInt::from(1));
    let zero = terms.mk_int(BigInt::from(0));

    let two_x = terms.mk_mul(vec![two, x]);
    let three_y = terms.mk_mul(vec![three, y]);
    let five_z = terms.mk_mul(vec![five, z]);
    let sum = terms.mk_add(vec![two_x, three_y, five_z]);
    let eq = terms.mk_eq(r, sum);
    let r_ge = terms.mk_ge(r, one);
    let r_le = terms.mk_le(r, one);
    let z_ge = terms.mk_ge(z, zero);
    let z_le = terms.mk_le(z, zero);

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(eq, true);
    solver.assert_literal(r_ge, true);
    solver.assert_literal(r_le, true);
    solver.assert_literal(z_ge, true);
    solver.assert_literal(z_le, true);

    let result = solver.check();
    assert!(
        !matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "2x + 3y + 5(0) = 1 should NOT be UNSAT (GCD(2,3)=1, e.g. x=2,y=-1). Got: {result:?}"
    );
}

/// GCD test: non-basic coefficients share a factor but basic variable breaks it.
///
/// 6x + 10y + 15z = 7. Non-basic pair GCD(10,15) = 5 does not divide 7.
/// But GCD(6,10,15) = 1 DOES divide 7, so the equation is SAT (integer solutions
/// exist). This tests that the basic variable coefficient (lcm_den) properly
/// reduces the overall GCD.
#[test]
fn test_gcd_basic_var_breaks_non_basic_factor() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let z = terms.mk_var("z", Sort::Int);
    let r = terms.mk_var("r", Sort::Int);
    let six = terms.mk_int(BigInt::from(6));
    let ten = terms.mk_int(BigInt::from(10));
    let fifteen = terms.mk_int(BigInt::from(15));
    let seven = terms.mk_int(BigInt::from(7));

    let six_x = terms.mk_mul(vec![six, x]);
    let ten_y = terms.mk_mul(vec![ten, y]);
    let fifteen_z = terms.mk_mul(vec![fifteen, z]);
    let sum = terms.mk_add(vec![six_x, ten_y, fifteen_z]);
    let eq = terms.mk_eq(r, sum);
    let r_ge = terms.mk_ge(r, seven);
    let r_le = terms.mk_le(r, seven);

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(eq, true);
    solver.assert_literal(r_ge, true);
    solver.assert_literal(r_le, true);

    let result = solver.check();
    assert!(
        !matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "6x + 10y + 15z = 7 should NOT be UNSAT (GCD(6,10,15)=1). Got: {result:?}"
    );
}
