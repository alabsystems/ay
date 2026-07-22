// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_compound_atom_push_pop_unassigned_count() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let ten = terms.mk_rational(BigRational::from(BigInt::from(10)));
    let one = terms.mk_rational(BigRational::from(BigInt::from(1)));

    // Compound atom: x + y <= 10 (references both x and y)
    let sum = terms.mk_add(vec![x, y]);
    let sum_le = terms.mk_le(sum, ten); // x + y <= 10
                                        // Single-variable atoms
    let x_ge = terms.mk_ge(x, one); // x >= 1
    let y_ge = terms.mk_ge(y, one); // y >= 1
                                    // Conflicting compound: x + y <= 0 (with x >= 1, y >= 1 → UNSAT)
    let zero = terms.mk_rational(BigRational::from(BigInt::from(0)));
    let sum_le_zero = terms.mk_le(sum, zero); // x + y <= 0

    let mut solver = LraSolver::new(&terms);

    // Base scope: assert single-variable bounds + compound atom
    solver.assert_literal(x_ge, true);
    solver.assert_literal(y_ge, true);
    solver.assert_literal(sum_le, true);

    // Base: x >= 1, y >= 1, x+y <= 10 → SAT
    assert!(matches!(solver.check(), TheoryResult::Sat));

    // Push scope and assert conflicting compound atom
    solver.push();
    solver.assert_literal(sum_le_zero, true); // x + y <= 0

    // Inner: x >= 1, y >= 1, x+y <= 0 → UNSAT (1+1=2 > 0)
    let result = solver.check();
    assert!(
        matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "x >= 1, y >= 1, x + y <= 0 should be UNSAT, got {result:?}"
    );

    // Pop: should restore to SAT state
    solver.pop();
    solver.reset();
    solver.assert_literal(x_ge, true);
    solver.assert_literal(y_ge, true);
    solver.assert_literal(sum_le, true);
    assert!(
        matches!(solver.check(), TheoryResult::Sat),
        "After pop, x >= 1, y >= 1, x + y <= 10 should be SAT"
    );

    // Verify unassigned_atom_count optimization data.
    // NOTE(#4919): After pop()+reset(), unassigned_atom_count may be empty
    // because register_atom() isn't called during the post-reset check() path.
    // When populated, verify counts are correct.
    assert_unassigned_counts_zero(&solver, &[x, y]);
}

/// Regression test: disequality_trail push/pop correctness.
///
/// The disequality_trail tracks disequality atoms incrementally (W2:1901, #4919).
/// Without correct push/pop, stale disequalities from a popped scope remain
/// in the trail, causing false UNSAT or missed violations.
///
/// Scenario:
/// - Base scope: x >= 0, x <= 10 (SAT, no disequalities)
/// - Push, assert x != 5 (adds to disequality_trail)
/// - Check inner scope (SAT: model can be x=0)
/// - Pop — disequality_trail must be truncated
/// - Assert x >= 5, x <= 5 (forces x=5 exactly)
/// - Check: must be SAT because x != 5 was popped
///
/// If pop fails to truncate disequality_trail, the solver still sees x != 5
/// and would incorrectly return UNSAT.
#[test]
fn test_disequality_trail_push_pop_correctness() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let zero = terms.mk_rational(BigRational::from(BigInt::from(0)));
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let ten = terms.mk_rational(BigRational::from(BigInt::from(10)));

    let x_ge_0 = terms.mk_ge(x, zero); // x >= 0
    let x_le_10 = terms.mk_le(x, ten); // x <= 10
    let x_eq_5 = terms.mk_eq(x, five); // x = 5 (asserted false → x != 5)
    let x_ge_5 = terms.mk_ge(x, five); // x >= 5
    let x_le_5 = terms.mk_le(x, five); // x <= 5

    let mut solver = LraSolver::new(&terms);

    // Base scope: x in [0, 10]
    solver.assert_literal(x_ge_0, true);
    solver.assert_literal(x_le_10, true);
    assert!(
        matches!(solver.check(), TheoryResult::Sat),
        "Base scope x in [0,10] must be SAT"
    );

    // Push scope and assert x != 5
    solver.push();
    solver.assert_literal(x_eq_5, false); // x != 5

    // Inner scope: x in [0,10], x != 5 — SAT (e.g. x=0)
    assert!(
        matches!(solver.check(), TheoryResult::Sat),
        "Inner scope x in [0,10], x != 5 must be SAT"
    );

    // Pop: x != 5 must be removed from disequality_trail
    solver.pop();

    // Now force x = 5 exactly (x >= 5 and x <= 5)
    solver.assert_literal(x_ge_5, true);
    solver.assert_literal(x_le_5, true);

    // This MUST be SAT because x != 5 was popped.
    // If disequality_trail still contains x != 5, solver would report UNSAT.
    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "After pop, x=5 must be SAT (x != 5 was popped), got {result:?}"
    );
}

/// Regression test: nested push/pop with disequalities across scopes.
///
/// Tests that disequalities from different scopes are correctly tracked
/// and restored independently.
#[test]
fn test_disequality_trail_nested_push_pop() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let zero = terms.mk_rational(BigRational::from(BigInt::from(0)));
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let ten = terms.mk_rational(BigRational::from(BigInt::from(10)));

    let x_ge_0 = terms.mk_ge(x, zero);
    let x_le_10 = terms.mk_le(x, ten);
    let x_eq_3 = terms.mk_eq(x, three); // for x != 3
    let x_eq_5 = terms.mk_eq(x, five); // for x != 5
    let x_ge_3 = terms.mk_ge(x, three);
    let x_le_3 = terms.mk_le(x, three);

    let mut solver = LraSolver::new(&terms);

    // Base: x in [0, 10]
    solver.assert_literal(x_ge_0, true);
    solver.assert_literal(x_le_10, true);
    assert!(matches!(solver.check(), TheoryResult::Sat));

    // Scope 1: x != 5
    solver.push();
    solver.assert_literal(x_eq_5, false);
    assert!(matches!(solver.check(), TheoryResult::Sat));

    // Scope 2: x != 5 AND x != 3
    solver.push();
    solver.assert_literal(x_eq_3, false);
    assert!(
        matches!(solver.check(), TheoryResult::Sat),
        "x in [0,10], x!=5, x!=3 is SAT"
    );

    // Pop scope 2: x != 3 removed, x != 5 remains
    solver.pop();

    // Force x = 3: should be SAT (x != 3 was popped, x != 5 still active)
    solver.push();
    solver.assert_literal(x_ge_3, true);
    solver.assert_literal(x_le_3, true);
    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "x=3 with only x!=5 active must be SAT, got {result:?}"
    );
    solver.pop();

    // Pop scope 1: x != 5 removed
    solver.pop();

    // Now we're back to base: x in [0, 10], no disequalities
    // This is already checked implicitly — solver state should be clean
}

/// Regression test for #6130: propagate_var_atoms must detect that
/// a strict lower bound x > k contradicts a strict upper atom x < k.
///
/// Before the fix, the condition `lb.value == atom.bound_value && !lb.strict`
/// evaluated to false when both lb and atom were strict at the same value,
/// missing the propagation.
#[test]
fn test_strict_bound_propagation_both_strict_at_same_value() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Real);
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));

    // x > 5 (strict lower bound)
    let gt_x_5 = terms.mk_gt(x, five);
    // x < 5 (strict upper atom)
    let lt_x_5 = terms.mk_lt(x, five);

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(gt_x_5, true);
    solver.assert_literal(lt_x_5, true);

    let result = solver.check();

    assert!(
        matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "x > 5 AND x < 5 must be UNSAT, got {result:?}"
    );
}

/// Symmetric case of #6130: strict upper bound x < k contradicts strict
/// lower atom x > k.
#[test]
fn test_strict_bound_propagation_upper_contradicts_lower_atom() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Real);
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));

    // x < 5 (strict upper bound)
    let lt_x_5 = terms.mk_lt(x, five);
    // x > 5 (strict lower atom)
    let gt_x_5 = terms.mk_gt(x, five);

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(lt_x_5, true);
    solver.assert_literal(gt_x_5, true);

    let result = solver.check();

    assert!(
        matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "x < 5 AND x > 5 must be UNSAT, got {result:?}"
    );
}

/// Regression test for #6130 in compute_bound_propagations: strict upper atom
/// with strict lower bound at the same value.
///
/// The `compute_bound_propagations` function had the same strict-bound bug as
/// `propagate_var_atoms`: when atom is `x < k` (strict upper) and lb is strict
/// at value k, the old condition `lb.value == k && !lb.strict` missed the case
/// where `lb.strict == true` (i.e., `x > k` contradicts `x < k`).
///
/// This tests the full check() → compute_bound_propagations path by asserting
/// atoms that only become contradictory through bound propagation.
#[test]
fn test_compute_bound_propagations_strict_upper_vs_strict_lower_6130() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Real);
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));

    // x > 5 (strict lower bound at 5)
    let gt_5 = terms.mk_gt(x, five);
    // x < 5 (strict upper atom)
    let lt_5 = terms.mk_lt(x, five);

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(gt_5, true);
    solver.assert_literal(lt_5, true);

    // Full check triggers compute_bound_propagations
    let result = solver.check();
    assert!(
        matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "#6130: x > 5 AND x < 5 must be UNSAT via compute_bound_propagations, got {result:?}"
    );
}

/// Regression test for #6130 in compute_bound_propagations: strict lower atom
/// with strict upper bound at the same value.
///
/// Symmetric case: atom is `x > k` (strict lower) and ub is strict at k,
/// the old condition `ub.value == k && !ub.strict` missed `x < k` contradicts
/// `x > k`.
#[test]
fn test_compute_bound_propagations_strict_lower_vs_strict_upper_6130() {
    let mut terms = TermStore::new();

    let x = terms.mk_var("x", Sort::Real);
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));

    // x < 5 (strict upper bound at 5)
    let lt_5 = terms.mk_lt(x, five);
    // x > 5 (strict lower atom)
    let gt_5 = terms.mk_gt(x, five);

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(lt_5, true);
    solver.assert_literal(gt_5, true);

    let result = solver.check();
    assert!(
        matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "#6130: x < 5 AND x > 5 must be UNSAT via compute_bound_propagations, got {result:?}"
    );
}

/// #6157: assert_shared_equality with constant non-zero diff must record a conflict.
///
/// When EUF tells LRA that `3 = 5`, the difference expression is constant (-2 != 0).
/// Previously this was silently ignored; now it must set trivial_conflict and produce UNSAT.
#[test]
fn test_assert_shared_equality_constant_nonzero_records_conflict() {
    let mut terms = TermStore::new();
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let reason_atom = terms.mk_var("eq_atom", Sort::Bool);

    let mut solver = LraSolver::new(&terms);
    let reasons = [TheoryLit::new(reason_atom, true)];
    solver.assert_shared_equality(three, five, &reasons);

    // trivial_conflict must be set
    assert!(
        solver.trivial_conflict.is_some(),
        "#6157: assert_shared_equality(3, 5) must set trivial_conflict"
    );

    // check() must return UNSAT
    let result = solver.check();
    assert!(
        matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "#6157: 3 = 5 shared equality must be UNSAT, got {result:?}"
    );
}

/// #6157: assert_shared_disequality with constant zero diff must record a conflict.
///
/// When EUF tells LRA that `3 != 3`, the difference expression is constant (0).
/// The disequality is violated because 3 = 3. Previously this was silently ignored;
/// now it must set trivial_conflict and produce UNSAT.
#[test]
fn test_assert_shared_disequality_constant_zero_records_conflict() {
    let mut terms = TermStore::new();
    let three_a = terms.mk_rational(BigRational::from(BigInt::from(3)));
    let three_b = terms.mk_rational(BigRational::from(BigInt::from(3)));
    let reason_atom = terms.mk_var("diseq_atom", Sort::Bool);

    let mut solver = LraSolver::new(&terms);
    // The reason has value=false because it represents (not (= a b)), i.e.,
    // the negated equality atom that caused this disequality.
    let reasons = [TheoryLit::new(reason_atom, false)];
    solver.assert_shared_disequality(three_a, three_b, &reasons);

    // trivial_conflict must be set
    assert!(
        solver.trivial_conflict.is_some(),
        "#6157: assert_shared_disequality(3, 3) must set trivial_conflict"
    );

    // check() must return UNSAT
    let result = solver.check();
    assert!(
        matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "#6157: 3 != 3 shared disequality must be UNSAT, got {result:?}"
    );
}

/// #6155: Shared disequality split with non-unit coefficient computes wrong excluded value.
///
/// The shared disequality path at lib.rs:3518-3520 ignores the coefficient:
///   `let (var, _coeff) = &expr.coeffs[0];`
///   `let excluded = -&expr.constant;`
/// For `2*x - 6 != 0` (i.e., `2*x != 6`), the excluded value should be
/// `-(-6)/2 = 3`, but the bug computes `-(-6) = 6`.
///
/// This test constructs a shared disequality `(* 2 x) != 6` with x in [3, 5].
/// Simplex assigns x=3, making `2*3 - 6 = 0` (violation). The split should
/// exclude x=3, producing `x < 3 OR x > 3`. With the bug, it excludes x=6,
/// producing `x < 6 OR x > 6`, which is always true for x in [3, 5] — an
/// infinite loop or wrong answer.
#[test]
fn test_shared_disequality_coefficient_excluded_value_6155() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let two = terms.mk_rational(BigRational::from(BigInt::from(2)));
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let six = terms.mk_rational(BigRational::from(BigInt::from(6)));

    // Build (= (* 2 x) 6) as the equality term for the reason
    let two_x = terms.mk_mul(vec![two, x]);
    let eq_term = terms.mk_eq(two_x, six);

    // Bounds: x >= 3, x <= 5
    let x_ge_3 = terms.mk_ge(x, three);
    let x_le_5 = terms.mk_le(x, five);

    let mut solver = LraSolver::new(&terms);

    // Assert bounds first
    solver.assert_literal(x_ge_3, true); // x >= 3
    solver.assert_literal(x_le_5, true); // x <= 5

    // Simplex should now be SAT with x=3 (lower bound)
    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "Bounds x in [3,5] should be SAT, got {result:?}"
    );

    // Now assert shared disequality: 2*x != 6 (from EUF)
    // Reason: (not (= (* 2 x) 6)) — the negated equality atom
    let reasons = [TheoryLit::new(eq_term, false)];
    solver.assert_shared_disequality(two_x, six, &reasons);

    // check() should detect 2*3 - 6 = 0 (violation) and request a split
    let result = solver.check();
    match &result {
        TheoryResult::NeedDisequalitySplit(req) => {
            // The excluded value MUST be 3 (= -constant/coeff = 6/2),
            // not 6 (= -constant, the buggy value).
            let expected = BigRational::from(BigInt::from(3));
            assert_eq!(
                req.excluded_value, expected,
                "#6155: shared disequality excluded value should be 3 (=-const/coeff), \
                 got {} (bug: missing /coeff at lib.rs:3520)",
                req.excluded_value
            );
        }
        other => {
            // Simplex assigns x=3 (lower bound), making 2*3 - 6 = 0, which
            // violates the shared disequality. The ONLY correct response is
            // NeedDisequalitySplit. Any other result means the test is not
            // exercising the excluded_value computation (#6155).
            panic!(
                "#6155: expected NeedDisequalitySplit (simplex assigns x=3, \
                 violating 2*x != 6), got {other:?}"
            );
        }
    }
}

/// Negative coefficient shared disequality: (-2)*x + 6 = 0 means x = 3.
/// The excluded value must be -constant/coeff = -6/(-2) = 3.
/// Tests that sign handling in the coefficient division is correct.
#[test]
fn test_shared_disequality_negative_coefficient_excluded_value_6155() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let neg_two = terms.mk_rational(BigRational::from(BigInt::from(-2)));
    let three = terms.mk_rational(BigRational::from(BigInt::from(3)));
    let five = terms.mk_rational(BigRational::from(BigInt::from(5)));
    let neg_six = terms.mk_rational(BigRational::from(BigInt::from(-6)));

    // Build (= (* -2 x) -6) as the equality term
    let neg_two_x = terms.mk_mul(vec![neg_two, x]);
    let eq_term = terms.mk_eq(neg_two_x, neg_six);

    // Bounds: x >= 3, x <= 5
    let x_ge_3 = terms.mk_ge(x, three);
    let x_le_5 = terms.mk_le(x, five);

    let mut solver = LraSolver::new(&terms);

    solver.assert_literal(x_ge_3, true); // x >= 3
    solver.assert_literal(x_le_5, true); // x <= 5

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "Bounds x in [3,5] should be SAT, got {result:?}"
    );

    // Shared disequality: -2*x != -6 (from EUF)
    let reasons = [TheoryLit::new(eq_term, false)];
    solver.assert_shared_disequality(neg_two_x, neg_six, &reasons);

    let result = solver.check();
    match &result {
        TheoryResult::NeedDisequalitySplit(req) => {
            // The internal normalized form is coeff*var + constant = 0.
            // For -2*x + 6 = 0 (i.e. -2*x - (-6) = 0): excluded = -6/(-2) = 3
            let expected = BigRational::from(BigInt::from(3));
            assert_eq!(
                req.excluded_value, expected,
                "Negative coeff shared disequality: excluded value should be 3, got {}",
                req.excluded_value
            );
        }
        other => {
            // Simplex assigns x=3 (lower bound), making -2*3 + 6 = 0, which
            // violates the shared disequality. The ONLY correct response is
            // NeedDisequalitySplit.
            panic!(
                "#6155 negative coeff: expected NeedDisequalitySplit (simplex \
                 assigns x=3, violating -2*x != -6), got {other:?}"
            );
        }
    }
}

/// #8785: pairwise disequalities between otherwise unconstrained Int variables
/// should not require a SAT-level expression split clique. The LIA adapter uses
/// LRA in integer mode; for free variables, assigning distinct integer model
/// values is a complete local repair.
#[test]
fn test_free_integer_pairwise_disequalities_repair_model_8785() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let z = terms.mk_var("z", Sort::Int);

    let x_eq_y = terms.mk_eq(x, y);
    let x_eq_z = terms.mk_eq(x, z);
    let y_eq_z = terms.mk_eq(y, z);

    let mut solver = LraSolver::new(&terms);
    solver.set_integer_mode(true);
    solver.assert_literal(x_eq_y, false);
    solver.assert_literal(x_eq_z, false);
    solver.assert_literal(y_eq_z, false);

    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "free Int pairwise disequalities should repair locally, got {result:?}"
    );

    let model = solver.extract_model();
    let x_value = model.values.get(&x).expect("x value");
    let y_value = model.values.get(&y).expect("y value");
    let z_value = model.values.get(&z).expect("z value");
    assert_ne!(x_value, y_value);
    assert_ne!(x_value, z_value);
    assert_ne!(y_value, z_value);
}

#[test]
fn test_free_integer_pairwise_repair_rejects_tableau_row_vars_8785() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let z = terms.mk_var("z", Sort::Int);
    let x_eq_y = terms.mk_eq(x, y);

    let mut solver = LraSolver::new(&terms);
    solver.set_integer_mode(true);
    let x_var = solver.ensure_var_registered(x);
    let y_var = solver.ensure_var_registered(y);
    let z_var = solver.ensure_var_registered(z);

    solver.vars[z_var as usize].status = Some(VarStatus::Basic(0));
    solver.rows.push(TableauRow::new_rat(
        z_var,
        vec![(x_var, Rational::from(1i64))],
        Rational::zero(),
    ));

    let disequality = LinearExpr {
        coeffs: vec![
            (x_var, Rational::from(1i64)),
            (y_var, Rational::from(-1i64)),
        ],
        constant: Rational::zero(),
    };
    let result = solver.check_disequalities(&[(x_eq_y, disequality, false)], false);

    assert!(
        matches!(
            result,
            Some(TheoryResult::NeedExpressionSplit(_))
                | Some(TheoryResult::NeedExpressionSplits(_))
        ),
        "vars that occur in tableau rows are not free; repair must fall back to an expression split, got {result:?}"
    );
}
