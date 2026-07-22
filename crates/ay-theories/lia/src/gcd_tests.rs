// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for GCD-based infeasibility detection.

use super::*;

#[test]
fn tableau_gcd_basic_variable_coefficient_prevents_false_unsat() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let three = terms.mk_int(BigInt::from(3));
    let five = terms.mk_int(BigInt::from(5));
    let seven = terms.mk_int(BigInt::from(7));

    // 3*x + 5*y = 7 has integer solutions (for example x = -1, y = 2), but the
    // LP relaxation exposes a fractional tableau row such as x = 7/3 - 5/3*y.
    // The #5648 fix must include the basic variable's scaled coefficient (3) in
    // the row GCD; otherwise gcd_test_tableau() falsely reports UNSAT because it
    // only sees the non-basic coefficient 5.
    let three_x = terms.mk_mul(vec![three, x]);
    let five_y = terms.mk_mul(vec![five, y]);
    let lhs = terms.mk_add(vec![three_x, five_y]);
    let eq = terms.mk_eq(lhs, seven);

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(eq, true);

    assert!(
        matches!(solver.lra.check(), TheoryResult::Sat),
        "LP relaxation for 3x + 5y = 7 should be feasible"
    );

    let rows = solver.lra.get_fractional_int_rows(&solver.integer_vars);
    assert!(
        !rows.is_empty(),
        "expected a fractional integer tableau row before running gcd_test_tableau()"
    );

    assert!(
        solver.gcd_test_tableau().is_none(),
        "3x + 5y = 7 has integer solutions, so gcd_test_tableau() must not report UNSAT; fractional rows: {rows:?}"
    );

    let result = solver.check();
    assert!(
        !matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "solver-level check must preserve satisfiability for 3x + 5y = 7. Got: {result:?}"
    );
}

#[test]
fn tableau_gcd_detects_true_divisibility_conflict() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let four = terms.mk_int(BigInt::from(4));
    let six = terms.mk_int(BigInt::from(6));
    let three = terms.mk_int(BigInt::from(3));

    // 4*x + 6*y = 3 has no integer solutions because gcd(4, 6) = 2 does not
    // divide 3. This reaches the same tableau path as the coprime regression
    // above, but should still produce a conflict after the #5648 fix.
    let four_x = terms.mk_mul(vec![four, x]);
    let six_y = terms.mk_mul(vec![six, y]);
    let lhs = terms.mk_add(vec![four_x, six_y]);
    let eq = terms.mk_eq(lhs, three);

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(eq, true);

    assert!(
        matches!(solver.lra.check(), TheoryResult::Sat),
        "LP relaxation for 4x + 6y = 3 should be feasible before integer recovery"
    );

    let rows = solver.lra.get_fractional_int_rows(&solver.integer_vars);
    assert!(
        !rows.is_empty(),
        "expected a fractional integer tableau row before running gcd_test_tableau()"
    );

    assert!(
        solver.gcd_test_tableau().is_some(),
        "4x + 6y = 3 should trigger a tableau GCD conflict; fractional rows: {rows:?}"
    );
}

#[test]
fn tableau_gcd_conflict_literals_only_include_participating_bound_reasons() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let z = terms.mk_var("z", Sort::Int);
    let zero = terms.mk_int(BigInt::zero());
    let one = terms.mk_int(BigInt::one());

    let x_ge_0 = terms.mk_ge(x, zero);
    let x_le_1 = terms.mk_le(x, one);
    let y_ge_0 = terms.mk_ge(y, zero);
    let z_ge_0 = terms.mk_ge(z, zero);

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(x_ge_0, true);
    solver.assert_literal(x_le_1, true);
    solver.assert_literal(y_ge_0, true);
    solver.assert_literal(z_ge_0, true);

    assert!(matches!(solver.lra.check(), TheoryResult::Sat));

    let x_var = solver.lra.ensure_var_registered(x);
    let y_var = solver.lra.ensure_var_registered(y);
    let row = GcdRowInfo {
        basic_var: x_var,
        basic_term: Some(x),
        coeffs: vec![(y_var, BigRational::from_integer(BigInt::from(2)))],
        constant: BigRational::one(),
        lower_bound: None,
        upper_bound: None,
        is_fixed: false,
        is_bounded: false,
    };

    let conflict = solver.collect_tableau_gcd_conflict_literals(&row);

    assert!(
        conflict.contains(&TheoryLit::new(x_ge_0, true)),
        "conflict should include x>=0 bound reason: {conflict:?}"
    );
    assert!(
        conflict.contains(&TheoryLit::new(x_le_1, true)),
        "conflict should include x<=1 bound reason: {conflict:?}"
    );
    assert!(
        conflict.contains(&TheoryLit::new(y_ge_0, true)),
        "conflict should include y>=0 bound reason: {conflict:?}"
    );
    assert!(
        !conflict.contains(&TheoryLit::new(z_ge_0, true)),
        "conflict should exclude unrelated z>=0 literal: {conflict:?}"
    );
}

#[test]
fn tableau_gcd_conflict_literals_fallback_to_asserted_when_no_row_reasons() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let z = terms.mk_var("z", Sort::Int);
    let zero = terms.mk_int(BigInt::zero());

    let z_ge_0 = terms.mk_ge(z, zero);

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(z_ge_0, true);
    let x_var = solver.lra.ensure_var_registered(x);
    let row = GcdRowInfo {
        basic_var: x_var,
        basic_term: Some(x),
        coeffs: Vec::new(),
        constant: BigRational::zero(),
        lower_bound: None,
        upper_bound: None,
        is_fixed: false,
        is_bounded: false,
    };

    let conflict = solver.collect_tableau_gcd_conflict_literals(&row);

    assert_eq!(
        conflict,
        vec![TheoryLit::new(z_ge_0, true)],
        "fallback should return asserted literals when row reasons are unavailable"
    );
}

#[test]
fn update_gcd_and_least_coeff_marks_tied_bounded_candidate() {
    let mut gcds = BigInt::zero();
    let mut least_coeff = BigInt::zero();
    let mut least_coeff_is_bounded = false;

    LiaSolver::update_gcd_and_least_coeff(
        &BigInt::from(2),
        false,
        &mut gcds,
        &mut least_coeff,
        &mut least_coeff_is_bounded,
    );
    LiaSolver::update_gcd_and_least_coeff(
        &BigInt::from(2),
        true,
        &mut gcds,
        &mut least_coeff,
        &mut least_coeff_is_bounded,
    );

    assert_eq!(gcds, BigInt::from(2));
    assert_eq!(least_coeff, BigInt::from(2));
    assert!(
        least_coeff_is_bounded,
        "a bounded tie for the least coefficient should enable extended GCD checks"
    );
}

#[test]
fn update_gcd_and_least_coeff_preserves_bounded_tie_after_unbounded() {
    let mut gcds = BigInt::zero();
    let mut least_coeff = BigInt::zero();
    let mut least_coeff_is_bounded = false;

    LiaSolver::update_gcd_and_least_coeff(
        &BigInt::from(2),
        true,
        &mut gcds,
        &mut least_coeff,
        &mut least_coeff_is_bounded,
    );
    LiaSolver::update_gcd_and_least_coeff(
        &BigInt::from(2),
        false,
        &mut gcds,
        &mut least_coeff,
        &mut least_coeff_is_bounded,
    );

    assert_eq!(gcds, BigInt::from(2));
    assert_eq!(least_coeff, BigInt::from(2));
    assert!(
        least_coeff_is_bounded,
        "an unbounded tie must not clear bounded status selected earlier"
    );
}

/// Verify positive_mod returns canonical non-negative representatives.
#[test]
fn positive_mod_returns_nonnegative_canonical_residue() {
    assert_eq!(
        positive_mod(&BigInt::from(5), &BigInt::from(3)),
        BigInt::from(2)
    );
    assert_eq!(
        positive_mod(&BigInt::from(-1), &BigInt::from(6)),
        BigInt::from(5)
    );
    assert_eq!(
        positive_mod(&BigInt::from(0), &BigInt::from(4)),
        BigInt::from(0)
    );
    assert_eq!(
        positive_mod(&BigInt::from(12), &BigInt::from(4)),
        BigInt::from(0)
    );
    assert_eq!(
        positive_mod(&BigInt::from(-7), &BigInt::from(3)),
        BigInt::from(2)
    );
}

/// Verify that the accumulative GCD/CRT test detects cross-row modular conflict.
///
/// System: x + 6*y = 5 and x + 4*z = 2.
/// Row 1 implies x ≡ 5 (mod 6) (odd), Row 2 implies x ≡ 2 (mod 4) (even).
/// gcd(6,4) = 2, and 5 mod 2 = 1 ≠ 0 = 2 mod 2 → UNSAT.
///
/// The per-row GCD test passes (gcd of each row's coefficients is 1),
/// but the cross-row CRT test detects the incompatibility.
#[test]
fn accumulative_gcd_crt_detects_cross_row_modular_conflict() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let z = terms.mk_var("z", Sort::Int);

    let six = terms.mk_int(BigInt::from(6));
    let four = terms.mk_int(BigInt::from(4));
    let five = terms.mk_int(BigInt::from(5));
    let two = terms.mk_int(BigInt::from(2));

    // x + 6*y = 5
    let six_y = terms.mk_mul(vec![six, y]);
    let x_plus_6y = terms.mk_add(vec![x, six_y]);
    let eq1 = terms.mk_eq(x_plus_6y, five);

    // x + 4*z = 2
    let four_z = terms.mk_mul(vec![four, z]);
    let x_plus_4z = terms.mk_add(vec![x, four_z]);
    let eq2 = terms.mk_eq(x_plus_4z, two);

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(eq1, true);
    solver.assert_literal(eq2, true);

    let result = solver.check();
    assert!(
        matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "cross-row CRT incompatibility (x odd from row 1, x even from row 2) should be UNSAT, got {result:?}",
    );
}

/// Verify that accumulative GCD/CRT conflicts contain unique literals.
///
/// Re-asserting equalities can duplicate row reasons. The merge path in
/// `gcd_accumulative_test` must deduplicate before constructing conflicts.
#[test]
fn accumulative_gcd_crt_conflict_literals_are_deduplicated() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let z = terms.mk_var("z", Sort::Int);

    let six = terms.mk_int(BigInt::from(6));
    let four = terms.mk_int(BigInt::from(4));
    let five = terms.mk_int(BigInt::from(5));
    let two = terms.mk_int(BigInt::from(2));

    // x + 6*y = 5
    let six_y = terms.mk_mul(vec![six, y]);
    let x_plus_6y = terms.mk_add(vec![x, six_y]);
    let eq1 = terms.mk_eq(x_plus_6y, five);

    // x + 4*z = 2
    let four_z = terms.mk_mul(vec![four, z]);
    let x_plus_4z = terms.mk_add(vec![x, four_z]);
    let eq2 = terms.mk_eq(x_plus_4z, two);

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(eq1, true);
    solver.assert_literal(eq1, true);
    solver.assert_literal(eq2, true);
    solver.assert_literal(eq2, true);

    let result = solver.check();
    assert!(
        matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "expected UNSAT from cross-row CRT conflict, got {result:?}"
    );
    let conflict_literals = match result {
        TheoryResult::Unsat(lits) => lits,
        TheoryResult::UnsatWithFarkas(conflict) => conflict.literals,
        _ => Vec::new(),
    };
    let unique: HashSet<TheoryLit> = conflict_literals.iter().copied().collect();
    assert_eq!(
        unique.len(),
        conflict_literals.len(),
        "expected deduplicated conflict literals, got {conflict_literals:?}"
    );
}

/// Verify that compatible modular constraints do NOT produce false conflicts.
///
/// System: x + 6*y = 12 and x + 4*z = 8.
/// Row 1 implies x ≡ 0 (mod 6), Row 2 implies x ≡ 0 (mod 4).
/// gcd(6,4) = 2, 0 mod 2 == 0 mod 2 → compatible.
/// CRT merge: x ≡ 0 (mod 12).
/// This system is SAT (e.g., x=0, y=2, z=2).
#[test]
fn accumulative_gcd_crt_no_false_conflict_on_compatible_constraints() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let z = terms.mk_var("z", Sort::Int);

    let six = terms.mk_int(BigInt::from(6));
    let four = terms.mk_int(BigInt::from(4));
    let twelve = terms.mk_int(BigInt::from(12));
    let eight = terms.mk_int(BigInt::from(8));

    // x + 6*y = 12
    let six_y = terms.mk_mul(vec![six, y]);
    let x_plus_6y = terms.mk_add(vec![x, six_y]);
    let eq1 = terms.mk_eq(x_plus_6y, twelve);

    // x + 4*z = 8
    let four_z = terms.mk_mul(vec![four, z]);
    let x_plus_4z = terms.mk_add(vec![x, four_z]);
    let eq2 = terms.mk_eq(x_plus_4z, eight);

    let mut solver = LiaSolver::new(&terms);
    solver.assert_literal(eq1, true);
    solver.assert_literal(eq2, true);

    let result = solver.check();
    // The system is SAT (x=0, y=2, z=2) — the accumulative test must NOT
    // produce a false conflict from compatible modular constraints.
    assert!(
        !matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "compatible CRT constraints should not produce false conflict, got {result:?}",
    );
}
