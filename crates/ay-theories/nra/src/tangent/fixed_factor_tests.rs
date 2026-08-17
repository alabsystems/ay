// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::term::TermStore;
use ay_core::{Sort, TheoryResult, TheorySolver};
use num_traits::{FromPrimitive, One, Zero};

fn rat(n: i64) -> BigRational {
    BigRational::from_i64(n).unwrap()
}

#[test]
fn missing_free_variable_is_a_typed_decline() {
    assert_eq!(
        require_free_variable(None),
        Err(FixedFactorLinearizationError::MissingFreeVariable)
    );
}

#[test]
fn tentative_scope_cannot_seed_fixed_factor_authority() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let xy = terms.mk_mul(vec![x, y]);
    let zero = terms.mk_rational(BigRational::zero());
    let xy_ge_zero = terms.mk_ge(xy, zero);

    let mut solver = NraSolver::new(&terms);
    solver.assert_literal(xy_ge_zero, true);
    let _ = solver.lra.check();
    solver.lra.push();
    solver.tentative_depth += 1;
    let x_var = solver.lra.ensure_var_registered(x);
    for is_lower in [true, false] {
        solver.lra.add_gomory_cut(
            &GomoryCut {
                coeffs: vec![(x_var, BigRational::one())],
                bound: rat(7),
                is_lower,
                reasons: Vec::new(),
                source_term: None,
            },
            x,
        );
    }
    let _ = solver.lra.check();
    assert_eq!(solver.var_value(x), Some(rat(7)));
    solver.fixed_lin_emitted.insert(xy);

    solver.refresh_fixed_factor_values();
    assert!(solver.fixed_factor_values.is_empty());
    assert!(solver.fixed_lin_emitted.is_empty());
    solver.undo_tentative_patch();
}

#[test]
fn later_matching_upper_bound_still_authenticates_pin() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let one = terms.mk_rational(rat(1));
    let two = terms.mk_rational(rat(2));
    let lower = terms.mk_le(one, x);
    let loose_upper = terms.mk_le(x, two);
    let exact_upper = terms.mk_le(x, one);

    let mut solver = NraSolver::new(&terms);
    solver.assert_literal(lower, true);
    solver.assert_literal(loose_upper, true);
    solver.assert_literal(exact_upper, true);
    let pins = solver.asserted_pins();
    assert!(pins
        .iter()
        .any(|(var, value)| *var == x && *value == rat(1)));
}

#[test]
fn reset_clears_fixed_factor_authority() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let mut solver = NraSolver::new(&terms);
    solver.fixed_factor_values.insert(x, rat(3));
    solver.fixed_lin_emitted.insert(x);

    solver.reset();
    assert!(solver.fixed_factor_values.is_empty());
    assert!(solver.fixed_lin_emitted.is_empty());
}

/// The shape the fix exists for: a product of a case-split multiplier and a
/// COMPLETELY UNBOUNDED coefficient. McCormick declines outright here (it has no
/// box on `y`), so before the fixed-factor identity the only lemma available was
/// a model-point tangent plane and the check loop returned `unknown`. With `x`
/// pinned by an asserted equality, `x*y = 3*y` is exact and LRA decides it.
#[test]
fn test_fixed_factor_linearizes_unbounded_partner() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let xy = terms.mk_mul(vec![x, y]);
    let three = terms.mk_rational(rat(3));
    let twelve = terms.mk_rational(rat(12));
    let x_eq_3 = terms.mk_eq(x, three);
    let xy_eq_12 = terms.mk_eq(xy, twelve);

    let mut solver = NraSolver::new(&terms);
    solver.assert_literal(x_eq_3, true);
    solver.assert_literal(xy_eq_12, true);
    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "x = 3 ∧ x*y = 12 is SAT (y = 4) with y unbounded, got {result:?}"
    );

    // The pin itself: taken from the assertion-only bound state, it must see
    // `x` (asserted equality) and must NOT see `y` (unbounded).
    solver.undo_tentative_patch();
    let _ = solver.lra.check();
    solver.refresh_fixed_factor_values();
    assert_eq!(
        solver.fixed_factor_values.get(&x),
        Some(&rat(3)),
        "x must be pinned to 3 by the asserted equality"
    );
    assert!(
        !solver.fixed_factor_values.contains_key(&y),
        "y is unbounded and must not be pinned"
    );

    // And the pin must yield the exact two-sided identity `aux - 3*y = 0`.
    let mut vars = vec![x, y];
    vars.sort_by_key(|t| t.0);
    let mon = solver
        .monomials
        .get(&vars)
        .expect("x*y must be registered")
        .clone();
    assert_eq!(
        solver.add_fixed_factor_linearization(&mon),
        2,
        "one pinned factor and one free factor is an exact linear equality"
    );
}

/// A pinned ZERO factor annihilates the product no matter how many free factors
/// remain — the one case that stays exact at arbitrary degree.
#[test]
fn test_fixed_factor_zero_annihilates_higher_degree() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let z = terms.mk_var("z", Sort::Real);
    let xyz = terms.mk_mul(vec![x, y, z]);
    let zero = terms.mk_rational(BigRational::zero());
    let one = terms.mk_rational(rat(1));
    let x_eq_0 = terms.mk_eq(x, zero);
    // x*y*z >= 1 is unsatisfiable once x is pinned to 0.
    let ge = terms.mk_ge(xyz, one);

    let mut solver = NraSolver::new(&terms);
    solver.assert_literal(x_eq_0, true);
    solver.assert_literal(ge, true);
    let result = solver.check();
    assert!(
        matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "x = 0 ∧ x*y*z >= 1 is UNSAT for unbounded y, z, got {result:?}"
    );
}

/// Two free OCCURRENCES are still nonlinear: the identity must DECLINE rather
/// than emit `aux = c*y` for `aux = c*y*y`.
#[test]
fn test_fixed_factor_declines_repeated_free_factor() {
    let mut terms = TermStore::new();
    let c = terms.mk_var("c", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let cyy = terms.mk_mul(vec![c, y, y]);
    let two = terms.mk_rational(rat(2));
    let four = terms.mk_rational(rat(4));
    let c_eq_2 = terms.mk_eq(c, two);
    let prod_eq_4 = terms.mk_eq(cyy, four);

    let mut solver = NraSolver::new(&terms);
    solver.assert_literal(c_eq_2, true);
    solver.assert_literal(prod_eq_4, true);
    // 2*y^2 = 4 has the irrational solutions y = ±√2. Whatever verdict the
    // other phases reach, it must never be UNSAT — that is the wrong answer a
    // bogus `aux = 2*y` identity would produce.
    let result = solver.check();
    assert!(
        !matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "c = 2 ∧ c*y*y = 4 is SAT (y = ±√2); a linear identity must not be \
         emitted for a repeated free factor, got {result:?}"
    );
    let mut vars = vec![c, y, y];
    vars.sort_by_key(|t| t.0);
    let mon = solver
        .monomials
        .get(&vars)
        .expect("c*y*y must be registered")
        .clone();
    solver.fixed_lin_emitted.clear();
    assert_eq!(
        solver.add_fixed_factor_linearization(&mon),
        0,
        "a monomial with two free occurrences has no exact linearization"
    );
}

/// The pin snapshot must be taken from the ASSERTION-ONLY bound state: a
/// variable that is merely bounded, not pinned, must never be treated as fixed.
#[test]
fn test_fixed_factor_ignores_non_pinning_bounds() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let xy = terms.mk_mul(vec![x, y]);
    let one = terms.mk_rational(rat(1));
    let five = terms.mk_rational(rat(5));
    let zero = terms.mk_rational(BigRational::zero());
    // 1 <= x <= 5: bounded but NOT pinned.
    let lo = terms.mk_le(one, x);
    let hi = terms.mk_le(x, five);
    let ge = terms.mk_ge(xy, zero);

    let mut solver = NraSolver::new(&terms);
    solver.assert_literal(lo, true);
    solver.assert_literal(hi, true);
    solver.assert_literal(ge, true);
    let _ = solver.check();
    solver.undo_tentative_patch();
    let _ = solver.lra.check();
    solver.refresh_fixed_factor_values();
    assert!(
        !solver.fixed_factor_values.contains_key(&x),
        "1 <= x <= 5 pins nothing; x must not appear in the pin map"
    );
    assert!(
        !solver.fixed_factor_values.contains_key(&y),
        "y is entirely unconstrained; it must not appear in the pin map"
    );
    let mut vars = vec![x, y];
    vars.sort_by_key(|t| t.0);
    let mon = solver
        .monomials
        .get(&vars)
        .expect("x*y must be registered")
        .clone();
    assert_eq!(
        solver.add_fixed_factor_linearization(&mon),
        0,
        "no pinned factor means no exact linearization"
    );
}
