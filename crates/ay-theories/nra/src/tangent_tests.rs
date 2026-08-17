// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::term::TermStore;
use ay_core::{Sort, TheoryResult, TheorySolver};
use num_traits::FromPrimitive;

fn rat(n: i64) -> BigRational {
    BigRational::from_i64(n).unwrap()
}

#[test]
fn test_mccormick_bounds_at_corners() {
    // For m = x*y with x in [2,3], y in [2,3]:
    // Lower 1 at (2,2): m >= 2*y + 2*x - 4 -> at (3,3): m >= 6+6-4 = 8
    // Lower 2 at (3,3): m >= 3*y + 3*x - 9 -> at (2,2): m >= 6+6-9 = 3
    // Upper 1 at (3,2): m <= 3*y + 2*x - 6 -> at (3,3): m <= 9+6-6 = 9
    // Upper 2 at (2,3): m <= 2*y + 3*x - 6 -> at (3,3): m <= 6+9-6 = 9
    let xl = rat(2);
    let xu = rat(3);
    let yl = rat(2);
    let yu = rat(3);

    // Upper bound 1 at (3,3): 3*3 + 2*3 - 3*2 = 9+6-6 = 9
    let ub1 = &xu * &yu + &yl * &xu - &xu * &yl;
    assert_eq!(ub1, rat(9));

    // Upper bound 2 at (3,3): 2*3 + 3*3 - 2*3 = 6+9-6 = 9
    let ub2 = &xl * &yu + &yu * &xu - &xl * &yu;
    assert_eq!(ub2, rat(9));

    // At (2,2): upper bound 1 = 3*2 + 2*2 - 3*2 = 6+4-6 = 4 = 2*2 (exact at corner)
    let ub1_at_22 = &xu * &yl + &yl * &xl - &xu * &yl;
    assert_eq!(ub1_at_22, rat(4));
}

#[test]
fn test_tangent_hyperplane_ternary() {
    // For m = x*y*z at (2, 3, 5): product = 30
    // Partial derivatives: d(xyz)/dx = yz = 15, d/dy = xz = 10, d/dz = xy = 6
    // T = 15*x + 10*y + 6*z - 2*30 = 15x + 10y + 6z - 60
    let vals = [rat(2), rat(3), rat(5)];
    let product = rat(30);

    // General formula bound: -(3-1)*30 = -60
    let bound = -(rat(2) * &product);
    assert_eq!(bound, rat(-60));

    // Coefficients
    let coeff_x = -(&product / &vals[0]); // -30/2 = -15
    let coeff_y = -(&product / &vals[1]); // -30/3 = -10
    let coeff_z = -(&product / &vals[2]); // -30/5 = -6
    assert_eq!(coeff_x, rat(-15));
    assert_eq!(coeff_y, rat(-10));
    assert_eq!(coeff_z, rat(-6));
}

// ============================================================================
// NRA Theory-Level Integration Tests
// ============================================================================

/// Fresh NRA solver should not be in conflict.
#[test]
fn test_nra_solver_creation_no_conflict() {
    let terms = TermStore::new();
    let mut solver = NraSolver::new(&terms);
    let result = solver.check();
    assert!(
        !matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "fresh NRA solver must not be in conflict, got {result:?}"
    );
}

/// x*y >= 0 should register the nonlinear monomial.
#[test]
fn test_nra_nonlinear_term_detection() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let xy = terms.mk_mul(vec![x, y]);
    let zero = terms.mk_rational(BigRational::zero());
    let ge = terms.mk_ge(xy, zero);

    let mut solver = NraSolver::new(&terms);
    solver.assert_literal(ge, true);

    let mut sorted = vec![x, y];
    sorted.sort_by_key(|t| t.0);
    assert!(
        solver.monomials.contains_key(&sorted),
        "x*y should be registered as a monomial"
    );
}

/// Linear term (2*x) should NOT be registered as nonlinear.
#[test]
fn test_nra_linear_term_not_registered() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let two = terms.mk_rational(rat(2));
    let two_x = terms.mk_mul(vec![two, x]);
    let zero = terms.mk_rational(BigRational::zero());
    let ge = terms.mk_ge(two_x, zero);

    let mut solver = NraSolver::new(&terms);
    solver.assert_literal(ge, true);
    assert!(
        solver.monomials.is_empty(),
        "2*x is linear, should not be registered as nonlinear"
    );
}

/// x*x (square term) should be detected.
#[test]
fn test_nra_square_term_detection() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let xx = terms.mk_mul(vec![x, x]);
    let zero = terms.mk_rational(BigRational::zero());
    let ge = terms.mk_ge(xx, zero);

    let mut solver = NraSolver::new(&terms);
    solver.assert_literal(ge, true);
    let vars = vec![x, x];
    assert!(
        solver.monomials.contains_key(&vars),
        "x*x should be registered as a monomial"
    );
}

/// Push/pop should restore asserted atoms.
#[test]
fn test_nra_push_pop_assertions() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let xy = terms.mk_mul(vec![x, y]);
    let zero = terms.mk_rational(BigRational::zero());
    let ge = terms.mk_ge(xy, zero);
    let le = terms.mk_le(xy, zero);

    let mut solver = NraSolver::new(&terms);
    solver.assert_literal(ge, true);
    assert_eq!(solver.asserted.len(), 1);

    solver.push();
    solver.assert_literal(le, true);
    assert_eq!(solver.asserted.len(), 2);

    solver.pop();
    assert_eq!(solver.asserted.len(), 1);
}

/// Division purification: (/ x y) with symbolic y should be tracked.
#[test]
fn test_nra_division_purification_tracking() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let x_div_y = terms.mk_div(x, y);
    let zero = terms.mk_rational(BigRational::zero());
    let ge = terms.mk_ge(x_div_y, zero);

    let mut solver = NraSolver::new(&terms);
    solver.assert_literal(ge, true);
    assert!(
        !solver.div_purifications.is_empty(),
        "(/ x y) with symbolic denominator should be tracked for refinement"
    );
}

/// Division by a constant should NOT be tracked as a purification.
#[test]
fn test_nra_division_by_constant_not_tracked() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let two = terms.mk_rational(rat(2));
    let x_div_2 = terms.mk_div(x, two);
    let zero = terms.mk_rational(BigRational::zero());
    let ge = terms.mk_ge(x_div_2, zero);

    let mut solver = NraSolver::new(&terms);
    solver.assert_literal(ge, true);
    assert!(
        solver.div_purifications.is_empty(),
        "(/ x 2) should NOT create a division purification (constant denominator)"
    );
}

/// Push/pop should scope division purifications.
#[test]
fn test_nra_push_pop_division_purifications() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let z = terms.mk_var("z", Sort::Real);
    let x_div_y = terms.mk_div(x, y);
    let x_div_z = terms.mk_div(x, z);
    let zero = terms.mk_rational(BigRational::zero());
    let ge1 = terms.mk_ge(x_div_y, zero);
    let ge2 = terms.mk_ge(x_div_z, zero);

    let mut solver = NraSolver::new(&terms);
    solver.assert_literal(ge1, true);
    let count_0 = solver.div_purifications.len();

    solver.push();
    solver.assert_literal(ge2, true);
    assert!(
        solver.div_purifications.len() > count_0,
        "scoped division should add purification"
    );

    solver.pop();
    assert_eq!(
        solver.div_purifications.len(),
        count_0,
        "pop should restore division purification count"
    );
}

/// Push/pop should restore sign constraints.
#[test]
fn test_nra_push_pop_sign_constraints() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let xy = terms.mk_mul(vec![x, y]);
    let zero = terms.mk_rational(BigRational::zero());
    let xy_ge = terms.mk_ge(xy, zero);
    let x_gt = terms.mk_gt(x, zero);
    let y_gt = terms.mk_gt(y, zero);

    let mut solver = NraSolver::new(&terms);
    solver.assert_literal(xy_ge, true);
    solver.assert_literal(x_gt, true);
    let sign_count_0 = solver.var_sign_constraints.len();

    solver.push();
    solver.assert_literal(y_gt, true);
    assert!(
        solver.var_sign_constraints.len() >= sign_count_0,
        "deeper scope should have more sign constraints"
    );

    solver.pop();
    assert_eq!(
        solver.var_sign_constraints.len(),
        sign_count_0,
        "pop should restore sign constraint count"
    );
}

/// Reset should clear all state.
#[test]
fn test_nra_reset_clears_state() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let xy = terms.mk_mul(vec![x, y]);
    let zero = terms.mk_rational(BigRational::zero());
    let ge = terms.mk_ge(xy, zero);

    let mut solver = NraSolver::new(&terms);
    solver.assert_literal(ge, true);
    assert!(!solver.monomials.is_empty());

    solver.reset();
    assert!(solver.monomials.is_empty());
    assert!(solver.asserted.is_empty());
    assert!(solver.sign_constraints.is_empty());
    assert!(solver.div_purifications.is_empty());
}

/// Ternary monomial x*y*z should be detected from nested multiplications.
#[test]
fn test_nra_ternary_monomial_from_nested_mul() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let z = terms.mk_var("z", Sort::Real);
    // (x * y * z) as a single n-ary multiplication
    let xyz = terms.mk_mul(vec![x, y, z]);
    let zero = terms.mk_rational(BigRational::zero());
    let ge = terms.mk_ge(xyz, zero);

    let mut solver = NraSolver::new(&terms);
    solver.assert_literal(ge, true);

    // Should register a 3-variable monomial
    let mut sorted = vec![x, y, z];
    sorted.sort_by_key(|t| t.0);
    assert!(
        solver.monomials.contains_key(&sorted),
        "ternary monomial x*y*z should be registered"
    );
}

/// Statistics should be collected after check.
#[test]
fn test_nra_statistics_collected() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let xy = terms.mk_mul(vec![x, y]);
    let zero = terms.mk_rational(BigRational::zero());
    let ge = terms.mk_ge(xy, zero);

    let mut solver = NraSolver::new(&terms);
    solver.assert_literal(ge, true);
    let _ = solver.check();

    let stats = solver.collect_statistics();
    let stat_names: Vec<&str> = stats.iter().map(|(name, _)| *name).collect();
    assert!(
        stat_names.contains(&"nra_checks"),
        "should track check count"
    );
    // At least one check was performed
    let check_count = stats.iter().find(|(n, _)| *n == "nra_checks").unwrap().1;
    assert!(check_count >= 1, "should have performed at least one check");
}

/// McCormick at zero factors must produce finite bounds.
#[test]
fn test_mccormick_zero_bounds() {
    // McCormick with one bound at zero: xL=0, yL=0
    let xl = rat(0);
    let xu = rat(1);
    let yl = rat(0);
    let yu = rat(1);

    // Lower bound 1 at (0,0): m >= 0*y + 0*x - 0 = 0
    let lb1 = &xl * &yl + &yl * &xl - &xl * &yl;
    assert_eq!(lb1, rat(0));

    // Lower bound 2 at (1,1): m >= 1*y + 1*x - 1
    let lb2_at_half = &xu * &BigRational::new(1.into(), 2.into())
        + &yu * &BigRational::new(1.into(), 2.into())
        - &xu * &yu;
    // At (0.5, 0.5): T = 1*0.5 + 1*0.5 - 1 = 0, actual = 0.25
    assert_eq!(lb2_at_half, rat(0));
}

/// Zero-valued factors must handle the degenerate zero partial derivative.
#[test]
fn test_tangent_hyperplane_with_zero_factor() {
    let vals = [rat(0), rat(3)];
    let product = rat(0); // 0 * 3 = 0

    // Coefficient for first var (value=0): full_product / 0 is undefined
    // The implementation should skip this term (continue).
    // Coefficient for second var (value=3): 0 / 3 = 0
    let coeff_y = -(&product / &vals[1]);
    assert_eq!(coeff_y, rat(0));
}

/// McCormick with negative bounds: x in [-3,-1], y in [-3,-1]
#[test]
fn test_mccormick_negative_bounds() {
    let xl = rat(-3);
    let _xu = rat(-1);
    let yl = rat(-3);
    let _yu = rat(-1);

    // Lower bound 1 at (xL,yL) = (-3,-3): m >= -3*y + (-3)*x - 9
    // At (-2,-2): T = -3*(-2) + (-3)*(-2) - 9 = 6+6-9 = 3
    // Actual: (-2)*(-2) = 4 >= 3
    let lb1_at_m2 = &xl * &rat(-2) + &yl * &rat(-2) - &xl * &yl;
    assert_eq!(lb1_at_m2, rat(3));
    assert!(
        lb1_at_m2 <= rat(4),
        "McCormick lower bound should be <= actual value"
    );
}

/// Nested nonlinear inside addition: x*y + z >= 0
#[test]
fn test_nra_nested_nonlinear_in_addition() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let z = terms.mk_var("z", Sort::Real);
    let xy = terms.mk_mul(vec![x, y]);
    let xy_plus_z = terms.mk_add(vec![xy, z]);
    let zero = terms.mk_rational(BigRational::zero());
    let ge = terms.mk_ge(xy_plus_z, zero);

    let mut solver = NraSolver::new(&terms);
    solver.assert_literal(ge, true);

    let mut sorted = vec![x, y];
    sorted.sort_by_key(|t| t.0);
    assert!(
        solver.monomials.contains_key(&sorted),
        "x*y nested in addition should still be detected"
    );
}

/// Multiple distinct monomials should all be registered.
#[test]
fn test_nra_multiple_monomials() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let z = terms.mk_var("z", Sort::Real);
    let xy = terms.mk_mul(vec![x, y]);
    let xz = terms.mk_mul(vec![x, z]);
    let zero = terms.mk_rational(BigRational::zero());
    let ge1 = terms.mk_ge(xy, zero);
    let ge2 = terms.mk_ge(xz, zero);

    let mut solver = NraSolver::new(&terms);
    solver.assert_literal(ge1, true);
    solver.assert_literal(ge2, true);

    assert_eq!(
        solver.monomials.len(),
        2,
        "two distinct monomials x*y and x*z should both be registered"
    );
}

/// Even power nonneg: tangent test that x^2 >= 0 is sound.
/// Mathematically, for m = x*x, the even-power lemma m >= 0
/// is always valid regardless of x.
#[test]
fn test_even_power_nonneg_mathematical_property() {
    // For any value of x, x^2 >= 0
    for x_val in &[rat(-100), rat(-1), rat(0), rat(1), rat(100)] {
        let product = x_val * x_val;
        assert!(
            product >= BigRational::zero(),
            "x^2 must be >= 0 for x = {x_val}"
        );
    }
}

/// Tangent hyperplane: single variable repeated (x*x) at point (a):
/// T(x) = a*x + a*x - a^2 = 2a*x - a^2
#[test]
fn test_tangent_plane_square_monomial() {
    // At point a=3: T(x) = 3*x + 3*x - 9 = 6x - 9
    let a = rat(3);
    let tangent_offset = &a * &a;
    // T evaluated at x=3: 6*3 - 9 = 9 = 3^2 (exact at tangent point)
    let tangent_at_3 = &a * &rat(3) + &a * &rat(3);
    let t_at_3 = tangent_at_3 - &tangent_offset;
    assert_eq!(t_at_3, rat(9));
    // T evaluated at x=0: 0 - 9 = -9 (underestimate, actual 0)
    let tangent_at_0 = &a * &rat(0) + &a * &rat(0);
    let t_at_0 = tangent_at_0 - tangent_offset;
    assert_eq!(t_at_0, rat(-9));
    assert!(t_at_0 <= rat(0), "tangent plane underestimates at x=0");
}

/// McCormick bounds should be exact at corners of the box.
/// For m = x*y with x in [1, 4], y in [2, 5]:
/// At corner (1,2): actual = 2, lower = xL*y + yL*x - xL*yL = 1*2 + 2*1 - 2 = 2
#[test]
fn test_mccormick_exact_at_corner() {
    let xl = rat(1);
    let xu = rat(4);
    let yl = rat(2);
    let _yu = rat(5);

    // Lower bound 1 at corner (xL, yL) = (1, 2):
    // m >= xL*y + yL*x - xL*yL
    // At (1, 2): 1*2 + 2*1 - 1*2 = 2 (exact since actual = 1*2 = 2)
    let lb1_at_corner = &xl * &yl + &yl * &xl - &xl * &yl;
    assert_eq!(lb1_at_corner, rat(2));

    // Upper bound 1 at corner (xU, yL) = (4, 2):
    // m <= xU*y + yL*x - xU*yL
    // At (4, 2): 4*2 + 2*4 - 4*2 = 8 (exact since actual = 4*2 = 8)
    let ub1_at_corner = &xu * &yl + &yl * &xu - &xu * &yl;
    assert_eq!(ub1_at_corner, rat(8));
}

/// McCormick with unit interval: x in [0,1], y in [0,1].
/// At midpoint (0.5, 0.5): actual = 0.25.
/// Lower bound 1 at (0,0): m >= 0 (exact at corner).
/// Lower bound 2 at (1,1): m >= y + x - 1.
/// At (0.5, 0.5): T = 0.5 + 0.5 - 1 = 0 <= 0.25 (valid lower bound).
#[test]
fn test_mccormick_unit_interval() {
    let half = BigRational::new(1.into(), 2.into());
    let one = rat(1);
    // Lower bound 2 at (1,1) evaluated at (0.5, 0.5):
    let linear = &one * &half + &one * &half;
    let unit_product = &one * &one;
    let lb2 = linear - unit_product;
    assert_eq!(lb2, rat(0));
    assert!(
        lb2 <= BigRational::new(1.into(), 4.into()),
        "McCormick lower bound should be <= actual 0.25"
    );
}

/// Tangent hyperplane with 4 factors at (1, 1, 1, 1).
/// Product = 1. Each partial = 1. Bound = -(4-1)*1 = -3.
/// T = x1 + x2 + x3 + x4 - 3.
/// At (1,1,1,1): T = 4 - 3 = 1 = product (exact at tangent point).
#[test]
fn test_tangent_hyperplane_four_factors() {
    let vals = [rat(1), rat(1), rat(1), rat(1)];
    let product = rat(1);
    let n = 4i64;

    // Bound = -(n-1) * product = -3
    let bound = -(rat(n - 1) * &product);
    assert_eq!(bound, rat(-3));

    // Coefficients: each is -product/vi = -1
    for v in &vals {
        let coeff = -(&product / v);
        assert_eq!(coeff, rat(-1));
    }

    // Evaluate T at (1,1,1,1): sum(coeffs * vars) + m = 0
    // m + (-1)*1 + (-1)*1 + (-1)*1 + (-1)*1 >= -3
    // m - 4 >= -3 => m >= 1 (correct: 1*1*1*1 = 1)
}

/// McCormick with symmetric bounds: x in [-2, 2], y in [-2, 2].
/// Lower bound 1 at (-2, -2): m >= -2*y + (-2)*x - 4
/// At (0, 0): T = 0 + 0 - 4 = -4. Actual = 0. Valid lower bound.
#[test]
fn test_mccormick_symmetric_bounds() {
    let xl = rat(-2);
    let xu = rat(2);
    let yl = rat(-2);
    let _yu = rat(2);

    // Lower bound 1 at (xL, yL) = (-2, -2), evaluated at (0, 0):
    let lb_at_origin = &xl * &rat(0) + &yl * &rat(0) - &xl * &yl;
    assert_eq!(lb_at_origin, rat(-4));
    // Actual at (0,0) = 0 >= -4, so the bound is valid.

    // Upper bound 1 at (xU, yL) = (2, -2), evaluated at (0, 0):
    let ub_at_origin = &xu * &rat(0) + &yl * &rat(0) - &xu * &yl;
    assert_eq!(ub_at_origin, rat(4));
    // Actual at (0,0) = 0 <= 4, so the bound is valid.
}

/// even_power_nonneg_mathematical: x^4 >= 0 for all x
#[test]
fn test_even_power_fourth_nonneg() {
    for x_val in &[rat(-10), rat(-1), rat(0), rat(1), rat(10)] {
        let fourth = x_val * x_val * x_val * x_val;
        assert!(
            fourth >= BigRational::zero(),
            "x^4 must be >= 0 for x = {x_val}"
        );
    }
}

/// Collect nonlinear terms in subtraction: x*y - z >= 0
/// The x*y inside the subtraction should be detected.
#[test]
fn test_nra_nonlinear_in_subtraction() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let z = terms.mk_var("z", Sort::Real);
    let xy = terms.mk_mul(vec![x, y]);
    let diff = terms.mk_sub(vec![xy, z]);
    let zero = terms.mk_rational(BigRational::zero());
    let ge = terms.mk_ge(diff, zero);

    let mut solver = NraSolver::new(&terms);
    solver.assert_literal(ge, true);

    let mut sorted = vec![x, y];
    sorted.sort_by_key(|t| t.0);
    assert!(
        solver.monomials.contains_key(&sorted),
        "x*y nested in subtraction should still be detected"
    );
}

// ============================================================================
// Check loop helper tests (#8460)
// ============================================================================

/// has_inconsistent_monomials should return false when no monomials exist.
#[test]
fn test_nra_no_monomials_consistent() {
    let terms = TermStore::new();
    let solver = NraSolver::new(&terms);
    assert!(
        !solver.has_inconsistent_monomials(),
        "empty solver has no inconsistent monomials"
    );
}

/// has_inconsistent_divisions should return false when no divisions exist.
#[test]
fn test_nra_no_divisions_consistent() {
    let terms = TermStore::new();
    let solver = NraSolver::new(&terms);
    assert!(
        !solver.has_inconsistent_divisions(),
        "empty solver has no inconsistent divisions"
    );
}

/// undo_tentative_patch on a fresh solver (tentative_depth = 0) should
/// be a no-op and not panic.
#[test]
fn test_nra_undo_tentative_patch_fresh_solver() {
    let terms = TermStore::new();
    let mut solver = NraSolver::new(&terms);
    solver.undo_tentative_patch(); // Should not panic
    assert_eq!(solver.tentative_depth, 0);
}

/// Fresh NRA solver check should return Sat (no constraints).
#[test]
fn test_nra_fresh_check_sat() {
    let terms = TermStore::new();
    let mut solver = NraSolver::new(&terms);
    let result = solver.check();
    assert!(
        matches!(result, TheoryResult::Sat),
        "fresh solver with no assertions should return Sat"
    );
}

/// Asserting a simple linear constraint should be handled by
/// the LRA subsolver and return Sat.
#[test]
fn test_nra_linear_constraint_sat() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let zero = terms.mk_rational(BigRational::zero());
    let x_ge_0 = terms.mk_ge(x, zero);

    let mut solver = NraSolver::new(&terms);
    solver.assert_literal(x_ge_0, true);
    let result = solver.check();
    assert!(
        !matches!(result, TheoryResult::Unsat(_)),
        "x >= 0 should be satisfiable"
    );
}

/// Push/pop should preserve tentative_depth at 0.
#[test]
fn test_nra_push_pop_tentative_depth_preserved() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let xy = terms.mk_mul(vec![x, y]);
    let zero = terms.mk_rational(BigRational::zero());
    let ge = terms.mk_ge(xy, zero);

    let mut solver = NraSolver::new(&terms);
    assert_eq!(solver.tentative_depth, 0);
    solver.assert_literal(ge, true);

    solver.push();
    assert_eq!(solver.tentative_depth, 0);

    solver.pop();
    assert_eq!(solver.tentative_depth, 0);
}

/// check_count should increment on each check call.
#[test]
fn test_nra_check_count_increments() {
    let terms = TermStore::new();
    let mut solver = NraSolver::new(&terms);

    let _ = solver.check();
    let _ = solver.check();
    let _ = solver.check();

    let stats = solver.collect_statistics();
    let check_count = stats.iter().find(|(n, _)| *n == "nra_checks").unwrap().1;
    assert_eq!(check_count, 3, "check_count should increment on each call");
}

/// suggest_phase on an unknown atom should not panic.
#[test]
fn test_nra_suggest_phase_unknown_atom() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let zero = terms.mk_rational(BigRational::zero());
    let ge = terms.mk_ge(x, zero);

    let solver = NraSolver::new(&terms);
    // suggest_phase on an atom the solver has not seen should not panic
    let _ = solver.suggest_phase(ge);
}

/// Division purification: push/pop should scope div_purifications correctly.
#[test]
fn test_nra_division_purification_scope_depth() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let z = terms.mk_var("z", Sort::Real);
    let w = terms.mk_var("w", Sort::Real);
    let x_div_y = terms.mk_div(x, y);
    let z_div_w = terms.mk_div(z, w);
    let zero = terms.mk_rational(BigRational::zero());
    let ge1 = terms.mk_ge(x_div_y, zero);
    let ge2 = terms.mk_ge(z_div_w, zero);

    let mut solver = NraSolver::new(&terms);
    solver.assert_literal(ge1, true);
    let base = solver.div_purifications.len();

    solver.push();
    solver.assert_literal(ge2, true);
    assert!(solver.div_purifications.len() > base);

    solver.push();
    // no new assertions at level 2
    let level2 = solver.div_purifications.len();

    solver.pop();
    assert_eq!(
        solver.div_purifications.len(),
        level2,
        "pop without new assertions should not change div_purifications"
    );

    solver.pop();
    assert_eq!(
        solver.div_purifications.len(),
        base,
        "pop to base should restore original div_purifications count"
    );
}

/// Asserting both x*y >= 0 (true) and x*y >= 0 (false) should add 2 assertions.
#[test]
fn test_nra_dual_polarity_assertions() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let xy = terms.mk_mul(vec![x, y]);
    let zero = terms.mk_rational(BigRational::zero());
    let ge = terms.mk_ge(xy, zero);

    let mut solver = NraSolver::new(&terms);
    solver.assert_literal(ge, true);
    assert_eq!(solver.asserted.len(), 1);
    solver.assert_literal(ge, false);
    assert_eq!(solver.asserted.len(), 2);
    // Monomial registered once
    assert_eq!(solver.monomials.len(), 1);
}

/// McCormick with wide bounds: x in [0, 1000], y in [0, 1000].
/// Tangent plane at (500, 500): should produce valid bounds.
#[test]
fn test_mccormick_wide_bounds() {
    let xl = rat(0);
    let xu = rat(1000);
    let yl = rat(0);
    let yu = rat(1000);

    // Lower bound 1 at (0,0): m >= 0
    let lb1 = &xl * &yl + &yl * &xl - &xl * &yl;
    assert_eq!(lb1, rat(0));

    // Upper bound 1 at (1000, 0): m <= 1000*y + 0*x - 0 = 1000*y
    // At (500, 500): T = 1000*500 + 0*500 - 0 = 500000
    // Actual: 500*500 = 250000 <= 500000 (valid upper bound)
    let ub1_at_500 = &xu * &rat(500) + &yl * &rat(500) - &xu * &yl;
    assert_eq!(ub1_at_500, rat(500000));
    assert!(
        ub1_at_500 >= rat(250000),
        "McCormick upper bound should be >= actual"
    );

    // Upper bound 2 at (0, 1000): m <= 0*y + 1000*x - 0 = 1000*x
    // At (500, 500): T = 0*500 + 1000*500 - 0 = 500000
    let ub2_at_500 = &xl * &rat(500) + &yu * &rat(500) - &xl * &yu;
    assert_eq!(ub2_at_500, rat(500000));
}

/// Tangent hyperplane with all-equal factors at point (2, 2, 2).
/// Product = 8. Each partial = 4. Bound = -(3-1)*8 = -16.
/// T(x,y,z) = 4x + 4y + 4z - 16.
/// At (2,2,2): T = 8 + 8 + 8 - 16 = 8 = product (exact).
#[test]
fn test_tangent_hyperplane_all_equal_factors() {
    let vals = [rat(2), rat(2), rat(2)];
    let product = rat(8);
    let n = 3i64;

    let bound = -(rat(n - 1) * &product);
    assert_eq!(bound, rat(-16));

    for v in &vals {
        let coeff = -(&product / v);
        assert_eq!(coeff, rat(-4));
    }

    // Evaluate at (2,2,2): sum of coefficients * values + bound
    // -4*2 + -4*2 + -4*2 = -24; m + (-24) >= -16 => m >= 8 (correct)
}

/// Even power non-negativity: x^6 >= 0 for all x.
#[test]
fn test_even_power_sixth_nonneg() {
    for x_val in &[rat(-5), rat(-1), rat(0), rat(1), rat(5)] {
        let sixth = x_val * x_val * x_val * x_val * x_val * x_val;
        assert!(
            sixth >= BigRational::zero(),
            "x^6 must be >= 0 for x = {x_val}"
        );
    }
}

/// Tangent plane with large values should not overflow (BigRational handles it).
#[test]
fn test_tangent_plane_large_values() {
    let a = rat(1_000_000);
    let b = rat(1_000_000);
    // T(a, b) at (a, b) should equal a*b = 10^12
    let t_at_ab = &a * &b + &b * &a - &a * &b;
    assert_eq!(t_at_ab, rat(1_000_000) * rat(1_000_000));
}

/// Tangent plane with very small (fractional) values.
#[test]
fn test_tangent_plane_small_fractions() {
    let a = BigRational::new(1.into(), 1000.into()); // 0.001
    let b = BigRational::new(1.into(), 1000.into()); // 0.001
                                                     // T(a,b) at (a,b) = a*b + b*a - a*b = a*b = 10^-6
    let expected = BigRational::new(1.into(), 1_000_000.into());
    let t_at_ab = &a * &b + &b * &a - &a * &b;
    assert_eq!(t_at_ab, expected);
}

include!("tangent_tests/fixed_factor.rs");
