// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Delta-rational objective simplex tests (#opt-epsilon).
//!
//! The objective loop in `optimize_impl` runs in `InfRational` (x + y·ε)
//! space, so STRICT bounds participate exactly: the terminal ε-part of the
//! objective classifies attainment (k = 0 ⟺ attained — a theorem of the
//! delta-order, not a heuristic), and a nonzero k yields
//! [`OptimizationResult::OptimalInf`] carrying the unattained sup/inf plus its
//! ε-coefficient. Sign convention: minimize ⇒ k > 0, maximize ⇒ k < 0.

use super::*;
use crate::{LinearExpr, OptimizationResult, OptimizationSense};

fn rat(n: i64, d: i64) -> BigRational {
    BigRational::new(BigInt::from(n), BigInt::from(d))
}

/// Build a solver over the given assertions, run `check()` (which parses atoms
/// and sets bounds), and return the interned objective variable for `obj`.
fn checked_solver(terms: &TermStore, assertions: &[(ay_core::TermId, bool)]) -> LraSolver {
    let mut solver = LraSolver::new(terms);
    for &(atom, polarity) in assertions {
        solver.assert_literal(atom, polarity);
    }
    assert!(
        is_sat_like(&solver.check()),
        "test constraints must be feasible"
    );
    solver
}

fn objective_of(solver: &LraSolver, var_term: ay_core::TermId) -> LinearExpr {
    LinearExpr::var(*solver.term_to_var().get(&var_term).expect("interned"))
}

#[test]
fn strict_upper_maximize_is_unattained_sup() {
    // x < 3, maximize x => sup 3, unattained: OptimalInf { 3, -1 }.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let c3 = terms.mk_rational(rat(3, 1));
    let lt = terms.mk_lt(x, c3);

    let mut solver = checked_solver(&terms, &[(lt, true)]);
    let obj = objective_of(&solver, x);
    match solver.optimize(&obj, OptimizationSense::Maximize) {
        OptimizationResult::OptimalInf { value, eps_coeff } => {
            assert_eq!(value, rat(3, 1));
            assert_eq!(eps_coeff, rat(-1, 1));
        }
        other => panic!("expected OptimalInf, got {other:?}"),
    }
}

#[test]
fn strict_lower_minimize_is_unattained_inf() {
    // x > 3/2, minimize x => inf 3/2, unattained: OptimalInf { 3/2, +1 }.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let c = terms.mk_rational(rat(3, 2));
    let gt = terms.mk_gt(x, c);

    let mut solver = checked_solver(&terms, &[(gt, true)]);
    let obj = objective_of(&solver, x);
    match solver.optimize(&obj, OptimizationSense::Minimize) {
        OptimizationResult::OptimalInf { value, eps_coeff } => {
            assert_eq!(value, rat(3, 2));
            assert_eq!(eps_coeff, rat(1, 1));
        }
        other => panic!("expected OptimalInf, got {other:?}"),
    }
}

#[test]
fn dominated_strict_bound_still_attains() {
    // x < 3 AND x <= 2, maximize x => the strict bound is dominated; the
    // optimum 2 is attained: plain Optimal(2), byte-identical legacy path.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let c3 = terms.mk_rational(rat(3, 1));
    let c2 = terms.mk_rational(rat(2, 1));
    let lt = terms.mk_lt(x, c3);
    let le = terms.mk_le(x, c2);

    let mut solver = checked_solver(&terms, &[(lt, true), (le, true)]);
    let obj = objective_of(&solver, x);
    match solver.optimize(&obj, OptimizationSense::Maximize) {
        OptimizationResult::Optimal(value) => assert_eq!(value, rat(2, 1)),
        other => panic!("expected Optimal, got {other:?}"),
    }
}

#[test]
fn epsilon_scales_through_bound_chains() {
    // y < x, x < 3, maximize y: y <= x - eps <= 3 - 2*eps => OptimalInf { 3, -2 }.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let c3 = terms.mk_rational(rat(3, 1));
    let y_lt_x = terms.mk_lt(y, x);
    let x_lt_3 = terms.mk_lt(x, c3);

    let mut solver = checked_solver(&terms, &[(y_lt_x, true), (x_lt_3, true)]);
    let obj = objective_of(&solver, y);
    match solver.optimize(&obj, OptimizationSense::Maximize) {
        OptimizationResult::OptimalInf { value, eps_coeff } => {
            assert_eq!(value, rat(3, 1));
            assert_eq!(eps_coeff, rat(-2, 1));
        }
        other => panic!("expected OptimalInf, got {other:?}"),
    }
}

#[test]
fn epsilon_scales_through_objective_coefficients() {
    // x < 3, maximize 2x => OptimalInf { 6, -2 }; fractional coefficient
    // 1/2 x => OptimalInf { 3/2, -1/2 } (fractional k, pinned vs z3).
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let c3 = terms.mk_rational(rat(3, 1));
    let lt = terms.mk_lt(x, c3);

    let mut solver = checked_solver(&terms, &[(lt, true)]);
    let x_var = *solver.term_to_var().get(&x).expect("interned");

    let mut double = LinearExpr::var(x_var);
    double.scale(&rat(2, 1));
    match solver.optimize(&double, OptimizationSense::Maximize) {
        OptimizationResult::OptimalInf { value, eps_coeff } => {
            assert_eq!(value, rat(6, 1));
            assert_eq!(eps_coeff, rat(-2, 1));
        }
        other => panic!("expected OptimalInf, got {other:?}"),
    }

    let mut half = LinearExpr::var(x_var);
    half.scale(&rat(1, 2));
    match solver.optimize(&half, OptimizationSense::Maximize) {
        OptimizationResult::OptimalInf { value, eps_coeff } => {
            assert_eq!(value, rat(3, 2));
            assert_eq!(eps_coeff, rat(-1, 2));
        }
        other => panic!("expected OptimalInf, got {other:?}"),
    }
}

#[test]
fn unbounded_direction_stays_unbounded_with_strict_elsewhere() {
    // y < 100, maximize x (free): Unbounded — a strict bound elsewhere must
    // not degrade the unbounded verdict (pre-#opt-epsilon it forced Unknown).
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let c100 = terms.mk_rational(rat(100, 1));
    let y_lt = terms.mk_lt(y, c100);
    // x participates via a non-binding constraint so it is interned.
    let x_ge = terms.mk_ge(x, c100);

    let mut solver = checked_solver(&terms, &[(y_lt, true), (x_ge, true)]);
    let obj = objective_of(&solver, x);
    assert!(matches!(
        solver.optimize(&obj, OptimizationSense::Maximize),
        OptimizationResult::Unbounded
    ));
}

#[test]
fn degenerate_vertex_with_strict_bound_terminates_attained() {
    // x <= y, x <= -y, x < 5, maximize x: the vertex (0,0) is degenerate
    // (both rows bind at ratio zero) and the strict bound is non-binding;
    // Bland's rule must terminate at the ATTAINED optimum 0.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let c5 = terms.mk_rational(rat(5, 1));
    let neg_y = terms.mk_neg(y);
    let le1 = terms.mk_le(x, y);
    let le2 = terms.mk_le(x, neg_y);
    let lt5 = terms.mk_lt(x, c5);

    let mut solver = checked_solver(&terms, &[(le1, true), (le2, true), (lt5, true)]);
    let obj = objective_of(&solver, x);
    match solver.optimize(&obj, OptimizationSense::Maximize) {
        OptimizationResult::Optimal(value) => assert_eq!(value, rat(0, 1)),
        other => panic!("expected Optimal(0), got {other:?}"),
    }
}

#[test]
fn equality_chain_doubles_epsilon() {
    // x = y, y < 3, maximize x + y => sup 6 approached as 2*(3-eps):
    // OptimalInf { 6, -2 } (adv4 shape, pinned vs z3).
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let c3 = terms.mk_rational(rat(3, 1));
    let eq = terms.mk_eq(x, y);
    let lt = terms.mk_lt(y, c3);

    let mut solver = checked_solver(&terms, &[(eq, true), (lt, true)]);
    let x_var = *solver.term_to_var().get(&x).expect("interned");
    let y_var = *solver.term_to_var().get(&y).expect("interned");
    let mut obj = LinearExpr::var(x_var);
    obj.add(&LinearExpr::var(y_var));
    match solver.optimize(&obj, OptimizationSense::Maximize) {
        OptimizationResult::OptimalInf { value, eps_coeff } => {
            assert_eq!(value, rat(6, 1));
            assert_eq!(eps_coeff, rat(-2, 1));
        }
        other => panic!("expected OptimalInf, got {other:?}"),
    }
}

#[test]
fn no_certificate_is_extracted_for_unattained_optima() {
    // Phase A: an unattained optimum never carries a dual certificate
    // (`(get-objective-certificates)` must not report an unverified shape).
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let c3 = terms.mk_rational(rat(3, 1));
    let lt = terms.mk_lt(x, c3);

    let mut solver = checked_solver(&terms, &[(lt, true)]);
    let obj = objective_of(&solver, x);
    let (result, certificate) =
        solver.optimize_impl(&obj, OptimizationSense::Maximize, 10_000, true);
    assert!(matches!(result, OptimizationResult::OptimalInf { .. }));
    assert!(certificate.is_none());
}
