// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for dual (Farkas) optimality certificates (#lra-opt-cert).
//!
//! Every certificate returned by `optimize_with_certificate` must pass
//! `OptimalityCertificate::verify`, the independent checker that re-derives
//! the entailed bound from the atom terms alone (no solver state).

use super::*;
use crate::{OptimalityCertificate, OptimizationResult, OptimizationSense};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Zero};

fn rat(n: i64) -> BigRational {
    BigRational::from(BigInt::from(n))
}

fn rat2(n: i64, d: i64) -> BigRational {
    BigRational::new(BigInt::from(n), BigInt::from(d))
}

/// minimize x s.t. x >= 5: optimum 5, certificate {1 * (x >= 5)}.
#[test]
fn certificate_basic_minimize() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let five = terms.mk_rational(rat(5));
    let ge_5 = terms.mk_ge(x, five);

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(ge_5, true);
    assert!(matches!(solver.check(), TheoryResult::Sat));

    let x_var = *solver.term_to_var.get(&x).expect("x interned");
    let (result, cert) =
        solver.optimize_with_certificate(&LinearExpr::var(x_var), OptimizationSense::Minimize);

    assert!(matches!(result, OptimizationResult::Optimal(v) if v == rat(5)));
    let cert = cert.expect("certificate for single-bound minimize");
    assert_eq!(cert.bound, rat(5));
    assert!(!cert.strict);
    assert_eq!(cert.atoms.len(), 1);
    assert_eq!(cert.atoms[0].atom, ge_5);
    assert!(cert.atoms[0].value);
    assert_eq!(cert.atoms[0].coeff, BigRational::one());
    assert!(cert.verify(&terms, x), "independent check must pass");
}

/// maximize x s.t. 2x <= 10: optimum 5, multiplier is the Farkas scale 1/2.
#[test]
fn certificate_scaled_atom_maximize() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let two = terms.mk_rational(rat(2));
    let ten = terms.mk_rational(rat(10));
    let two_x = terms.mk_mul(vec![two, x]);
    let le_10 = terms.mk_le(two_x, ten);

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(le_10, true);
    assert!(matches!(solver.check(), TheoryResult::Sat));

    let x_var = *solver.term_to_var.get(&x).expect("x interned");
    let (result, cert) =
        solver.optimize_with_certificate(&LinearExpr::var(x_var), OptimizationSense::Maximize);

    assert!(matches!(result, OptimizationResult::Optimal(v) if v == rat(5)));
    let cert = cert.expect("certificate for scaled-atom maximize");
    assert_eq!(cert.sense, OptimizationSense::Maximize);
    assert_eq!(cert.bound, rat(5));
    assert_eq!(cert.atoms.len(), 1);
    assert_eq!(cert.atoms[0].coeff, rat2(1, 2));
    assert!(cert.verify(&terms, x), "independent check must pass");
}

/// minimize x + y s.t. x >= 0, y >= 0, x + y >= 10: optimum 10; the dual
/// combination must sum to exactly `x + y >= 10` whichever bounds block.
#[test]
fn certificate_two_vars_slack_bound() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let zero = terms.mk_rational(BigRational::zero());
    let ten = terms.mk_rational(rat(10));
    let x_ge_0 = terms.mk_ge(x, zero);
    let y_ge_0 = terms.mk_ge(y, zero);
    let x_plus_y = terms.mk_add(vec![x, y]);
    let sum_ge_10 = terms.mk_ge(x_plus_y, ten);

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(x_ge_0, true);
    solver.assert_literal(y_ge_0, true);
    solver.assert_literal(sum_ge_10, true);
    assert!(matches!(solver.check(), TheoryResult::Sat));

    let x_var = *solver.term_to_var.get(&x).expect("x interned");
    let y_var = *solver.term_to_var.get(&y).expect("y interned");
    let mut objective = LinearExpr::zero();
    objective.add_term(x_var, BigRational::one());
    objective.add_term(y_var, BigRational::one());

    let (result, cert) = solver.optimize_with_certificate(&objective, OptimizationSense::Minimize);

    assert!(matches!(result, OptimizationResult::Optimal(v) if v == rat(10)));
    let cert = cert.expect("certificate for two-var minimize");
    assert_eq!(cert.bound, rat(10));
    assert!(
        cert.verify(&terms, x_plus_y),
        "independent check must pass: {cert:?}"
    );
}

/// MINIMIZE TWIN of `standalone_optimizer_classifies_unattained_strict_supremum`.
///
/// A negated atom: `not(x <= 5)` is `x > 5`. Minimizing `x` has infimum 5 — and
/// NO feasible point attains it, because `x = 5` does not satisfy `x > 5`.
///
/// Contract history: this used to assert `Optimal(5)` with a `strict`
/// certificate, then was narrowed to `Unknown` by the strict fail-closed
/// guard. The delta-rational objective simplex (#opt-epsilon) now reports the
/// truth exactly: `OptimalInf { value: 5, eps_coeff: +1 }` — the infimum 5,
/// explicitly flagged unattained (approached as `5 + ε`), never a bare scalar
/// a consumer would go looking for a witness of, and never carrying a dual
/// certificate (Phase A).
#[test]
fn certificate_unattained_strict_infimum_is_epsilon_classified() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let five = terms.mk_rational(rat(5));
    let le_5 = terms.mk_le(x, five);

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(le_5, false); // x > 5
    assert!(matches!(solver.check(), TheoryResult::Sat));

    let x_var = *solver.term_to_var.get(&x).expect("x interned");
    let (result, cert) =
        solver.optimize_with_certificate(&LinearExpr::var(x_var), OptimizationSense::Minimize);

    match result {
        OptimizationResult::OptimalInf { value, eps_coeff } => {
            assert_eq!(value, rat(5));
            assert_eq!(eps_coeff, BigRational::one());
        }
        other => panic!("expected OptimalInf {{ 5, +1 }}, got {other:?}"),
    }
    assert!(
        cert.is_none(),
        "an unattained optimum carries no optimality certificate (Phase A)"
    );
}

/// Tampered certificates must be rejected by the independent checker.
#[test]
fn certificate_verify_rejects_tampering() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let five = terms.mk_rational(rat(5));
    let ge_5 = terms.mk_ge(x, five);

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(ge_5, true);
    assert!(matches!(solver.check(), TheoryResult::Sat));

    let x_var = *solver.term_to_var.get(&x).expect("x interned");
    let (_, cert) =
        solver.optimize_with_certificate(&LinearExpr::var(x_var), OptimizationSense::Minimize);
    let cert = cert.expect("certificate");
    assert!(cert.verify(&terms, x));

    // Claiming a better bound than entailed must fail.
    let mut too_strong = cert.clone();
    too_strong.bound = rat(6);
    assert!(!too_strong.verify(&terms, x));

    // A wrong multiplier must fail.
    let mut wrong_coeff = cert.clone();
    wrong_coeff.atoms[0].coeff = rat(2);
    assert!(!wrong_coeff.verify(&terms, x));

    // A flipped polarity must fail.
    let mut wrong_polarity = cert.clone();
    wrong_polarity.atoms[0].value = false;
    assert!(!wrong_polarity.verify(&terms, x));

    // A negative multiplier must fail even if the sum happens to match.
    let mut negative = cert;
    negative.atoms[0].coeff = -BigRational::one();
    assert!(!negative.verify(&terms, x));
}

/// Equality reasons are ambiguous to orient; extraction fails closed while
/// the optimum itself is still reported.
#[test]
fn certificate_fails_closed_on_equality_reason() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let five = terms.mk_rational(rat(5));
    let eq_5 = terms.mk_eq(x, five);

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(eq_5, true);
    assert!(matches!(solver.check(), TheoryResult::Sat));

    let x_var = *solver.term_to_var.get(&x).expect("x interned");
    let (result, cert) =
        solver.optimize_with_certificate(&LinearExpr::var(x_var), OptimizationSense::Minimize);

    assert!(matches!(result, OptimizationResult::Optimal(v) if v == rat(5)));
    assert!(
        cert.is_none(),
        "equality-justified bounds must fail closed, got {cert:?}"
    );
}

/// Unbounded objectives carry no certificate.
#[test]
fn certificate_none_when_unbounded() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let ten = terms.mk_rational(rat(10));
    let le_10 = terms.mk_le(x, ten);

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(le_10, true);
    assert!(matches!(solver.check(), TheoryResult::Sat));

    let x_var = *solver.term_to_var.get(&x).expect("x interned");
    let (result, cert) =
        solver.optimize_with_certificate(&LinearExpr::var(x_var), OptimizationSense::Minimize);

    assert!(matches!(result, OptimizationResult::Unbounded));
    assert!(cert.is_none());
}

/// A constant objective is certified by the empty combination.
#[test]
fn certificate_constant_objective() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let ten = terms.mk_rational(rat(10));
    let le_10 = terms.mk_le(x, ten);

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(le_10, true);
    assert!(matches!(solver.check(), TheoryResult::Sat));

    let objective = LinearExpr::constant(rat(7));
    let (result, cert) = solver.optimize_with_certificate(&objective, OptimizationSense::Minimize);

    assert!(matches!(result, OptimizationResult::Optimal(v) if v == rat(7)));
    let cert = cert.expect("empty certificate for constant objective");
    assert!(cert.atoms.is_empty());
    assert_eq!(cert.bound, rat(7));
    let seven = terms.mk_rational(rat(7));
    assert!(cert.verify(&terms, seven));
}

/// The hand-built cross-check from the module docs: the entailed inequality
/// must match the multiplier combination exactly, including constants.
#[test]
fn certificate_manual_combination_matches() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let one = terms.mk_rational(rat(1));
    let three = terms.mk_rational(rat(3));
    // x >= 1, y >= x + 3 (i.e. y - x >= 3): minimize y => 4 = 1*(x>=1) + 1*(y-x>=3)
    let x_ge_1 = terms.mk_ge(x, one);
    let y_minus_x = terms.mk_sub(vec![y, x]);
    let diff_ge_3 = terms.mk_ge(y_minus_x, three);

    let mut solver = LraSolver::new(&terms);
    solver.assert_literal(x_ge_1, true);
    solver.assert_literal(diff_ge_3, true);
    assert!(matches!(solver.check(), TheoryResult::Sat));

    let y_var = *solver.term_to_var.get(&y).expect("y interned");
    let (result, cert) =
        solver.optimize_with_certificate(&LinearExpr::var(y_var), OptimizationSense::Minimize);

    assert!(matches!(result, OptimizationResult::Optimal(v) if v == rat(4)));
    let cert = cert.expect("certificate for chained bounds");
    assert_eq!(cert.bound, rat(4));
    assert!(cert.verify(&terms, y), "independent check must pass");

    // The certificate must be exactly {1 * (x >= 1), 1 * (y - x >= 3)}.
    let expected = OptimalityCertificate {
        sense: OptimizationSense::Minimize,
        bound: rat(4),
        strict: false,
        atoms: vec![
            CertificateAtom {
                atom: x_ge_1,
                value: true,
                coeff: BigRational::one(),
            },
            CertificateAtom {
                atom: diff_ge_3,
                value: true,
                coeff: BigRational::one(),
            },
        ],
    };
    let mut got = cert.atoms.clone();
    got.sort_by_key(|a| a.atom);
    let mut want = expected.atoms.clone();
    want.sort_by_key(|a| a.atom);
    assert_eq!(got, want);
}

/// At a degenerate vertex, a basic variable can already be at one bound while
/// the requested entering move carries it away from that bound. It is not a
/// leaving candidate: selecting it used to alternate two zero-distance bases
/// until the 10,000-iteration limit.
#[test]
fn degenerate_optimization_pivots_only_on_the_limiting_bound() {
    let mut terms = TermStore::new();
    let x0 = terms.mk_var("x0", Sort::Real);
    let x1 = terms.mk_var("x1", Sort::Real);
    let x2 = terms.mk_var("x2", Sort::Real);
    let neg_one = terms.mk_rational(rat(-1));
    let neg_two = terms.mk_rational(rat(-2));
    let zero = terms.mk_rational(rat(0));
    let one = terms.mk_rational(rat(1));
    let two = terms.mk_rational(rat(2));
    let three = terms.mk_rational(rat(3));
    let four = terms.mk_rational(rat(4));

    let neg_two_x0 = terms.mk_mul(vec![neg_two, x0]);
    let neg_two_x1 = terms.mk_mul(vec![neg_two, x1]);
    let neg_two_x2 = terms.mk_mul(vec![neg_two, x2]);
    let row12 = terms.mk_add(vec![neg_two_x1, neg_two_x2]);
    let row02 = terms.mk_add(vec![neg_two_x0, neg_two_x2]);
    let neg_x0 = terms.mk_mul(vec![neg_one, x0]);
    let neg_x1 = terms.mk_mul(vec![neg_one, x1]);
    let objective = terms.mk_add(vec![neg_x0, neg_x1, x2]);

    let assertions = [
        terms.mk_ge(x0, zero),
        terms.mk_le(x0, one),
        terms.mk_ge(x1, neg_one),
        terms.mk_le(x1, one),
        terms.mk_ge(x2, zero),
        terms.mk_le(x2, four),
        terms.mk_ge(neg_two_x0, zero),
        terms.mk_le(neg_two_x0, three),
        terms.mk_le(row12, two),
        terms.mk_ge(row02, zero),
        terms.mk_le(row02, three),
        terms.mk_le(neg_two_x0, two),
    ];

    let mut solver = LraSolver::new(&terms);
    solver.set_standalone_simplex_mode();
    for assertion in assertions {
        solver.assert_literal(assertion, true);
    }
    let objective = solver.parse_linear_expr(objective);
    assert!(matches!(
        solver.optimize(&objective, OptimizationSense::Maximize),
        OptimizationResult::Optimal(value) if value == rat(1)
    ));
}

#[test]
fn standalone_optimizer_rejects_unresolved_disequality() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let zero = terms.mk_rational(rat(0));
    let one = terms.mk_rational(rat(1));
    let x_eq_one = terms.mk_eq(x, one);
    let x_ne_one = terms.mk_not(x_eq_one);
    let x_ge_zero = terms.mk_ge(x, zero);
    let x_le_one = terms.mk_le(x, one);

    let mut solver = LraSolver::new(&terms);
    solver.set_standalone_simplex_mode();
    solver.assert_literal(x_ge_zero, true);
    solver.assert_literal(x_le_one, true);
    solver.assert_literal(x_ne_one, true);
    let objective = solver.parse_linear_expr(x);
    assert!(matches!(
        solver.optimize(&objective, OptimizationSense::Maximize),
        OptimizationResult::Unknown
    ));
}

/// Contract history: the strict fail-closed guard used to force `Unknown`
/// here. The delta-rational objective simplex (#opt-epsilon) now classifies
/// the unattained supremum exactly: `0 <= x < 1`, maximize x =>
/// `OptimalInf { value: 1, eps_coeff: -1 }` (approached as `1 - ε`), never a
/// bare `Optimal(1)` that nothing attains.
#[test]
fn standalone_optimizer_classifies_unattained_strict_supremum() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let zero = terms.mk_rational(rat(0));
    let one = terms.mk_rational(rat(1));
    let x_ge_zero = terms.mk_ge(x, zero);
    let x_lt_one = terms.mk_lt(x, one);

    let mut solver = LraSolver::new(&terms);
    solver.set_standalone_simplex_mode();
    solver.assert_literal(x_ge_zero, true);
    solver.assert_literal(x_lt_one, true);
    let objective = solver.parse_linear_expr(x);
    match solver.optimize(&objective, OptimizationSense::Maximize) {
        OptimizationResult::OptimalInf { value, eps_coeff } => {
            assert_eq!(value, rat(1));
            assert_eq!(eps_coeff, -BigRational::one());
        }
        other => panic!("expected OptimalInf {{ 1, -1 }}, got {other:?}"),
    }
}

#[test]
fn standalone_optimizer_rejects_unsupported_nonlinear_atom() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let one = terms.mk_rational(rat(1));
    let product = terms.mk_mul(vec![x, y]);
    let nonlinear_bound = terms.mk_le(product, one);

    let mut solver = LraSolver::new(&terms);
    solver.set_standalone_simplex_mode();
    solver.assert_literal(nonlinear_bound, true);
    let objective = solver.parse_linear_expr(x);
    assert!(matches!(
        solver.optimize(&objective, OptimizationSense::Maximize),
        OptimizationResult::Unknown
    ));
}
