// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Kernel tests for `TheoryLemmaKind::NraUnivariateUnsat`: valid univariate
//! refutations accepted (including at-root cases), INVALID ones rejected —
//! most importantly the sqrt(2) trap, where rational-only sampling would
//! forge a certificate for a satisfiable system — plus Sturm internals and a
//! brute-force rational-witness cross-check.

use super::*;
use crate::checker::recognize_nra_interval_unsat;
use ay_core::{ProofId, Sort, TermId, TermStore};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

fn rat(n: i64) -> BigRational {
    BigRational::from_integer(BigInt::from(n))
}

fn rat2(n: i64, d: i64) -> BigRational {
    BigRational::new(BigInt::from(n), BigInt::from(d))
}

fn real_var(terms: &mut TermStore, name: &str) -> TermId {
    terms.mk_var(name, Sort::Real)
}

fn real_const(terms: &mut TermStore, n: i64) -> TermId {
    terms.mk_rational(rat(n))
}

fn assert_no_drift(terms: &TermStore, clause: &[TermId]) {
    let rec = recognize_nra_univariate_unsat(terms, clause);
    let val = validate_nra_univariate_unsat(terms, ProofId(0), clause).is_ok();
    assert_eq!(rec, val, "recognizer and validator drifted");
    assert_eq!(rec, recognize_nra_univariate_unsat(terms, clause));
}

// ============================================================================
// Positives: valid univariate refutations MUST be accepted
// ============================================================================

/// hong_1 shape: x^2 < 1 and x > 1.
#[test]
fn accepts_hong_one_shape() {
    let mut terms = TermStore::new();
    let x = real_var(&mut terms, "x");
    let one = real_const(&mut terms, 1);
    let sq = terms.mk_mul(vec![x, x]);
    let lt = terms.mk_lt(sq, one);
    let gt = terms.mk_gt(x, one);
    let clause = vec![terms.mk_not_raw(lt), terms.mk_not_raw(gt)];

    assert!(recognize_nra_univariate_unsat(&terms, &clause));
    validate_nra_univariate_unsat(&terms, ProofId(0), &clause)
        .expect("hong_1-shaped refutation must validate");
    assert_no_drift(&terms, &clause);
}

/// x^2 = 2 and x > 2: infeasible (both roots of x^2-2 are below 2). The
/// at-root sign of x - 2 is decided algebraically on the irrational cells.
#[test]
fn accepts_sqrt_two_against_gt_two() {
    let mut terms = TermStore::new();
    let x = real_var(&mut terms, "x");
    let two = real_const(&mut terms, 2);
    let sq = terms.mk_mul(vec![x, x]);
    let eq = terms.mk_eq(sq, two);
    let gt = terms.mk_gt(x, two);
    let conj = terms.mk_and(vec![eq, gt]);
    let clause = vec![terms.mk_not_raw(conj)];

    assert!(recognize_nra_univariate_unsat(&terms, &clause));
    assert_no_drift(&terms, &clause);
}

/// x^2 + 1 <= 0: no real roots at all — single-cell scan refutes.
#[test]
fn accepts_square_plus_one_nonpositive() {
    let mut terms = TermStore::new();
    let x = real_var(&mut terms, "x");
    let zero = real_const(&mut terms, 0);
    let one = real_const(&mut terms, 1);
    let sq = terms.mk_mul(vec![x, x]);
    let sum = terms.mk_add(vec![sq, one]);
    let le = terms.mk_le(sum, zero);
    let clause = vec![terms.mk_not_raw(le)];

    assert!(recognize_nra_univariate_unsat(&terms, &clause));
    assert_no_drift(&terms, &clause);
}

/// (x-1)^2 <= 0 and x > 1: the even-multiplicity root pins x = 1, where
/// x > 1 fails — valid, and it exercises the at-root zero sign.
#[test]
fn accepts_even_multiplicity_root_pin() {
    let mut terms = TermStore::new();
    let x = real_var(&mut terms, "x");
    let zero = real_const(&mut terms, 0);
    let one = real_const(&mut terms, 1);
    let xm1 = terms.mk_sub(vec![x, one]);
    let sq = terms.mk_mul(vec![xm1, xm1]);
    let le = terms.mk_le(sq, zero);
    let gt = terms.mk_gt(x, one);
    let conj = terms.mk_and(vec![le, gt]);
    let clause = vec![terms.mk_not_raw(conj)];

    assert!(recognize_nra_univariate_unsat(&terms, &clause));
    assert_no_drift(&terms, &clause);
}

/// x^2 <= 0 and x > 0: the rational root 0 is hit by a bisection midpoint
/// (exact-root cell) and the scan refutes.
#[test]
fn accepts_exact_rational_root_cell() {
    let mut terms = TermStore::new();
    let x = real_var(&mut terms, "x");
    let zero = real_const(&mut terms, 0);
    let sq = terms.mk_mul(vec![x, x]);
    let le = terms.mk_le(sq, zero);
    let gt = terms.mk_gt(x, zero);
    let conj = terms.mk_and(vec![le, gt]);
    let clause = vec![terms.mk_not_raw(conj)];

    assert!(recognize_nra_univariate_unsat(&terms, &clause));
    assert_no_drift(&terms, &clause);
}

/// The univariate decision also covers opaque leaves: (f x)^2 < 0 alone.
#[test]
fn accepts_opaque_leaf_square_negative() {
    let mut terms = TermStore::new();
    let x = real_var(&mut terms, "x");
    let zero = real_const(&mut terms, 0);
    let f = terms.mk_app(ay_core::Symbol::named("f"), [x], Sort::Real);
    let sq = terms.mk_mul(vec![f, f]);
    let lt = terms.mk_lt(sq, zero);
    let clause = vec![terms.mk_not_raw(lt)];

    assert!(recognize_nra_univariate_unsat(&terms, &clause));
    assert_no_drift(&terms, &clause);
}

// ============================================================================
// Negatives: satisfiable systems MUST be refused — the sqrt(2) trap first
// ============================================================================

/// THE sqrt(2) trap: x^2 = 2 and x > 0 is satisfiable exactly at the
/// IRRATIONAL x = sqrt(2). Every rational x gives x^2 != 2, so a
/// rational-only sampler would refute it and forge a certificate for a
/// satisfiable constraint. The algebraic at-root sign must catch this.
#[test]
fn rejects_sqrt_two_trap() {
    let mut terms = TermStore::new();
    let x = real_var(&mut terms, "x");
    let zero = real_const(&mut terms, 0);
    let two = real_const(&mut terms, 2);
    let sq = terms.mk_mul(vec![x, x]);
    let eq = terms.mk_eq(sq, two);
    let gt = terms.mk_gt(x, zero);
    let conj = terms.mk_and(vec![eq, gt]);
    let clause = vec![terms.mk_not_raw(conj)];

    assert!(
        !recognize_nra_univariate_unsat(&terms, &clause),
        "the sqrt(2) trap MUST be refused: the system is satisfiable at an \
         irrational point"
    );
    validate_nra_univariate_unsat(&terms, ProofId(0), &clause)
        .expect_err("satisfiable-at-irrational system must be rejected");
    assert_no_drift(&terms, &clause);
}

/// x^2 = 2 and x >= 1: satisfiable AT the root sqrt(2) (>= holds there).
#[test]
fn rejects_satisfiable_at_root() {
    let mut terms = TermStore::new();
    let x = real_var(&mut terms, "x");
    let one = real_const(&mut terms, 1);
    let two = real_const(&mut terms, 2);
    let sq = terms.mk_mul(vec![x, x]);
    let eq = terms.mk_eq(sq, two);
    let ge = terms.mk_ge(x, one);
    let conj = terms.mk_and(vec![eq, ge]);
    let clause = vec![terms.mk_not_raw(conj)];

    assert!(!recognize_nra_univariate_unsat(&terms, &clause));
    assert_no_drift(&terms, &clause);
}

/// (x-1)^2 <= 0 and x >= 1: satisfiable exactly at the even-multiplicity
/// root x = 1.
#[test]
fn rejects_satisfiable_at_even_multiplicity_root() {
    let mut terms = TermStore::new();
    let x = real_var(&mut terms, "x");
    let zero = real_const(&mut terms, 0);
    let one = real_const(&mut terms, 1);
    let xm1 = terms.mk_sub(vec![x, one]);
    let sq = terms.mk_mul(vec![xm1, xm1]);
    let le = terms.mk_le(sq, zero);
    let ge = terms.mk_ge(x, one);
    let conj = terms.mk_and(vec![le, ge]);
    let clause = vec![terms.mk_not_raw(conj)];

    assert!(!recognize_nra_univariate_unsat(&terms, &clause));
    assert_no_drift(&terms, &clause);
}

/// x^2 = 0 and x >= 0: satisfiable at the rational root 0, which bisection
/// hits as an exact midpoint root.
#[test]
fn rejects_satisfiable_at_exact_rational_root() {
    let mut terms = TermStore::new();
    let x = real_var(&mut terms, "x");
    let zero = real_const(&mut terms, 0);
    let sq = terms.mk_mul(vec![x, x]);
    let eq = terms.mk_eq(sq, zero);
    let ge = terms.mk_ge(x, zero);
    let conj = terms.mk_and(vec![eq, ge]);
    let clause = vec![terms.mk_not_raw(conj)];

    assert!(!recognize_nra_univariate_unsat(&terms, &clause));
    assert_no_drift(&terms, &clause);
}

/// Two distinct variables: out of the univariate fragment.
#[test]
fn rejects_two_variables() {
    let mut terms = TermStore::new();
    let x = real_var(&mut terms, "x");
    let y = real_var(&mut terms, "y");
    let zero = real_const(&mut terms, 0);
    let prod = terms.mk_mul(vec![x, y]);
    let gt = terms.mk_gt(prod, zero);
    let lt = terms.mk_lt(prod, zero);
    let conj = terms.mk_and(vec![gt, lt]);
    let clause = vec![terms.mk_not_raw(conj)];

    assert!(!recognize_nra_univariate_unsat(&terms, &clause));
    assert_no_drift(&terms, &clause);
}

/// An mbo-shaped multivariate clause cross-tagged univariate must reject.
#[test]
fn rejects_mbo_shaped_multivariate_clause() {
    let mut terms = TermStore::new();
    let h1 = real_var(&mut terms, "h1");
    let h2 = real_var(&mut terms, "h2");
    let zero = real_const(&mut terms, 0);
    let g1 = terms.mk_gt(h1, zero);
    let g2 = terms.mk_gt(h2, zero);
    let m = terms.mk_mul(vec![h1, h1, h2]);
    let eq = terms.mk_eq(m, zero);
    let conj = terms.mk_and(vec![g1, g2, eq]);
    let clause = vec![terms.mk_not_raw(conj)];

    // The INTERVAL kernel accepts this (it is a valid refutation)...
    assert!(recognize_nra_interval_unsat(&terms, &clause));
    // ...but the UNIVARIATE kind must refuse it: two variables.
    assert!(!recognize_nra_univariate_unsat(&terms, &clause));
    assert_no_drift(&terms, &clause);
}

/// Linear conflicts stay out (nonlinearity gate).
#[test]
fn rejects_linear_conflict() {
    let mut terms = TermStore::new();
    let x = real_var(&mut terms, "x");
    let zero = real_const(&mut terms, 0);
    let one = real_const(&mut terms, 1);
    let gt = terms.mk_gt(x, one);
    let lt = terms.mk_lt(x, zero);
    let clause = vec![terms.mk_not_raw(gt), terms.mk_not_raw(lt)];

    assert!(!recognize_nra_univariate_unsat(&terms, &clause));
    assert_no_drift(&terms, &clause);
}

/// Degree-257 budget bomb: refused by the degree cap.
#[test]
fn rejects_degree_bomb() {
    let mut terms = TermStore::new();
    let x = real_var(&mut terms, "x");
    let zero = real_const(&mut terms, 0);
    let big = terms.mk_mul(vec![x; 257]);
    let gt = terms.mk_gt(big, zero);
    let lt = terms.mk_lt(big, zero);
    let conj = terms.mk_and(vec![gt, lt]);
    let clause = vec![terms.mk_not_raw(conj)];

    assert!(!recognize_nra_univariate_unsat(&terms, &clause));
    assert_no_drift(&terms, &clause);
}

/// Empty clause and Bool-variable literals refuse.
#[test]
fn rejects_empty_and_bool_var() {
    let mut terms = TermStore::new();
    assert!(!recognize_nra_univariate_unsat(&terms, &[]));
    let p = terms.mk_var("p", Sort::Bool);
    assert!(!recognize_nra_univariate_unsat(&terms, &[p]));
    assert_no_drift(&terms, &[p]);
}

// ============================================================================
// Sturm internals
// ============================================================================

fn upoly(coeffs: &[i64]) -> Vec<BigRational> {
    let mut p: Vec<BigRational> = coeffs.iter().map(|&c| rat(c)).collect();
    while p.last().is_some_and(num_traits::Zero::is_zero) {
        p.pop();
    }
    p
}

fn count_roots_between(p: &[BigRational], a: &BigRational, b: &BigRational) -> usize {
    let mut meter = WorkMeter::new();
    let chain = sturm_chain(&p.to_vec(), &mut meter).expect("chain");
    let va = sign_variations(&chain, a, &mut meter).expect("va");
    let vb = sign_variations(&chain, b, &mut meter).expect("vb");
    va - vb
}

#[test]
fn sturm_counts_match_known_factorizations() {
    // x(x-1)(x+2) = x^3 + x^2 - 2x: roots -2, 0, 1.
    let p = upoly(&[0, -2, 1, 1]);
    assert_eq!(count_roots_between(&p, &rat(-3), &rat(2)), 3);
    assert_eq!(count_roots_between(&p, &rat2(-1, 2), &rat(2)), 2);
    assert_eq!(count_roots_between(&p, &rat2(1, 2), &rat(2)), 1);
    assert_eq!(count_roots_between(&p, &rat2(3, 2), &rat(2)), 0);
}

#[test]
fn square_free_part_collapses_multiplicity() {
    let mut meter = WorkMeter::new();
    // (x-1)^2 = x^2 - 2x + 1 → square-free part proportional to (x-1).
    let p = upoly(&[1, -2, 1]);
    let sf = square_free_part(&p, &mut meter).expect("sf");
    assert_eq!(poly_deg(&sf), Some(1));
    // Root preserved: sf(1) = 0.
    assert!(poly_eval(&sf, &rat(1), &mut meter).expect("eval").is_zero());
}

#[test]
fn content_normalization_is_sign_faithful() {
    let mut meter = WorkMeter::new();
    // (-4/6)x + 2/3 → positive scaling only: signs per coefficient preserved.
    let p = vec![rat2(2, 3), rat2(-4, 6)];
    let n = content_normalize(&p, &mut meter).expect("normalize");
    assert_eq!(n.len(), 2);
    assert!(n[0].is_positive() && n[1].is_negative(), "signs preserved");
    // Primitive integer vector: gcd 1, denominators 1.
    assert!(n.iter().all(|c| c.denom().is_one()));
}

#[test]
fn cauchy_bound_contains_all_roots() {
    // x^2 - 4: roots ±2; M = 1 + 4 = 5 > 2.
    let p = upoly(&[-4, 0, 1]);
    let m = cauchy_bound(&p).expect("bound");
    assert!(m > rat(2));
    let mut meter = WorkMeter::new();
    let chain = sturm_chain(&p, &mut meter).expect("chain");
    let neg_m = -m.clone();
    let va = sign_variations(&chain, &neg_m, &mut meter).expect("va");
    let vb = sign_variations(&chain, &m, &mut meter).expect("vb");
    assert_eq!(va - vb, 2, "both roots strictly inside (-M, M)");
}

// ============================================================================
// Brute-force rational-witness cross-check + interval agreement
// ============================================================================

/// Deterministic mini property test: for a family of small univariate
/// systems, any rational witness found by brute force forces the recognizer
/// FALSE, and on single-variable systems an interval-kernel acceptance
/// implies a univariate acceptance (the univariate decision is complete).
#[test]
fn brute_force_witness_and_interval_agreement() {
    let grid: Vec<BigRational> = (-8..=8).map(|n| rat2(n, 2)).collect();
    // (coefficients low→high of p, relation name) systems of 2 constraints.
    let polys: Vec<Vec<i64>> = vec![
        vec![0, 0, 1],  // x^2
        vec![-2, 0, 1], // x^2 - 2
        vec![-1, 0, 1], // x^2 - 1
        vec![1, -2, 1], // (x-1)^2
        vec![0, 1],     // x
        vec![-1, 1],    // x - 1
        vec![1, 0, 1],  // x^2 + 1
    ];
    let rels = ["<", "<=", ">", ">=", "="];

    let mut checked = 0usize;
    for pa in &polys {
        for pb in &polys {
            for ra in &rels {
                for rb in &rels {
                    let mut terms = TermStore::new();
                    let x = real_var(&mut terms, "x");
                    let a1 = mk_poly_atom(&mut terms, x, pa, ra);
                    let a2 = mk_poly_atom(&mut terms, x, pb, rb);
                    let clause = vec![terms.mk_not_raw(a1), terms.mk_not_raw(a2)];

                    let accepted = recognize_nra_univariate_unsat(&terms, &clause);
                    if accepted {
                        // No rational grid point may satisfy both constraints.
                        for g in &grid {
                            let va = eval_i64_poly(pa, g);
                            let vb = eval_i64_poly(pb, g);
                            assert!(
                                !(rel_holds(ra, &va) && rel_holds(rb, &vb)),
                                "accepted system has rational witness {g}: \
                                 {pa:?} {ra} 0 && {pb:?} {rb} 0"
                            );
                        }
                    }
                    // Interval acceptance implies univariate acceptance on
                    // this shared single-variable fragment.
                    if recognize_nra_interval_unsat(&terms, &clause) {
                        assert!(
                            accepted,
                            "interval kernel accepted but the complete univariate \
                             decision refused: {pa:?} {ra} 0 && {pb:?} {rb} 0"
                        );
                    }
                    checked += 1;
                }
            }
        }
    }
    assert!(checked > 1000, "corpus actually ran");
}

fn mk_poly_atom(terms: &mut TermStore, x: TermId, coeffs: &[i64], rel: &str) -> TermId {
    let mut monos: Vec<TermId> = Vec::new();
    for (k, &c) in coeffs.iter().enumerate() {
        if c == 0 {
            continue;
        }
        let cterm = terms.mk_rational(rat(c));
        let mut factors = vec![cterm];
        for _ in 0..k {
            factors.push(x);
        }
        monos.push(terms.mk_mul(factors));
    }
    let zero = terms.mk_rational(BigRational::zero());
    let lhs = if monos.is_empty() {
        zero
    } else {
        terms.mk_add(monos)
    };
    match rel {
        "<" => terms.mk_lt(lhs, zero),
        "<=" => terms.mk_le(lhs, zero),
        ">" => terms.mk_gt(lhs, zero),
        ">=" => terms.mk_ge(lhs, zero),
        "=" => terms.mk_eq(lhs, zero),
        _ => unreachable!("test relation"),
    }
}

fn eval_i64_poly(coeffs: &[i64], x: &BigRational) -> BigRational {
    let mut acc = BigRational::zero();
    for &c in coeffs.iter().rev() {
        acc = acc * x + rat(c);
    }
    acc
}

fn rel_holds(rel: &str, v: &BigRational) -> bool {
    match rel {
        "<" => v < &BigRational::zero(),
        "<=" => v <= &BigRational::zero(),
        ">" => v > &BigRational::zero(),
        ">=" => v >= &BigRational::zero(),
        "=" => v.is_zero(),
        _ => unreachable!("test relation"),
    }
}
