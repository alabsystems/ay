// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Kernel tests for `TheoryLemmaKind::NraIntervalUnsat`: valid refutations
//! accepted, INVALID refutations rejected (satisfiable systems, boundary
//! openness traps, wrong shapes, budget bombs), and recognize == validate.

use super::*;
use ay_core::{ProofId, Sort, TermId, TermStore};
use num_bigint::BigInt;
use num_rational::BigRational;

fn rat(n: i64) -> BigRational {
    BigRational::from_integer(BigInt::from(n))
}

fn real_var(terms: &mut TermStore, name: &str) -> TermId {
    terms.mk_var(name, Sort::Real)
}

fn real_const(terms: &mut TermStore, n: i64) -> TermId {
    terms.mk_rational(rat(n))
}

/// recognize must equal validate-success on every corpus clause (drift guard).
fn assert_no_drift(terms: &TermStore, clause: &[TermId]) {
    let rec = recognize_nra_interval_unsat(terms, clause);
    let val = validate_nra_interval_unsat(terms, ProofId(0), clause).is_ok();
    assert_eq!(rec, val, "recognizer and validator drifted");
    // Determinism: a second invocation is identical.
    assert_eq!(rec, recognize_nra_interval_unsat(terms, clause));
}

// ============================================================================
// Positives: valid refutations MUST be accepted
// ============================================================================

/// Miniature mbo: all-positive coefficients, positivity atoms, `= 0`, one
/// `not(and ...)` literal — the exact Sturm-MBO conflict shape.
#[test]
fn accepts_mini_mbo_positive_orthant_equality() {
    let mut terms = TermStore::new();
    let h1 = real_var(&mut terms, "h1");
    let h2 = real_var(&mut terms, "h2");
    let j2 = real_var(&mut terms, "j2");
    let zero = real_const(&mut terms, 0);
    let two = real_const(&mut terms, 2);
    let three = real_const(&mut terms, 3);

    let g1 = terms.mk_gt(h1, zero);
    let g2 = terms.mk_gt(h2, zero);
    let g3 = terms.mk_gt(j2, zero);
    // 2*h1*h1*j2 + 3*h2*j2*j2 + h1*h2 = 0
    let m1 = terms.mk_mul(vec![two, h1, h1, j2]);
    let m2 = terms.mk_mul(vec![three, h2, j2, j2]);
    let m3 = terms.mk_mul(vec![h1, h2]);
    let sum = terms.mk_add(vec![m1, m2, m3]);
    let eq = terms.mk_eq(sum, zero);
    let conj = terms.mk_and(vec![g1, g2, g3, eq]);
    let lit = terms.mk_not_raw(conj);
    let clause = vec![lit];

    assert!(recognize_nra_interval_unsat(&terms, &clause));
    validate_nra_interval_unsat(&terms, ProofId(0), &clause)
        .expect("mini-mbo refutation must validate");
    assert_no_drift(&terms, &clause);
}

/// Miniature hong: sum of squares < 1 and product > 1, two negated atoms.
#[test]
fn accepts_mini_hong_sumsq_product() {
    let mut terms = TermStore::new();
    let x = real_var(&mut terms, "x");
    let y = real_var(&mut terms, "y");
    let z = real_var(&mut terms, "z");
    let one = real_const(&mut terms, 1);

    let xx = terms.mk_mul(vec![x, x]);
    let yy = terms.mk_mul(vec![y, y]);
    let zz = terms.mk_mul(vec![z, z]);
    let sumsq = terms.mk_add(vec![xx, yy, zz]);
    let lt = terms.mk_lt(sumsq, one);
    let prod = terms.mk_mul(vec![x, y, z]);
    let gt = terms.mk_gt(prod, one);
    let clause = vec![terms.mk_not_raw(lt), terms.mk_not_raw(gt)];

    assert!(recognize_nra_interval_unsat(&terms, &clause));
    assert_no_drift(&terms, &clause);
}

/// x > 0, y > 0, x*y = 0: a strictly-positive product cannot be zero. This
/// needs the OPEN lower endpoint (0, inf) — the openness algebra positive.
#[test]
fn accepts_strict_positive_product_zero() {
    let mut terms = TermStore::new();
    let x = real_var(&mut terms, "x");
    let y = real_var(&mut terms, "y");
    let zero = real_const(&mut terms, 0);

    let gx = terms.mk_gt(x, zero);
    let gy = terms.mk_gt(y, zero);
    let prod = terms.mk_mul(vec![x, y]);
    let eq = terms.mk_eq(prod, zero);
    let conj = terms.mk_and(vec![gx, gy, eq]);
    let clause = vec![terms.mk_not_raw(conj)];

    assert!(recognize_nra_interval_unsat(&terms, &clause));
    assert_no_drift(&terms, &clause);
}

/// x > 1 and x^2 < 1: backward narrowing on x then a forward violation.
#[test]
fn accepts_gt_one_square_lt_one() {
    let mut terms = TermStore::new();
    let x = real_var(&mut terms, "x");
    let one = real_const(&mut terms, 1);

    let gx = terms.mk_gt(x, one);
    let sq = terms.mk_mul(vec![x, x]);
    let lt = terms.mk_lt(sq, one);
    let conj = terms.mk_and(vec![gx, lt]);
    let clause = vec![terms.mk_not_raw(conj)];

    assert!(recognize_nra_interval_unsat(&terms, &clause));
    assert_no_drift(&terms, &clause);
}

/// A FALSE constant conjunct refutes outright — but only with nonlinear
/// content present (the gate): x*x >= 0 keeps the clause in-fragment while
/// 1 < 0 refutes it.
#[test]
fn accepts_false_constant_conjunct_with_nonlinear_content() {
    let mut terms = TermStore::new();
    let x = real_var(&mut terms, "x");
    let zero = real_const(&mut terms, 0);
    let one = real_const(&mut terms, 1);

    let sq = terms.mk_mul(vec![x, x]);
    let ge = terms.mk_ge(sq, zero);
    // Build (< 1 0) via raw app to dodge constant folding.
    let lt = terms.mk_app(ay_core::Symbol::named("<"), [one, zero], Sort::Bool);
    let conj = terms.mk_and(vec![ge, lt]);
    let clause = vec![terms.mk_not_raw(conj)];

    assert!(recognize_nra_interval_unsat(&terms, &clause));
    assert_no_drift(&terms, &clause);
}

// ============================================================================
// Negatives: satisfiable or out-of-fragment MUST be refused
// ============================================================================

/// x >= 0, y >= 0, x*y = 0 is SATISFIABLE (x = y = 0): the closed-endpoint
/// twin of the strict positive test. Accepting it would be an unsound open
/// endpoint. MUST refuse.
#[test]
fn rejects_weak_positive_product_zero_satisfiable() {
    let mut terms = TermStore::new();
    let x = real_var(&mut terms, "x");
    let y = real_var(&mut terms, "y");
    let zero = real_const(&mut terms, 0);

    let gx = terms.mk_ge(x, zero);
    let gy = terms.mk_ge(y, zero);
    let prod = terms.mk_mul(vec![x, y]);
    let eq = terms.mk_eq(prod, zero);
    let conj = terms.mk_and(vec![gx, gy, eq]);
    let clause = vec![terms.mk_not_raw(conj)];

    assert!(!recognize_nra_interval_unsat(&terms, &clause));
    validate_nra_interval_unsat(&terms, ProofId(0), &clause)
        .expect_err("satisfiable system must be rejected");
    assert_no_drift(&terms, &clause);
}

/// x^2 >= 0 and x = 0 is satisfiable — the kernel must reach a fixpoint and
/// refuse, not refute.
#[test]
fn rejects_satisfiable_square_at_zero() {
    let mut terms = TermStore::new();
    let x = real_var(&mut terms, "x");
    let zero = real_const(&mut terms, 0);

    let sq = terms.mk_mul(vec![x, x]);
    let ge = terms.mk_ge(sq, zero);
    let eq = terms.mk_eq(x, zero);
    let conj = terms.mk_and(vec![ge, eq]);
    let clause = vec![terms.mk_not_raw(conj)];

    assert!(!recognize_nra_interval_unsat(&terms, &clause));
    assert_no_drift(&terms, &clause);
}

/// x*y > 1 alone is satisfiable: fixpoint without refutation → refuse.
#[test]
fn rejects_satisfiable_product_bound() {
    let mut terms = TermStore::new();
    let x = real_var(&mut terms, "x");
    let y = real_var(&mut terms, "y");
    let one = real_const(&mut terms, 1);

    let prod = terms.mk_mul(vec![x, y]);
    let gt = terms.mk_gt(prod, one);
    let clause = vec![terms.mk_not_raw(gt)];

    assert!(!recognize_nra_interval_unsat(&terms, &clause));
    assert_no_drift(&terms, &clause);
}

/// A LINEAR contradiction (x > 1, x < 0) must be refused by the
/// nonlinearity gate: linear conflicts stay in the LRA/LIA lanes.
#[test]
fn rejects_linear_conflict_nonlinearity_gate() {
    let mut terms = TermStore::new();
    let x = real_var(&mut terms, "x");
    let zero = real_const(&mut terms, 0);
    let one = real_const(&mut terms, 1);

    let gt = terms.mk_gt(x, one);
    let lt = terms.mk_lt(x, zero);
    let clause = vec![terms.mk_not_raw(gt), terms.mk_not_raw(lt)];

    assert!(!recognize_nra_interval_unsat(&terms, &clause));
    assert_no_drift(&terms, &clause);
}

/// Variable-count cap: a 25-variable product trips the <= 24 cap.
#[test]
fn rejects_variable_cap_trip() {
    let mut terms = TermStore::new();
    let zero = real_const(&mut terms, 0);
    let vars: Vec<TermId> = (0..25)
        .map(|i| real_var(&mut terms, &format!("v{i}")))
        .collect();
    let mut factors = vars.clone();
    factors.push(vars[0]); // ensure degree >= 2 (nonlinearity gate)
    let prod = terms.mk_mul(factors);
    let lt = terms.mk_lt(prod, zero);
    let mut conj_args = Vec::new();
    for &v in &vars {
        conj_args.push(terms.mk_gt(v, zero));
    }
    conj_args.push(lt);
    let conj = terms.mk_and(conj_args);
    let clause = vec![terms.mk_not_raw(conj)];

    assert!(!recognize_nra_interval_unsat(&terms, &clause));
    assert_no_drift(&terms, &clause);
}

/// Empty clause: refused.
#[test]
fn rejects_empty_clause() {
    let terms = TermStore::new();
    assert!(!recognize_nra_interval_unsat(&terms, &[]));
    validate_nra_interval_unsat(&terms, ProofId(0), &[])
        .expect_err("empty clause must be rejected");
}

/// A bare Boolean variable literal is out of the fragment.
#[test]
fn rejects_bool_var_literal() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    assert!(!recognize_nra_interval_unsat(&terms, &[p]));
    assert_no_drift(&terms, &[p]);
}

/// A non-Bool-sorted literal is refused at the first gate.
#[test]
fn rejects_non_bool_literal() {
    let mut terms = TermStore::new();
    let x = real_var(&mut terms, "x");
    assert!(!recognize_nra_interval_unsat(&terms, &[x]));
    assert_no_drift(&terms, &[x]);
}

/// Disjunctive structure (`or`) is out of the conjunctive fragment.
#[test]
fn rejects_or_literal() {
    let mut terms = TermStore::new();
    let x = real_var(&mut terms, "x");
    let zero = real_const(&mut terms, 0);
    let sq = terms.mk_mul(vec![x, x]);
    let a = terms.mk_gt(sq, zero);
    let b = terms.mk_lt(x, zero);
    let or = terms.mk_or(vec![a, b]);
    let clause = vec![terms.mk_not_raw(or)];
    assert!(!recognize_nra_interval_unsat(&terms, &clause));
    assert_no_drift(&terms, &clause);
}

/// A Real-sorted `ite` inside the arithmetic is out of the whitelisted
/// fragment (not an App — refused, not abstracted).
#[test]
fn rejects_real_ite_subterm() {
    let mut terms = TermStore::new();
    let x = real_var(&mut terms, "x");
    let p = terms.mk_var("p", Sort::Bool);
    let zero = real_const(&mut terms, 0);
    let one = real_const(&mut terms, 1);
    let ite = terms.mk_ite_raw(p, one, zero);
    let prod = terms.mk_mul(vec![x, x, ite]);
    let gt = terms.mk_gt(prod, zero);
    let lt = terms.mk_lt(prod, zero);
    let conj = terms.mk_and(vec![gt, lt]);
    let clause = vec![terms.mk_not_raw(conj)];
    assert!(!recognize_nra_interval_unsat(&terms, &clause));
    assert_no_drift(&terms, &clause);
}

/// Division by a VARIABLE becomes an opaque leaf; `(/ x y) = 2` alone is
/// linear in that leaf, so the nonlinearity gate refuses (and the system
/// would be satisfiable anyway). MUST refuse.
#[test]
fn rejects_division_by_variable() {
    let mut terms = TermStore::new();
    let x = real_var(&mut terms, "x");
    let y = real_var(&mut terms, "y");
    let two = real_const(&mut terms, 2);
    let div = terms.mk_div(x, y);
    let eq = terms.mk_eq(div, two);
    let clause = vec![terms.mk_not_raw(eq)];
    assert!(!recognize_nra_interval_unsat(&terms, &clause));
    assert_no_drift(&terms, &clause);
}

/// Opaque-leaf soundness positive: the SAME opaque term `(f x)` squared
/// being both > 0 and < 0 is infeasible for EVERY valuation of the leaf —
/// accepted; distinct leaves are never merged.
#[test]
fn accepts_opaque_leaf_contradiction() {
    let mut terms = TermStore::new();
    let x = real_var(&mut terms, "x");
    let zero = real_const(&mut terms, 0);
    let f = terms.mk_app(ay_core::Symbol::named("f"), [x], Sort::Real);
    let sq = terms.mk_mul(vec![f, f]);
    let gt = terms.mk_gt(sq, zero);
    let lt = terms.mk_lt(sq, zero);
    let conj = terms.mk_and(vec![gt, lt]);
    let clause = vec![terms.mk_not_raw(conj)];
    assert!(recognize_nra_interval_unsat(&terms, &clause));
    assert_no_drift(&terms, &clause);
}

/// Degree bomb: x^300 comparisons exceed the degree cap and refuse.
#[test]
fn rejects_degree_cap_bomb() {
    let mut terms = TermStore::new();
    let x = real_var(&mut terms, "x");
    let zero = real_const(&mut terms, 0);
    let big = terms.mk_mul(vec![x; 300]);
    let gt = terms.mk_gt(big, zero);
    let lt = terms.mk_lt(big, zero);
    let conj = terms.mk_and(vec![gt, lt]);
    let clause = vec![terms.mk_not_raw(conj)];
    assert!(!recognize_nra_interval_unsat(&terms, &clause));
    assert_no_drift(&terms, &clause);
}

// ============================================================================
// Interval algebra unit tests (openness soundness)
// ============================================================================

#[test]
fn interval_mul_zero_attained_when_factor_attains_zero() {
    // [0, 1] * (0, 1): 0 IS attained (0 * anything). An open lower endpoint
    // here would be the unsound direction.
    let mut meter = WorkMeter::new();
    let a = Ival {
        lo: Bnd::closed(rat(0)),
        hi: Bnd::closed(rat(1)),
    };
    let b = Ival {
        lo: Bnd::open(rat(0)),
        hi: Bnd::open(rat(1)),
    };
    let p = a.mul(&b, &mut meter).expect("mul");
    assert_eq!(p.lo, Bnd::closed(rat(0)), "0 attained via 0 * interior");
}

#[test]
fn interval_mul_strict_positive_keeps_zero_open() {
    // (0, inf) * (0, inf) = (0, inf): every product is strictly positive.
    let mut meter = WorkMeter::new();
    let a = Ival {
        lo: Bnd::open(rat(0)),
        hi: Bnd::PosInf,
    };
    let p = a.mul(&a.clone(), &mut meter).expect("mul");
    assert_eq!(p.lo, Bnd::open(rat(0)));
    assert_eq!(p.hi, Bnd::PosInf);
}

#[test]
fn interval_add_openness_or() {
    let mut meter = WorkMeter::new();
    let a = Ival {
        lo: Bnd::open(rat(0)),
        hi: Bnd::closed(rat(1)),
    };
    let b = Ival {
        lo: Bnd::closed(rat(0)),
        hi: Bnd::closed(rat(2)),
    };
    let s = a.add(&b, &mut meter).expect("add");
    assert_eq!(s.lo, Bnd::open(rat(0)), "open + closed lower = open");
    assert_eq!(s.hi, Bnd::closed(rat(3)));
}

#[test]
fn interval_even_pow_attains_zero_across_zero() {
    let mut meter = WorkMeter::new();
    let a = Ival {
        lo: Bnd::open(rat(-1)),
        hi: Bnd::open(rat(1)),
    };
    let p = a.pow(2, &mut meter).expect("pow");
    assert_eq!(p.lo, Bnd::closed(rat(0)), "0 = 0^2 is attained");
    assert_eq!(p.hi, Bnd::open(rat(1)));
}

#[test]
fn interval_odd_pow_monotone() {
    let mut meter = WorkMeter::new();
    let a = Ival {
        lo: Bnd::open(rat(-2)),
        hi: Bnd::closed(rat(3)),
    };
    let p = a.pow(3, &mut meter).expect("pow");
    assert_eq!(p.lo, Bnd::open(rat(-8)));
    assert_eq!(p.hi, Bnd::closed(rat(27)));
}

#[test]
fn interval_neg_inf_product_widening() {
    // (-inf, inf) * [0, 1] must stay (-inf, inf)-safe (contains everything).
    let mut meter = WorkMeter::new();
    let a = Ival::full();
    let b = Ival {
        lo: Bnd::closed(rat(0)),
        hi: Bnd::closed(rat(1)),
    };
    let p = a.mul(&b, &mut meter).expect("mul");
    assert_eq!(p.lo, Bnd::NegInf);
    assert_eq!(p.hi, Bnd::PosInf);
}
