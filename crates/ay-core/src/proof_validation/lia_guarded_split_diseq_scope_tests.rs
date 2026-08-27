// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The disequality-split arm's SCOPE and FAIL-CLOSED negatives: sort
//! discipline, the two work caps, and the shapes with no split source at all.
//!
//! Split out of `lia_guarded_split_diseq_tests` to keep both files inside the
//! quality gate's per-file size limit; the literal model, the clause builders
//! and the independent evaluator live in the parent module and are re-used
//! here through `use super::*`.

use super::*;
use crate::{Sort, TermStore};
use num_bigint::BigInt;

/// FALSIFYING ASSIGNMENT over ℚ: `r3 = 1, q2 = q0 + 1/2`. The lattice step is
/// licensed by integrality alone, so `Real`-sorted variables must fail the
/// candidate. The witness is CHECKED below in exact rational arithmetic
/// (doubled coordinates: `2q2 = 2q0 + 1`).
#[test]
fn rejects_real_sorted_parity_clause() {
    // Exact rational check of the witness, with everything doubled so the
    // arithmetic stays integral: q0 = 0, 2·q2 = 1, r3 = 1.
    let (two_q0, two_q2, r3) = (0i64, 1i64, 1i64);
    assert_eq!(two_q2 + r3, two_q0 + 2, "witness: 2q2 + r3 = 2q0 + 2");
    assert!(r3 < 2 && 0 <= r3 && r3 != 0, "witness falsifies the rest");

    let mut terms = TermStore::new();
    let q0 = terms.mk_var("q0", Sort::Real);
    let q2 = terms.mk_var("q2", Sort::Real);
    let r3 = terms.mk_var("r3", Sort::Real);
    let rat = |terms: &mut TermStore, n: i64| {
        terms.mk_rational(num_rational::BigRational::from(BigInt::from(n)))
    };
    let two = rat(&mut terms, 2);
    let two_q2 = terms.mk_mul(vec![two, q2]);
    let lhs = terms.mk_add(vec![two_q2, r3]);
    let two_b = rat(&mut terms, 2);
    let two_q0 = terms.mk_mul(vec![two_b, q0]);
    let two_c = rat(&mut terms, 2);
    let rhs = terms.mk_add(vec![two_q0, two_c]);
    let witness = terms.mk_eq(lhs, rhs);
    let l0 = terms.mk_not_raw(witness);
    let two_d = rat(&mut terms, 2);
    let upper = terms.mk_lt(r3, two_d);
    let l1 = terms.mk_not_raw(upper);
    let zero = rat(&mut terms, 0);
    let lower = terms.mk_le(zero, r3);
    let l2 = terms.mk_not_raw(lower);
    let zero_again = rat(&mut terms, 0);
    let l3 = terms.mk_eq(r3, zero_again);
    let clause = vec![l0, l1, l2, l3];
    assert!(
        !recognize_int_guarded_split_gap(&terms, &clause),
        "a Real-sorted parity clause is FALSE at r3 = 1, q2 = q0 + 1/2"
    );
}

/// The row cap declines OUTRIGHT rather than truncating, so acceptance can
/// never depend on literal order. The padded clause below carries the same
/// accepted core as the sweeps' parity family plus enough irrelevant bounds to
/// exceed `MAX_GUARDED_ROWS`; the unpadded core is accepted, so the decline is
/// the cap and nothing else.
#[test]
fn rejects_a_split_branch_wider_than_the_row_cap() {
    let core = [
        eq_row([2, 1, 0], 0),
        ge([0, 1, 0], 0),
        le([0, 1, 0], 1),
        diseq([0, 1, 0], 0),
    ];
    assert!(recognizes(&core), "the unpadded core must be accepted");

    let mut spec = core.to_vec();
    for k in 0..120i64 {
        spec.push(le([0, 0, 1], 10_000 + k));
    }
    assert!(
        !recognizes(&spec),
        "a clause past the row cap must be declined, not truncated"
    );
}

/// A clause with NO positive integer `=` and NO negated disjunction has no
/// split source at all; the arm's whole license is the case analysis.
#[test]
fn rejects_clause_without_any_split_source() {
    let spec = [eq_row([2, 1, 0], 0), ge([0, 1, 0], 0), le([0, 1, 0], 1)];
    // Falsified at x = 0, y = 0: the equality holds, and both bounds hold.
    assert_declined_and_falsified_at(&spec, [0, 0, 0]);
}

/// A positive `=` over a NON-arithmetic sort is not a disequality split: the
/// hypothesis contains `p != q` for uninterpreted `p, q`, which constrains no
/// linear form. Falsified by any interpretation with `p != q`, `y = 0`.
#[test]
fn rejects_positive_equality_over_an_uninterpreted_sort() {
    let mut terms = TermStore::new();
    let sort = Sort::Uninterpreted("S".to_string());
    let p = terms.mk_var("p", sort.clone());
    let q = terms.mk_var("q", sort);
    let eq = terms.mk_eq(p, q);
    let y = terms.mk_var("y", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let lower = terms.mk_le(zero, y);
    let l1 = terms.mk_not_raw(lower);
    let one = terms.mk_int(BigInt::from(1));
    let upper = terms.mk_le(y, one);
    let l2 = terms.mk_not_raw(upper);
    let clause = vec![eq, l1, l2];
    assert!(
        !recognize_int_guarded_split_gap(&terms, &clause),
        "an uninterpreted disequality constrains no linear form: false at \
         p != q, y = 0"
    );
}

/// SCOPE, and it is the guard that keeps this rule out of EUF's territory:
/// `int_linear_diff` returns an EMPTY coefficient map for `(= a a)` at ANY
/// sort, because the two sides cancel before the `Sort::Int` check can run on
/// anything. Splitting that "form" yields `0 >= 1` on both branches, so the
/// arm would accept every clause carrying a reflexive equality — sound (the
/// clause really is a tautology) but outside the rule's stated reach, and it
/// would silently take the shape `eq_reflexive` renders as a real Alethe rule.
#[test]
fn declines_a_split_over_a_variable_free_reflexive_equality() {
    let mut terms = TermStore::new();
    let u = Sort::Uninterpreted("U".to_string());
    let a = terms.mk_var("a", u.clone());
    let b = terms.mk_var("b", u);
    let eq_ab = terms.mk_eq(a, b);
    let not_ab = terms.mk_not_raw(eq_ab);
    // `mk_eq` folds `(= a a)` to `true`, so the raw application is built.
    let raw_eq_aa = terms.mk_app(crate::term::Symbol::named("="), [a, a], Sort::Bool);
    assert!(
        !recognize_int_guarded_split_gap(&terms, &[not_ab, raw_eq_aa]),
        "a variable-free reflexive equality is not an integer split source"
    );
}

/// The same guard over `Int`: `(= (+ x 1) (+ x 1))` also cancels to the empty
/// form, and the clause below is a reflexivity tautology that this rule must
/// leave to the rules that render it.
#[test]
fn declines_a_split_over_a_variable_free_integer_equality() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let one = terms.mk_int(BigInt::from(1));
    let lhs = terms.mk_add(vec![x, one]);
    let raw_eq = terms.mk_app(crate::term::Symbol::named("="), [lhs, lhs], Sort::Bool);
    let zero = terms.mk_int(BigInt::from(0));
    let bound = terms.mk_le(zero, x);
    let not_bound = terms.mk_not_raw(bound);
    assert!(
        !recognize_int_guarded_split_gap(&terms, &[raw_eq, not_bound]),
        "a variable-free reflexive equality is not an integer split source"
    );
}
