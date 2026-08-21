// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `*_holds` must agree with the `Result` verifier on EVERY input, and the
//! `λ = ±1` fast paths in [`super::farkas::LinearExpr::add_scaled`] must not
//! change a single verdict.
//!
//! Both changes exist to remove work, not to decide anything, so the whole
//! test surface is DIFFERENTIAL: for each input the two entry points are run
//! and their verdicts compared. A test that only asserted "this accepts" would
//! not catch a fast path that silently changed a combination — an agreement
//! sweep over inputs that include accepts, rejects, shape errors, disequality
//! case splits, zero weights and non-unit multipliers does.

use num_bigint::BigInt;
use num_rational::Rational64;

use super::{
    verify_farkas_conflict_lits_full, verify_farkas_conflict_lits_full_holds,
    verify_farkas_conflict_lits_linear, verify_farkas_conflict_lits_linear_holds,
};
use crate::{FarkasAnnotation, Sort, Symbol, TermId, TermStore, TheoryLit};

/// Assert both variants agree, and return the shared verdict.
#[track_caller]
fn agree(terms: &TermStore, conflict: &[TheoryLit], farkas: &FarkasAnnotation) -> bool {
    let full = verify_farkas_conflict_lits_full(terms, conflict, farkas).is_ok();
    let full_holds = verify_farkas_conflict_lits_full_holds(terms, conflict, farkas);
    assert_eq!(full, full_holds, "full/_holds disagree on {conflict:?}");
    let linear = verify_farkas_conflict_lits_linear(terms, conflict, farkas).is_ok();
    let linear_holds = verify_farkas_conflict_lits_linear_holds(terms, conflict, farkas);
    assert_eq!(
        linear, linear_holds,
        "linear/_holds disagree on {conflict:?}"
    );
    full
}

struct Bench {
    terms: TermStore,
    x: TermId,
    y: TermId,
}

impl Bench {
    fn new() -> Self {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let y = terms.mk_var("y", Sort::Int);
        Self { terms, x, y }
    }

    /// `(<= (+ (* a x) (* b y)) k)`.
    fn le(&mut self, a: i64, b: i64, k: i64) -> TermId {
        let ax = self.scaled(a, self.x);
        let by = self.scaled(b, self.y);
        let sum = self.terms.mk_add(vec![ax, by]);
        let konst = self.terms.mk_int(BigInt::from(k));
        self.terms.mk_le(sum, konst)
    }

    /// `(>= (+ (* a x) (* b y)) k)`.
    fn ge(&mut self, a: i64, b: i64, k: i64) -> TermId {
        let ax = self.scaled(a, self.x);
        let by = self.scaled(b, self.y);
        let sum = self.terms.mk_add(vec![ax, by]);
        let konst = self.terms.mk_int(BigInt::from(k));
        self.terms.mk_ge(sum, konst)
    }

    /// `(= (+ (* a x) (* b y)) k)`.
    fn eq(&mut self, a: i64, b: i64, k: i64) -> TermId {
        let ax = self.scaled(a, self.x);
        let by = self.scaled(b, self.y);
        let sum = self.terms.mk_add(vec![ax, by]);
        let konst = self.terms.mk_int(BigInt::from(k));
        self.terms.mk_eq(sum, konst)
    }

    fn scaled(&mut self, coefficient: i64, var: TermId) -> TermId {
        let c = self.terms.mk_int(BigInt::from(coefficient));
        self.terms.mk_mul(vec![c, var])
    }
}

#[test]
fn holds_agrees_with_result_on_an_accepting_unit_certificate() {
    let mut bench = Bench::new();
    // x >= 1 and x <= 0 is refuted by the all-ones combination.
    let lower = bench.ge(1, 0, 1);
    let upper = bench.le(1, 0, 0);
    let conflict = [TheoryLit::new(lower, true), TheoryLit::new(upper, true)];
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);
    assert!(agree(&bench.terms, &conflict, &farkas));
}

#[test]
fn holds_agrees_with_result_when_the_combination_fails() {
    let mut bench = Bench::new();
    // x >= 0 and x <= 1 is satisfiable: no certificate can refute it.
    let lower = bench.ge(1, 0, 0);
    let upper = bench.le(1, 0, 1);
    let conflict = [TheoryLit::new(lower, true), TheoryLit::new(upper, true)];
    for coefficients in [[1, 1], [2, 1], [1, 3], [5, 7]] {
        let farkas = FarkasAnnotation::from_ints(&coefficients);
        assert!(
            !agree(&bench.terms, &conflict, &farkas),
            "x in [0,1] must not be refutable with {coefficients:?}"
        );
    }
}

#[test]
fn holds_agrees_with_result_when_variables_survive() {
    let mut bench = Bench::new();
    // Only y is bounded, so x survives the combination.
    let lower = bench.ge(1, 1, 1);
    let upper = bench.le(0, 1, 0);
    let conflict = [TheoryLit::new(lower, true), TheoryLit::new(upper, true)];
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);
    assert!(!agree(&bench.terms, &conflict, &farkas));
}

#[test]
fn holds_agrees_with_result_on_a_shape_error() {
    let mut bench = Bench::new();
    let lower = bench.ge(1, 0, 1);
    let upper = bench.le(1, 0, 0);
    let conflict = [TheoryLit::new(lower, true), TheoryLit::new(upper, true)];
    // Wrong length, and a negative coefficient on an inequality row: both are
    // rejected before the combination is ever built.
    assert!(!agree(
        &bench.terms,
        &conflict,
        &FarkasAnnotation::from_ints(&[1])
    ));
    assert!(!agree(
        &bench.terms,
        &conflict,
        &FarkasAnnotation::new(vec![Rational64::from(-1), Rational64::from(1)])
    ));
}

#[test]
fn holds_agrees_with_result_on_a_non_arithmetic_literal() {
    let mut bench = Bench::new();
    let lower = bench.ge(1, 0, 1);
    let flag = bench.terms.mk_var("p", Sort::Bool);
    let conflict = [TheoryLit::new(lower, true), TheoryLit::new(flag, true)];
    assert!(!agree(
        &bench.terms,
        &conflict,
        &FarkasAnnotation::from_ints(&[1, 1])
    ));
    // With a ZERO weight the non-arithmetic literal is skipped, so the verdict
    // is decided by the remaining rows alone — still an agreement point.
    assert!(!agree(
        &bench.terms,
        &conflict,
        &FarkasAnnotation::from_ints(&[1, 0])
    ));
}

#[test]
fn holds_agrees_with_result_through_the_disequality_case_split() {
    // `x != x` is the accepting shape for the two-branch split: the difference
    // is the ZERO form, so BOTH branches reduce to the strict `0 < 0`. Built
    // through `mk_app` rather than `mk_eq` so the store does not fold the
    // reflexive equality to `true` before the verifier sees it.
    let mut bench = Bench::new();
    let reflexive = bench
        .terms
        .mk_app(Symbol::named("="), vec![bench.x, bench.x], Sort::Bool);
    let conflict = [TheoryLit::new(reflexive, false)];
    let farkas = FarkasAnnotation::from_ints(&[1]);
    assert!(
        agree(&bench.terms, &conflict, &farkas),
        "x != x must refute through both branches of the case split"
    );

    // A disequality whose difference is NOT the zero form leaves a variable
    // standing in each branch, so it must reject — through the same path.
    let satisfiable = bench.eq(1, 0, 0);
    let conflict = [TheoryLit::new(satisfiable, false)];
    assert!(!agree(&bench.terms, &conflict, &farkas));

    // Two weighted disequalities are unsupported outright; both entry points
    // must still say the same thing.
    let other = bench.eq(0, 1, 0);
    let conflict = [
        TheoryLit::new(reflexive, false),
        TheoryLit::new(other, false),
    ];
    assert!(!agree(
        &bench.terms,
        &conflict,
        &FarkasAnnotation::from_ints(&[1, 1])
    ));
}

#[test]
fn holds_agrees_with_result_on_the_asserted_equality_orientation_search() {
    // An equality asserted TRUE offers two orientations, so the combination
    // runs the orientation search rather than a single sum. `(= 1 2)` is
    // refuted by picking `2 - 1 <= 0`.
    let mut terms = TermStore::new();
    let one = terms.mk_int(BigInt::from(1));
    let two = terms.mk_int(BigInt::from(2));
    let false_equality = terms.mk_app(Symbol::named("="), vec![one, two], Sort::Bool);
    let conflict = [TheoryLit::new(false_equality, true)];
    assert!(agree(&terms, &conflict, &FarkasAnnotation::from_ints(&[1])));

    let true_equality = terms.mk_app(Symbol::named("="), vec![one, one], Sort::Bool);
    let conflict = [TheoryLit::new(true_equality, true)];
    assert!(!agree(
        &terms,
        &conflict,
        &FarkasAnnotation::from_ints(&[1])
    ));
}

#[test]
fn the_negative_one_fast_path_matches_the_general_multiplier() {
    // `x = y` asserted TRUE carries a SIGN-FREE multiplier, so `-1` reaches
    // `add_scaled` and takes the `sub_expr` fast path. The same conflict scaled
    // by 2 takes the general path and must agree.
    let mut bench = Bench::new();
    let equality = bench.eq(1, -1, 0); // x - y = 0
    let strict = bench.ge(1, -1, 1); // x - y >= 1
    let conflict = [TheoryLit::new(equality, true), TheoryLit::new(strict, true)];
    let minus_one = FarkasAnnotation::new(vec![Rational64::from(-1), Rational64::from(1)]);
    let minus_two = FarkasAnnotation::new(vec![Rational64::from(-2), Rational64::from(2)]);
    assert!(agree(&bench.terms, &conflict, &minus_one));
    assert!(agree(&bench.terms, &conflict, &minus_two));
}

#[test]
fn unit_and_scaled_certificates_agree_across_a_bounded_sweep() {
    // Falsification sweep: every `(a, b, k)` box below is decided twice — once
    // through the `Result` verifier and once through `*_holds` — and the two
    // must never disagree. It also mixes unit and non-unit multipliers so both
    // the `λ = 1` fast path and the general path are exercised on the SAME
    // conflicts.
    let mut accepted = 0usize;
    let mut rejected = 0usize;
    for a in 1..=3i64 {
        for k in -2..=2i64 {
            for lambda in 1..=3i64 {
                let mut bench = Bench::new();
                let lower = bench.ge(a, 0, k);
                let upper = bench.le(a, 0, k - 1);
                let conflict = [TheoryLit::new(lower, true), TheoryLit::new(upper, true)];
                let farkas = FarkasAnnotation::from_ints(&[lambda, lambda]);
                if agree(&bench.terms, &conflict, &farkas) {
                    accepted += 1;
                } else {
                    rejected += 1;
                }

                // A satisfiable box with the same multipliers: must reject.
                let mut sat = Bench::new();
                let lower = sat.ge(a, 0, k);
                let upper = sat.le(a, 0, k + 1);
                let conflict = [TheoryLit::new(lower, true), TheoryLit::new(upper, true)];
                assert!(
                    !agree(&sat.terms, &conflict, &farkas),
                    "a={a} k={k} lambda={lambda}: a satisfiable box must not be refuted"
                );
                rejected += 1;
            }
        }
    }
    // The sweep must not pass vacuously in either direction.
    assert!(accepted >= 45, "sweep accepted only {accepted}");
    assert!(rejected >= 45, "sweep rejected only {rejected}");
}

#[test]
fn holds_agrees_on_the_congruence_only_conflict_that_separates_the_two_variants() {
    // `f(x) < f(y)` with `x = y` is UNSAT only modulo congruence: the `full`
    // variant accepts, the `linear` variant must not. `agree` checks each
    // variant against its own `*_holds`, so this pins that the two remain
    // DISTINGUISHED after the refactor rather than collapsing onto one.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let fx = terms.mk_app(Symbol::named("f"), vec![x], Sort::Int);
    let fy = terms.mk_app(Symbol::named("f"), vec![y], Sort::Int);
    let one = terms.mk_int(BigInt::from(1));
    let neg_fy = terms.mk_neg(fy);
    let diff = terms.mk_add(vec![fx, neg_fy]);
    let gap = terms.mk_ge(diff, one); // f(x) - f(y) >= 1
    let equality = terms.mk_eq(x, y);
    let conflict = [TheoryLit::new(gap, true), TheoryLit::new(equality, true)];
    let farkas = FarkasAnnotation::from_ints(&[1, 1]);

    let full = verify_farkas_conflict_lits_full(&terms, &conflict, &farkas).is_ok();
    let linear = verify_farkas_conflict_lits_linear(&terms, &conflict, &farkas).is_ok();
    assert_eq!(
        full,
        verify_farkas_conflict_lits_full_holds(&terms, &conflict, &farkas)
    );
    assert_eq!(
        linear,
        verify_farkas_conflict_lits_linear_holds(&terms, &conflict, &farkas)
    );
    assert!(
        full,
        "congruence merges f(x) and f(y), so the full variant accepts"
    );
    assert!(
        !linear,
        "the linear variant performs no congruence reasoning"
    );
}
