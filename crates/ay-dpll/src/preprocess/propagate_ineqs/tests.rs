// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the `propagate-ineqs` bound-subsumption goal pass.
//!
//! Every expectation was verified against z3 4.15.4's `(apply
//! propagate-ineqs)` goal output (modulo AY's parse-time `>`/`>=` → `<`/`<=`
//! normalization, under which a z3 `(>= x 7)` is AY's `(<= 7 x)`).

use super::*;
use ay_core::Sort;
use num_bigint::BigInt;

fn int_var(terms: &mut TermStore, name: &str) -> TermId {
    terms.mk_var(name, Sort::Int)
}

fn int(terms: &mut TermStore, v: i64) -> TermId {
    terms.mk_int(BigInt::from(v))
}

fn apply(terms: &mut TermStore, fs: &mut Vec<TermId>) -> bool {
    PropagateIneqs::new().apply_goal(terms, fs)
}

#[test]
fn stronger_upper_bound_subsumes_weaker_same_strictness() {
    // (<= x 5) (<= x 10)  ->  ((<= x 5))   [z3-verified]
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "x");
    let five = int(&mut terms, 5);
    let ten = int(&mut terms, 10);
    let le5 = terms.mk_le(x, five);
    let le10 = terms.mk_le(x, ten);

    let mut fs = vec![le5, le10];
    assert!(apply(&mut terms, &mut fs));
    assert_eq!(fs, vec![le5]);
}

#[test]
fn subsumption_is_group_wise_not_a_sequential_filter() {
    // (<= x 10) (<= x 5)  ->  ((<= x 5)): the STRONGER LATER bound wins — a
    // sequential retained-so-far filter would wrongly keep the earlier 10.
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "x");
    let five = int(&mut terms, 5);
    let ten = int(&mut terms, 10);
    let le10 = terms.mk_le(x, ten);
    let le5 = terms.mk_le(x, five);

    let mut fs = vec![le10, le5];
    assert!(apply(&mut terms, &mut fs));
    assert_eq!(fs, vec![le5]);
}

#[test]
fn strongest_lower_bound_kept_alongside_upper() {
    // z3: (>= x 3) (>= x 7) (<= x 20)  ->  ((>= x 7) (<= x 20));
    // in AY's normalized shape: (<= 3 x) (<= 7 x) (<= x 20) -> ((<= 7 x) (<= x 20)).
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "x");
    let three = int(&mut terms, 3);
    let seven = int(&mut terms, 7);
    let twenty = int(&mut terms, 20);
    let ge3 = terms.mk_le(three, x);
    let ge7 = terms.mk_le(seven, x);
    let le20 = terms.mk_le(x, twenty);

    let mut fs = vec![ge3, ge7, le20];
    assert!(apply(&mut terms, &mut fs));
    assert_eq!(fs, vec![ge7, le20]);
}

#[test]
fn strict_and_non_strict_never_subsume_each_other() {
    // (< x 5) (<= x 5)  ->  both kept   [z3-verified]
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "x");
    let five = int(&mut terms, 5);
    let lt5 = terms.mk_lt(x, five);
    let le5 = terms.mk_le(x, five);

    let mut fs = vec![lt5, le5];
    assert!(!apply(&mut terms, &mut fs), "nothing subsumed: no progress");
    assert_eq!(fs, vec![lt5, le5]);
}

#[test]
fn strict_bounds_subsume_same_strictness_strict_bounds() {
    // Design rule (a) applies per strictness class: (< x 9) (< x 8) -> ((< x 8)).
    // DOCUMENTED SOUND DIVERGENCE: z3 4.15.4 keeps both strict bounds; AY
    // prints the simpler, still-equivalent goal.
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "x");
    let nine = int(&mut terms, 9);
    let eight = int(&mut terms, 8);
    let lt9 = terms.mk_lt(x, nine);
    let lt8 = terms.mk_lt(x, eight);

    let mut fs = vec![lt9, lt8];
    assert!(apply(&mut terms, &mut fs));
    assert_eq!(fs, vec![lt8]);
}

#[test]
fn contradictory_bounds_are_both_kept_no_false_collapse() {
    // (<= x 3) (<= 7 x)  ->  both kept, NO false   [z3-verified: no collapse]
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "x");
    let three = int(&mut terms, 3);
    let seven = int(&mut terms, 7);
    let le3 = terms.mk_le(x, three);
    let ge7 = terms.mk_le(seven, x);

    let mut fs = vec![le3, ge7];
    assert!(!apply(&mut terms, &mut fs));
    assert_eq!(fs, vec![le3, ge7]);
}

#[test]
fn passthrough_formulas_keep_their_slot() {
    // b (<= x 5) (<= x 10)  ->  (b (<= x 5))   [z3-verified]
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "x");
    let b = terms.mk_var("b", Sort::Bool);
    let five = int(&mut terms, 5);
    let ten = int(&mut terms, 10);
    let le5 = terms.mk_le(x, five);
    let le10 = terms.mk_le(x, ten);

    let mut fs = vec![b, le5, le10];
    assert!(apply(&mut terms, &mut fs));
    assert_eq!(fs, vec![b, le5]);
}

#[test]
fn value_equalities_are_re_emitted_at_the_end() {
    // (= x 5) b  ->  (b (= x 5))   [z3-verified]
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "x");
    let b = terms.mk_var("b", Sort::Bool);
    let five = int(&mut terms, 5);
    let eq = terms.mk_eq(x, five);

    let mut fs = vec![eq, b];
    assert!(apply(&mut terms, &mut fs));
    assert_eq!(fs, vec![b, eq]);
}

#[test]
fn value_equality_subsumes_satisfied_non_strict_bound() {
    // (= x 5) (<= x 10)  ->  ((= x 5))   [z3-verified]
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "x");
    let five = int(&mut terms, 5);
    let ten = int(&mut terms, 10);
    let eq = terms.mk_eq(x, five);
    let le10 = terms.mk_le(x, ten);

    let mut fs = vec![eq, le10];
    assert!(apply(&mut terms, &mut fs));
    assert_eq!(fs, vec![eq]);
}

#[test]
fn value_equality_never_subsumes_a_strict_bound() {
    // z3: (= x 5) (> x 3)  ->  ((> x 3) (= x 5)) — the STRICT bound is kept
    // (the equality is absorbed as the NON-strict pair x>=5 ∧ x<=5, and strict
    // and non-strict never subsume each other). AY shape: (< 3 x) kept.
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "x");
    let three = int(&mut terms, 3);
    let five = int(&mut terms, 5);
    let eq = terms.mk_eq(x, five);
    let gt3 = terms.mk_lt(three, x);

    let mut fs = vec![eq, gt3];
    assert!(
        apply(&mut terms, &mut fs),
        "the equality still moves to the end"
    );
    assert_eq!(fs, vec![gt3, eq]);
}

#[test]
fn contradictory_value_equality_keeps_the_bound() {
    // (= x 5) (< x 5)  ->  ((< x 5) (= x 5))   [z3-verified: both kept]
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "x");
    let five = int(&mut terms, 5);
    let eq = terms.mk_eq(x, five);
    let lt5 = terms.mk_lt(x, five);

    let mut fs = vec![eq, lt5];
    assert!(apply(&mut terms, &mut fs));
    assert_eq!(fs, vec![lt5, eq]);
}

#[test]
fn var_var_equalities_pass_through_in_place() {
    // (= x y) (<= x 10)  ->  unchanged   [z3-verified]
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "x");
    let y = int_var(&mut terms, "y");
    let ten = int(&mut terms, 10);
    let eq = terms.mk_eq(x, y);
    let le10 = terms.mk_le(x, ten);

    let mut fs = vec![eq, le10];
    assert!(!apply(&mut terms, &mut fs));
    assert_eq!(fs, vec![eq, le10]);
}

#[test]
fn monomial_bounds_pass_through() {
    // (<= (* 2 x) 10) (<= x 5)  ->  both kept in AY. DOCUMENTED SOUND
    // DIVERGENCE: z3 normalizes the monomial to x <= 5 and prints ((<= x 5))
    // only; AY does no coefficient normalization — weaker simplification,
    // still equivalent.
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "x");
    let two = int(&mut terms, 2);
    let five = int(&mut terms, 5);
    let ten = int(&mut terms, 10);
    let two_x = terms.mk_mul(vec![two, x]);
    let mono = terms.mk_le(two_x, ten);
    let le5 = terms.mk_le(x, five);

    let mut fs = vec![mono, le5];
    assert!(!apply(&mut terms, &mut fs));
    assert_eq!(fs, vec![mono, le5]);
}

#[test]
fn duplicate_bounds_dedup_to_one_copy() {
    // (<= x 5) (<= x 5)  ->  ((<= x 5))   [z3-verified]
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "x");
    let five = int(&mut terms, 5);
    let le5 = terms.mk_le(x, five);

    let mut fs = vec![le5, le5];
    assert!(apply(&mut terms, &mut fs));
    assert_eq!(fs, vec![le5]);
}

#[test]
fn duplicate_value_equalities_dedup_to_one_copy() {
    // (= x 5) (= x 5)  ->  ((= x 5))   [z3-verified]
    let mut terms = TermStore::new();
    let x = int_var(&mut terms, "x");
    let five = int(&mut terms, 5);
    let eq = terms.mk_eq(x, five);

    let mut fs = vec![eq, eq];
    assert!(apply(&mut terms, &mut fs));
    assert_eq!(fs, vec![eq]);
}

#[test]
fn real_bounds_compare_as_rationals() {
    // Real bounds: (<= x 5/2) (<= x 7/2)  ->  ((<= x 5/2))   [z3-verified via
    // decimal literals 2.5 / 3.5]
    use num_rational::BigRational;
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let five_halves = terms.mk_rational(BigRational::new(5.into(), 2.into()));
    let seven_halves = terms.mk_rational(BigRational::new(7.into(), 2.into()));
    let le_a = terms.mk_le(x, five_halves);
    let le_b = terms.mk_le(x, seven_halves);

    let mut fs = vec![le_a, le_b];
    assert!(apply(&mut terms, &mut fs));
    assert_eq!(fs, vec![le_a]);
}

#[test]
fn empty_goal_is_a_no_op() {
    let mut terms = TermStore::new();
    let mut fs: Vec<TermId> = Vec::new();
    assert!(!apply(&mut terms, &mut fs));
    assert!(fs.is_empty());
}
