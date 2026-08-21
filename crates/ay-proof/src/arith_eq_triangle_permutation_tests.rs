// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Recognizer, strict-checker and external-lowering tests for
//! `TheoryLemmaKind::ArithEqTriangle` reached through a NON-canonical literal
//! order.
//!
//! Two independent facts are pinned here, because the fix that consumes them
//! lives in another crate (`ay-dpll`'s classification funnel) and would
//! otherwise rest on an unstated assumption:
//!
//! 1. `validate_arith_eq_triangle` is ORDER-SENSITIVE and accepts exactly
//!    `[not_forward, not_reverse, equality]`. The census shape on #4751 —
//!    `(cl (= 0 d) (not (<= 0 d)) (not (<= d 0)))` — is that schema in the
//!    permutation `[1, 2, 0]`, so a classifier that records the CALLER's order
//!    under this kind produces a step the strict checker refuses. Recording
//!    the reordered clause is therefore mandatory, not cosmetic.
//! 2. The Alethe lowering must unpack `la_disequality`'s or-term in the
//!    PREMISE's order. carcara's `or` is positional (measured, see the `or`
//!    arm in `alethe_printer.rs`), and a permuted `or` step takes the whole
//!    document from `holey` to `invalid` — strictly worse than the `hole` the
//!    clause would otherwise have printed as.

use super::*;
use ay_core::{FarkasAnnotation, Sort, TermStore, TheoryLemmaKind};
use num_bigint::BigInt;
use num_rational::Rational64;

/// The exact #4751 census clause: `(cl (= 0 d) (not (<= 0 d)) (not (<= d 0)))`
/// over an `Int` definitional variable, returned with the three literals
/// separately so tests can permute them.
struct Triangle {
    equality: TermId,
    not_forward: TermId,
    not_reverse: TermId,
}

/// Build `(= lhs rhs)`, `(not (<= lhs rhs))`, `(not (<= rhs lhs))`.
fn triangle_of(terms: &mut TermStore, lhs: TermId, rhs: TermId) -> Triangle {
    let equality = terms.mk_eq(lhs, rhs);
    let forward = terms.mk_le(lhs, rhs);
    let reverse = terms.mk_le(rhs, lhs);
    Triangle {
        equality,
        not_forward: terms.mk_not(forward),
        not_reverse: terms.mk_not(reverse),
    }
}

fn census_triangle(terms: &mut TermStore) -> Triangle {
    let zero = terms.mk_int(BigInt::from(0));
    let d = terms.mk_var("__ay_eqdv!10", Sort::Int);
    triangle_of(terms, zero, d)
}

fn triangle_step(clause: Vec<TermId>, farkas: Option<FarkasAnnotation>) -> ProofStep {
    ProofStep::TheoryLemma {
        theory: "LIA".to_string(),
        clause,
        farkas,
        kind: TheoryLemmaKind::ArithEqTriangle,
        lia: None,
    }
}

// =====================================================================
// 1. The order fact the funnel fix rests on
// =====================================================================

/// THE PROBE. The census order is rejected by the real validator; the
/// `[1, 2, 0]` permutation of it is accepted, with no checker change.
#[test]
fn the_census_order_is_rejected_and_its_permutation_accepted_unchanged() {
    let mut terms = TermStore::new();
    let t = census_triangle(&mut terms);
    let census = vec![t.equality, t.not_forward, t.not_reverse];
    assert!(
        !recognize_arith_eq_triangle(&terms, &census),
        "precondition: the producer's own order must be validator-REJECTED, \
         otherwise the funnel fix would be reordering for no reason"
    );
    let permuted = vec![census[1], census[2], census[0]];
    assert!(
        recognize_arith_eq_triangle(&terms, &permuted),
        "the [1, 2, 0] permutation must be accepted by the EXISTING validator"
    );
}

/// Exactly ONE of the six permutations is accepted, so a classifier that
/// sweeps them cannot make acceptance depend on the sweep's order.
#[test]
fn exactly_one_permutation_of_the_triangle_validates() {
    let mut terms = TermStore::new();
    let t = census_triangle(&mut terms);
    let (a, b, c) = (t.equality, t.not_forward, t.not_reverse);
    let accepted = [
        [a, b, c],
        [a, c, b],
        [b, a, c],
        [b, c, a],
        [c, a, b],
        [c, b, a],
    ]
    .into_iter()
    .filter(|order| recognize_arith_eq_triangle(&terms, order))
    .count();
    assert_eq!(
        accepted, 1,
        "the schema pins every position to a distinct shape"
    );
}

/// The bounds may be handed over in reverse order too — `[not_reverse,
/// not_forward, equality]` is a genuine tautology the validator refuses, and
/// the accepted permutation swaps them back.
#[test]
fn reversed_bounds_are_accepted_only_after_the_swap() {
    let mut terms = TermStore::new();
    let t = census_triangle(&mut terms);
    let reversed = vec![t.not_reverse, t.not_forward, t.equality];
    assert!(!recognize_arith_eq_triangle(&terms, &reversed));
    let swapped = vec![t.not_forward, t.not_reverse, t.equality];
    assert!(recognize_arith_eq_triangle(&terms, &swapped));
}

/// `Real` operands are accepted too: antisymmetry is an ordered-field fact,
/// not an integer one.
#[test]
fn the_schema_holds_over_real_operands() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let t = triangle_of(&mut terms, x, y);
    assert!(recognize_arith_eq_triangle(
        &terms,
        &[t.not_forward, t.not_reverse, t.equality]
    ));
}

// =====================================================================
// 2. Adversarial negatives — each names a falsifying assignment
// =====================================================================

/// FALSIFIED AT `a = 0, b = 0, c = 1`: `(not (<= 0 0))` is false, `(not (<= 0
/// 0))` is false, `(0 = 1)` is false — the whole clause is FALSE, so no
/// permutation of it may validate.
#[test]
fn a_third_operand_in_the_equality_is_rejected_in_every_order() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let c = terms.mk_var("c", Sort::Int);
    let equality = terms.mk_eq(a, c);
    let forward = terms.mk_le(a, b);
    let reverse = terms.mk_le(b, a);
    let not_forward = terms.mk_not(forward);
    let not_reverse = terms.mk_not(reverse);
    assert_no_permutation_validates(&terms, [equality, not_forward, not_reverse]);
}

/// FALSIFIED AT `a = 0, b = 0, c = 1`: `(not (<= a b))` = `(not (<= 0 0))` is
/// false, `(not (<= b c))` = `(not (<= 0 1))` is false, and `(= a c)` =
/// `(0 = 1)` is false — a CHAIN of bounds does not close the triangle.
#[test]
fn a_chained_bound_pair_is_rejected_in_every_order() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let c = terms.mk_var("c", Sort::Int);
    let equality = terms.mk_eq(a, c);
    let forward = terms.mk_le(a, b);
    let reverse = terms.mk_le(b, c);
    let not_forward = terms.mk_not(forward);
    let not_reverse = terms.mk_not(reverse);
    assert_no_permutation_validates(&terms, [equality, not_forward, not_reverse]);
}

/// FALSIFIED AT `a = 0, b = 0`: the bounds `0 <= 0` hold so both negations are
/// false, and `(= 0 (+ 0 1))` is false. Syntactic operand identity between the
/// equality and the two bounds is load-bearing.
#[test]
fn an_offset_equality_operand_is_rejected_in_every_order() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let one = terms.mk_int(BigInt::from(1));
    let shifted = terms.mk_add(vec![b, one]);
    let equality = terms.mk_eq(a, shifted);
    let forward = terms.mk_le(a, b);
    let reverse = terms.mk_le(b, a);
    let not_forward = terms.mk_not(forward);
    let not_reverse = terms.mk_not(reverse);
    assert_no_permutation_validates(&terms, [equality, not_forward, not_reverse]);
}

/// FALSIFIED AT `a = 0, b = 1`: `(<= 0 1)` holds so `(not (<= a b))` is false,
/// the DUPLICATED copy of it is false too, and `(0 = 1)` is false.
#[test]
fn a_duplicated_forward_bound_is_rejected_in_every_order() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let equality = terms.mk_eq(a, b);
    let forward = terms.mk_le(a, b);
    let not_forward = terms.mk_not(forward);
    assert_no_permutation_validates(&terms, [equality, not_forward, not_forward]);
}

/// The strict-bound variant `(cl (= a b) (not (< a b)) (not (< b a)))` is in
/// fact VALID, and that is the point: the validator still declines it, because
/// `la_disequality` is stated over `<=`. A decline is never evidence that a
/// clause is false, only that this kind does not certify it.
#[test]
fn strict_bounds_are_declined_rather_than_certified() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let equality = terms.mk_eq(a, b);
    let forward = terms.mk_lt(a, b);
    let reverse = terms.mk_lt(b, a);
    let not_forward = terms.mk_not(forward);
    let not_reverse = terms.mk_not(reverse);
    assert_no_permutation_validates(&terms, [equality, not_forward, not_reverse]);
}

/// A four-literal clause carrying the whole valid triangle plus one junk
/// literal is refused: the kind authorizes exactly three literals, so it can
/// never launder an extra disjunct into a certified step.
#[test]
fn a_widened_triangle_is_refused_by_the_length_gate() {
    let mut terms = TermStore::new();
    let t = census_triangle(&mut terms);
    let junk = terms.mk_var("junk", Sort::Bool);
    let clause = vec![t.not_forward, t.not_reverse, t.equality, junk];
    assert!(!recognize_arith_eq_triangle(&terms, &clause));
}

fn assert_no_permutation_validates(terms: &TermStore, lits: [TermId; 3]) {
    let [a, b, c] = lits;
    for order in [
        [a, b, c],
        [a, c, b],
        [b, a, c],
        [b, c, a],
        [c, a, b],
        [c, b, a],
    ] {
        assert!(
            !recognize_arith_eq_triangle(terms, &order),
            "no permutation of a non-schema clause may validate: {order:?}"
        );
    }
}

// =====================================================================
// 3. Strict-checker acceptance and forgery refusal
// =====================================================================

#[test]
fn strict_mode_accepts_the_reordered_triangle_and_refuses_a_forged_label() {
    let mut terms = TermStore::new();
    let t = census_triangle(&mut terms);
    let step = triangle_step(vec![t.not_forward, t.not_reverse, t.equality], None);
    let mut derived = Vec::new();
    checker::validate_step(&terms, &mut derived, ProofId(0), &step, true, None)
        .expect("the reordered triangle must validate in strict mode");

    // FORGERY: the census order under the same kind. Refused as a STEP, not as
    // a formula — the checker must not accept a clause whose literals sit
    // where its rule does not put them.
    let forged = triangle_step(vec![t.equality, t.not_forward, t.not_reverse], None);
    let mut derived = Vec::new();
    assert!(
        checker::validate_step(&terms, &mut derived, ProofId(0), &forged, true, None).is_err(),
        "strict mode must refuse the schema in the producer's order"
    );

    // FORGERY: an outright false clause. `(cl (not (<= a b)) (not (<= b a))
    // (= a c))` is false at a = 0, b = 0, c = 1.
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let c = terms.mk_var("c", Sort::Int);
    let equality = terms.mk_eq(a, c);
    let forward = terms.mk_le(a, b);
    let reverse = terms.mk_le(b, a);
    let not_forward = terms.mk_not(forward);
    let not_reverse = terms.mk_not(reverse);
    let forged = triangle_step(vec![not_forward, not_reverse, equality], None);
    let mut derived = Vec::new();
    assert!(
        checker::validate_step(&terms, &mut derived, ProofId(0), &forged, true, None).is_err(),
        "a meta-false PROVE must be refused: falsified at a = 0, b = 0, c = 1"
    );
}

// =====================================================================
// 4. The Alethe wire
// =====================================================================

/// The lowering unpacks `la_disequality`'s or-term in the PREMISE's order and
/// reaches the recorded order with `reordering`. Pinned as exact text: the
/// defect this replaces emitted `(cl forward reverse equality) :rule or` from
/// the premise `(or equality forward reverse)`, a positional mismatch carcara
/// rejects outright.
#[test]
fn the_triangle_lowering_unpacks_the_or_in_premise_order() {
    let mut terms = TermStore::new();
    let t = census_triangle(&mut terms);
    let step = triangle_step(vec![t.not_forward, t.not_reverse, t.equality], None);
    let printer = AlethePrinter::new(&terms);
    let text = printer
        .format_step(&step, ProofId(7))
        .expect("the triangle lowers through la_disequality");

    assert_eq!(
        text,
        "(step t7.split (cl (or (= 0 __ay_eqdv!10) (not (<= 0 __ay_eqdv!10)) \
         (not (<= __ay_eqdv!10 0)))) :rule la_disequality)\n\
         (step t7.flat (cl (= 0 __ay_eqdv!10) (not (<= 0 __ay_eqdv!10)) \
         (not (<= __ay_eqdv!10 0))) :rule or :premises (t7.split))\n\
         (step t7 (cl (not (<= 0 __ay_eqdv!10)) (not (<= __ay_eqdv!10 0)) \
         (= 0 __ay_eqdv!10)) :rule reordering :premises (t7.flat))",
        "unexpected lowering:\n{text}"
    );
}

/// Every rule the lowering names is one the pinned checker implements, and
/// none of them is the honest-but-unchecked `hole`. This is what makes the
/// permutation worth recognizing at all: the alternative wire for these
/// clauses is a hole.
#[test]
fn every_rule_in_the_triangle_lowering_is_externally_checkable() {
    let mut terms = TermStore::new();
    let t = census_triangle(&mut terms);
    let step = triangle_step(vec![t.not_forward, t.not_reverse, t.equality], None);
    let printer = AlethePrinter::new(&terms);
    let text = printer
        .format_step(&step, ProofId(7))
        .expect("the triangle lowers through la_disequality");

    let rules: Vec<&str> = text
        .split(":rule ")
        .skip(1)
        .map(|tail| {
            tail.split(|c: char| c.is_whitespace() || c == ')')
                .next()
                .unwrap_or("")
        })
        .collect();
    assert_eq!(rules, vec!["la_disequality", "or", "reordering"]);
    for rule in rules {
        assert!(
            ay_core::is_checkable_alethe_rule(rule),
            "{rule} must be a rule the pinned checker implements"
        );
    }
    assert!(
        !text.contains(ay_core::UNPROVED_STEP_RULE),
        "this kind must never fall back to a hole:\n{text}"
    );
}

/// A stale positional certificate must not reach the wire on a kind whose
/// validator never consumed it: `la_disequality` takes no `:args`, so a
/// `farkas` payload on this step is silently irrelevant and must not be
/// printed as rule arguments.
#[test]
fn a_farkas_payload_cannot_reach_the_triangle_wire() {
    let mut terms = TermStore::new();
    let t = census_triangle(&mut terms);
    let farkas = FarkasAnnotation::new(vec![
        Rational64::new(9, 1),
        Rational64::new(9, 1),
        Rational64::new(9, 1),
    ]);
    let step = triangle_step(vec![t.not_forward, t.not_reverse, t.equality], Some(farkas));
    let printer = AlethePrinter::new(&terms);
    let text = printer
        .format_step(&step, ProofId(7))
        .expect("the triangle lowers through la_disequality");
    assert!(
        !text.contains(":args"),
        "no rule in this lowering takes arguments:\n{text}"
    );
}
