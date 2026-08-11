// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the independent symbolic word-identity checkers.
//!
//! Two load-bearing properties, mirroring `string_length_identity_tests`:
//!
//! 1. A genuine universally-valid identity (self-containment, self-prefix,
//!    self-suffix, `str.<=` reflexivity, `str.<` irreflexivity, empty-word
//!    containment, and free-monoid cancellation on either side) is ACCEPTED.
//! 2. Every NEAR-MISS is REJECTED — two different subjects, the wrong argument
//!    position for the empty word, a flipped polarity, a cancelled block that
//!    is not syntactically identical, a cancelled block at the wrong end, and a
//!    conclusion that does not match the residual.

use super::*;
use ay_core::{ProofId, Sort, Symbol, TermId, TermStore};

fn v(terms: &mut TermStore, name: &str) -> TermId {
    terms.mk_var(name, Sort::String)
}
fn sc(terms: &mut TermStore, s: &str) -> TermId {
    terms.mk_string(s.to_string())
}
fn concat(terms: &mut TermStore, xs: &[TermId]) -> TermId {
    terms.mk_app(Symbol::named("str.++"), xs, Sort::String)
}
fn eq(terms: &mut TermStore, a: TermId, b: TermId) -> TermId {
    terms.mk_app(Symbol::named("="), [a, b], Sort::Bool)
}
fn pred(terms: &mut TermStore, name: &str, a: TermId, b: TermId) -> TermId {
    terms.mk_app(Symbol::named(name), [a, b], Sort::Bool)
}
fn not(terms: &mut TermStore, a: TermId) -> TermId {
    terms.mk_not_raw(a)
}

// ---------------------------------------------------------------------------
// Containment / order identities
// ---------------------------------------------------------------------------

fn accept_identity(terms: &TermStore, t: TermId, why: &str) {
    assert!(
        recognize_string_containment_identity(terms, &[t]),
        "recognizer should ACCEPT: {why}"
    );
    validate_string_containment_identity(terms, ProofId(0), &[t])
        .unwrap_or_else(|e| panic!("strict validation must accept {why}: {e}"));
}

fn reject_identity(terms: &TermStore, t: TermId, why: &str) {
    assert!(
        !recognize_string_containment_identity(terms, &[t]),
        "recognizer should REJECT: {why}"
    );
    assert!(
        validate_string_containment_identity(terms, ProofId(0), &[t]).is_err(),
        "strict validation must reject {why}"
    );
}

#[test]
fn self_containment_identities_are_accepted() {
    let mut terms = TermStore::new();
    let x = v(&mut terms, "x");
    for name in ["str.contains", "str.prefixof", "str.suffixof", "str.<="] {
        let lit = pred(&mut terms, name, x, x);
        accept_identity(&terms, lit, name);
    }
    let strict = pred(&mut terms, "str.<", x, x);
    let irreflexive = not(&mut terms, strict);
    accept_identity(&terms, irreflexive, "(not (str.< x x))");
}

#[test]
fn empty_word_containment_identities_are_accepted() {
    let mut terms = TermStore::new();
    let x = v(&mut terms, "x");
    let empty = sc(&mut terms, "");
    let contains_empty = pred(&mut terms, "str.contains", x, empty);
    accept_identity(&terms, contains_empty, "(str.contains x \"\")");
    let prefix_empty = pred(&mut terms, "str.prefixof", empty, x);
    accept_identity(&terms, prefix_empty, "(str.prefixof \"\" x)");
    let suffix_empty = pred(&mut terms, "str.suffixof", empty, x);
    accept_identity(&terms, suffix_empty, "(str.suffixof \"\" x)");
}

#[test]
fn distinct_subjects_are_rejected() {
    let mut terms = TermStore::new();
    let x = v(&mut terms, "x");
    let y = v(&mut terms, "y");
    for name in ["str.contains", "str.prefixof", "str.suffixof", "str.<="] {
        let lit = pred(&mut terms, name, x, y);
        reject_identity(&terms, lit, &format!("{name} over two DIFFERENT subjects"));
    }
    let strict = pred(&mut terms, "str.<", x, y);
    let negated = not(&mut terms, strict);
    reject_identity(&terms, negated, "(not (str.< x y))");
}

#[test]
fn wrong_empty_word_position_is_rejected() {
    let mut terms = TermStore::new();
    let x = v(&mut terms, "x");
    let empty = sc(&mut terms, "");
    // `(str.contains "" x)` says the EMPTY word contains `x` — false for any
    // non-empty `x`. The container/contained positions are not interchangeable.
    let backwards = pred(&mut terms, "str.contains", empty, x);
    reject_identity(&terms, backwards, "(str.contains \"\" x)");
    // `(str.prefixof x "")` says `x` is a prefix of the empty word.
    let prefix_backwards = pred(&mut terms, "str.prefixof", x, empty);
    reject_identity(&terms, prefix_backwards, "(str.prefixof x \"\")");
    let suffix_backwards = pred(&mut terms, "str.suffixof", x, empty);
    reject_identity(&terms, suffix_backwards, "(str.suffixof x \"\")");
}

#[test]
fn flipped_polarities_are_rejected() {
    let mut terms = TermStore::new();
    let x = v(&mut terms, "x");
    // `(not (str.contains x x))` is the NEGATION of the theorem.
    for name in ["str.contains", "str.prefixof", "str.suffixof", "str.<="] {
        let lit = pred(&mut terms, name, x, x);
        let negated = not(&mut terms, lit);
        reject_identity(&terms, negated, &format!("(not ({name} x x))"));
    }
    // `(str.< x x)` positively asserts a strict order on one word.
    let strict = pred(&mut terms, "str.<", x, x);
    reject_identity(&terms, strict, "(str.< x x)");
}

#[test]
fn non_string_and_non_predicate_shapes_are_rejected() {
    let mut terms = TermStore::new();
    let x = v(&mut terms, "x");
    let b = terms.mk_var("b", Sort::Bool);
    // A same-named application over non-String arguments is not this theorem.
    let bool_contains = pred(&mut terms, "str.contains", b, b);
    reject_identity(&terms, bool_contains, "str.contains over Bool arguments");
    // An unrelated predicate over the same term is not licensed.
    let unrelated = pred(&mut terms, "str.in_re", x, x);
    reject_identity(&terms, unrelated, "an unrelated binary predicate");
    // A plain equality is not a containment identity, even reflexive.
    let reflexive_eq = eq(&mut terms, x, x);
    reject_identity(&terms, reflexive_eq, "(= x x)");
}

// ---------------------------------------------------------------------------
// Free-monoid cancellation
// ---------------------------------------------------------------------------

fn accept_cancellation(terms: &TermStore, clause: &[TermId], why: &str) {
    assert!(
        recognize_string_concat_cancellation(terms, clause),
        "recognizer should ACCEPT: {why}"
    );
    validate_string_concat_cancellation(terms, ProofId(0), clause)
        .unwrap_or_else(|e| panic!("strict validation must accept {why}: {e}"));
}

fn reject_cancellation(terms: &TermStore, clause: &[TermId], why: &str) {
    assert!(
        !recognize_string_concat_cancellation(terms, clause),
        "recognizer should REJECT: {why}"
    );
    assert!(
        validate_string_concat_cancellation(terms, ProofId(0), clause).is_err(),
        "strict validation must reject {why}"
    );
}

#[test]
fn right_cancellation_is_accepted() {
    let mut terms = TermStore::new();
    let x = v(&mut terms, "x");
    let y = v(&mut terms, "y");
    let c = sc(&mut terms, "c");
    let left = concat(&mut terms, &[x, c]);
    let right = concat(&mut terms, &[y, c]);
    let premise = eq(&mut terms, left, right);
    let negated = not(&mut terms, premise);
    let conclusion = eq(&mut terms, x, y);
    accept_cancellation(&terms, &[negated, conclusion], "x·c = y·c => x = y");
    // Clause order is immaterial.
    accept_cancellation(&terms, &[conclusion, negated], "reversed clause order");
}

#[test]
fn left_cancellation_is_accepted() {
    let mut terms = TermStore::new();
    let x = v(&mut terms, "x");
    let y = v(&mut terms, "y");
    let a = sc(&mut terms, "a");
    let left = concat(&mut terms, &[a, x]);
    let right = concat(&mut terms, &[a, y]);
    let premise = eq(&mut terms, left, right);
    let negated = not(&mut terms, premise);
    let conclusion = eq(&mut terms, x, y);
    accept_cancellation(&terms, &[negated, conclusion], "a·x = a·y => x = y");
}

#[test]
fn multi_operand_residual_is_accepted() {
    let mut terms = TermStore::new();
    let x = v(&mut terms, "x");
    let y = v(&mut terms, "y");
    let z = v(&mut terms, "z");
    let w = v(&mut terms, "w");
    let left = concat(&mut terms, &[x, y, w]);
    let right = concat(&mut terms, &[z, w]);
    let premise = eq(&mut terms, left, right);
    let negated = not(&mut terms, premise);
    let residual = concat(&mut terms, &[x, y]);
    let conclusion = eq(&mut terms, residual, z);
    accept_cancellation(&terms, &[negated, conclusion], "x·y·w = z·w => x·y = z");
}

#[test]
fn empty_residual_is_accepted() {
    let mut terms = TermStore::new();
    let x = v(&mut terms, "x");
    let w = v(&mut terms, "w");
    let empty = sc(&mut terms, "");
    let left = concat(&mut terms, &[x, w]);
    let premise = eq(&mut terms, left, w);
    let negated = not(&mut terms, premise);
    let conclusion = eq(&mut terms, x, empty);
    accept_cancellation(&terms, &[negated, conclusion], "x·w = w => x = \"\"");
}

#[test]
fn unshared_block_is_rejected() {
    let mut terms = TermStore::new();
    let x = v(&mut terms, "x");
    let y = v(&mut terms, "y");
    let c = sc(&mut terms, "c");
    let d = sc(&mut terms, "d");
    // `x·c = y·d` does NOT give `x = y` — the cancelled block must be the same
    // word on both sides.
    let left = concat(&mut terms, &[x, c]);
    let right = concat(&mut terms, &[y, d]);
    let premise = eq(&mut terms, left, right);
    let negated = not(&mut terms, premise);
    let conclusion = eq(&mut terms, x, y);
    reject_cancellation(&terms, &[negated, conclusion], "x·c = y·d => x = y");
}

#[test]
fn cancelling_at_the_wrong_end_is_rejected() {
    let mut terms = TermStore::new();
    let x = v(&mut terms, "x");
    let y = v(&mut terms, "y");
    let c = sc(&mut terms, "c");
    // `c·x = y·c` shares `c` but at OPPOSITE ends; nothing cancels.
    let left = concat(&mut terms, &[c, x]);
    let right = concat(&mut terms, &[y, c]);
    let premise = eq(&mut terms, left, right);
    let negated = not(&mut terms, premise);
    let conclusion = eq(&mut terms, x, y);
    reject_cancellation(&terms, &[negated, conclusion], "c·x = y·c => x = y");
}

#[test]
fn mismatched_conclusion_is_rejected() {
    let mut terms = TermStore::new();
    let x = v(&mut terms, "x");
    let y = v(&mut terms, "y");
    let z = v(&mut terms, "z");
    let c = sc(&mut terms, "c");
    let left = concat(&mut terms, &[x, c]);
    let right = concat(&mut terms, &[y, c]);
    let premise = eq(&mut terms, left, right);
    let negated = not(&mut terms, premise);
    // The residuals are `x` and `y`; concluding anything about `z` is forged.
    let conclusion = eq(&mut terms, x, z);
    reject_cancellation(&terms, &[negated, conclusion], "conclusion mentions z");
}

#[test]
fn wrong_clause_shape_is_rejected() {
    let mut terms = TermStore::new();
    let x = v(&mut terms, "x");
    let y = v(&mut terms, "y");
    let c = sc(&mut terms, "c");
    let left = concat(&mut terms, &[x, c]);
    let right = concat(&mut terms, &[y, c]);
    let premise = eq(&mut terms, left, right);
    let negated = not(&mut terms, premise);
    let conclusion = eq(&mut terms, x, y);
    let extra = pred(&mut terms, "str.contains", x, y);
    // Three literals is not the two-literal cancellation theorem: a third
    // literal would let an arbitrary claim ride along.
    reject_cancellation(
        &terms,
        &[negated, conclusion, extra],
        "a three-literal clause",
    );
    // Both literals positive: the premise is asserted, not discharged.
    reject_cancellation(&terms, &[premise, conclusion], "an unnegated premise");
    // Both literals negated: no conclusion at all.
    let negated_conclusion = not(&mut terms, conclusion);
    reject_cancellation(
        &terms,
        &[negated, negated_conclusion],
        "a negated conclusion",
    );
    // The bare unit premise is not a theorem.
    reject_cancellation(&terms, &[negated], "a unit clause");
}

#[test]
fn reflexive_premise_does_not_licence_an_arbitrary_conclusion() {
    let mut terms = TermStore::new();
    let x = v(&mut terms, "x");
    let y = v(&mut terms, "y");
    let c = sc(&mut terms, "c");
    // `(not (= t t))` is FALSE, so the clause reduces to its conclusion. A
    // checker that cancelled the shared block down to nothing and then ignored
    // the residual would licence `(= x y)` out of thin air.
    let t = concat(&mut terms, &[x, c]);
    let premise = eq(&mut terms, t, t);
    let negated = not(&mut terms, premise);
    let conclusion = eq(&mut terms, x, y);
    reject_cancellation(
        &terms,
        &[negated, conclusion],
        "a reflexive premise with an unrelated conclusion",
    );
}

#[test]
fn empty_and_non_bool_clauses_are_rejected() {
    let mut terms = TermStore::new();
    let x = v(&mut terms, "x");
    assert!(validate_string_containment_identity(&terms, ProofId(0), &[]).is_err());
    assert!(validate_string_concat_cancellation(&terms, ProofId(0), &[]).is_err());
    assert!(validate_string_ground_factor_conflict(&terms, ProofId(0), &[]).is_err());
    assert!(!recognize_string_containment_identity(&terms, &[]));
    assert!(!recognize_string_concat_cancellation(&terms, &[]));
    assert!(!recognize_string_ground_factor_conflict(&terms, &[]));
    // A String-sorted literal is not propositional.
    assert!(validate_string_containment_identity(&terms, ProofId(0), &[x]).is_err());
    assert!(validate_string_concat_cancellation(&terms, ProofId(0), &[x]).is_err());
    assert!(validate_string_ground_factor_conflict(&terms, ProofId(0), &[x]).is_err());
}

// ---------------------------------------------------------------------------
// Ground-factor conflicts
// ---------------------------------------------------------------------------

fn accept_conflict(terms: &TermStore, t: TermId, why: &str) {
    assert!(
        recognize_string_ground_factor_conflict(terms, &[t]),
        "recognizer should ACCEPT: {why}"
    );
    validate_string_ground_factor_conflict(terms, ProofId(0), &[t])
        .unwrap_or_else(|e| panic!("strict validation must accept {why}: {e}"));
}

fn reject_conflict(terms: &TermStore, t: TermId, why: &str) {
    assert!(
        !recognize_string_ground_factor_conflict(terms, &[t]),
        "recognizer should REJECT: {why}"
    );
    assert!(
        validate_string_ground_factor_conflict(terms, ProofId(0), &[t]).is_err(),
        "strict validation must reject {why}"
    );
}

#[test]
fn missing_ground_factor_refutes_containment() {
    let mut terms = TermStore::new();
    let x = v(&mut terms, "x");
    let y = v(&mut terms, "y");
    let ab = sc(&mut terms, "ab");
    let c = sc(&mut terms, "c");
    // "c" does not occur in "ab", so no value of `x` makes `x·"c"` a factor.
    let contained = concat(&mut terms, &[x, c]);
    let lit = pred(&mut terms, "str.contains", ab, contained);
    let negated = not(&mut terms, lit);
    accept_conflict(
        &terms,
        negated,
        "(not (str.contains \"ab\" (str.++ x \"c\")))",
    );
    // The ground block may sit anywhere in the chain.
    let middle = concat(&mut terms, &[x, c, y]);
    let lit = pred(&mut terms, "str.contains", ab, middle);
    let negated = not(&mut terms, lit);
    accept_conflict(&terms, negated, "ground block in the middle of the chain");
}

#[test]
fn present_ground_factor_is_rejected() {
    let mut terms = TermStore::new();
    let x = v(&mut terms, "x");
    let ab = sc(&mut terms, "ab");
    let b = sc(&mut terms, "b");
    // "b" DOES occur in "ab" (x = "a" satisfies it), so nothing is refuted.
    let contained = concat(&mut terms, &[x, b]);
    let lit = pred(&mut terms, "str.contains", ab, contained);
    let negated = not(&mut terms, lit);
    reject_conflict(
        &terms,
        negated,
        "(not (str.contains \"ab\" (str.++ x \"b\")))",
    );
    // The empty block is a factor of everything and licences nothing.
    let empty = sc(&mut terms, "");
    let with_empty = concat(&mut terms, &[x, empty]);
    let lit = pred(&mut terms, "str.contains", ab, with_empty);
    let negated = not(&mut terms, lit);
    reject_conflict(&terms, negated, "an empty ground block");
}

#[test]
fn symbolic_container_is_rejected() {
    let mut terms = TermStore::new();
    let x = v(&mut terms, "x");
    let y = v(&mut terms, "y");
    let c = sc(&mut terms, "c");
    // A symbolic container tells the checker nothing: `y` may well contain "c".
    let contained = concat(&mut terms, &[x, c]);
    let lit = pred(&mut terms, "str.contains", y, contained);
    let negated = not(&mut terms, lit);
    reject_conflict(&terms, negated, "a symbolic container");
}

#[test]
fn boundary_block_conflicts_refute_prefix_and_suffix() {
    let mut terms = TermStore::new();
    let x = v(&mut terms, "x");
    let b = sc(&mut terms, "b");
    let c = sc(&mut terms, "c");
    let ab = sc(&mut terms, "ab");
    let bc = sc(&mut terms, "bc");
    // `(str.suffixof "c" (str.++ x "b"))`: the last character is "b".
    let container = concat(&mut terms, &[x, b]);
    let lit = pred(&mut terms, "str.suffixof", c, container);
    let negated = not(&mut terms, lit);
    accept_conflict(&terms, negated, "(str.suffixof \"c\" (str.++ x \"b\"))");
    // `(str.suffixof "bc" (str.++ x "ab"))`: the last two characters are "ab".
    let container = concat(&mut terms, &[x, ab]);
    let lit = pred(&mut terms, "str.suffixof", bc, container);
    let negated = not(&mut terms, lit);
    accept_conflict(&terms, negated, "(str.suffixof \"bc\" (str.++ x \"ab\"))");
    // `(str.prefixof "c" (str.++ "b" x))`: the first character is "b".
    let container = concat(&mut terms, &[b, x]);
    let lit = pred(&mut terms, "str.prefixof", c, container);
    let negated = not(&mut terms, lit);
    accept_conflict(&terms, negated, "(str.prefixof \"c\" (str.++ \"b\" x))");
}

#[test]
fn boundary_pattern_longer_than_the_ground_block_is_rejected() {
    let mut terms = TermStore::new();
    let x = v(&mut terms, "x");
    let b = sc(&mut terms, "b");
    let ab = sc(&mut terms, "ab");
    // `(str.suffixof "ab" (str.++ x "b"))` is SATISFIABLE at x = "a": the
    // pattern reaches past the ground block, so the block alone decides
    // nothing.
    let container = concat(&mut terms, &[x, b]);
    let lit = pred(&mut terms, "str.suffixof", ab, container);
    let negated = not(&mut terms, lit);
    reject_conflict(&terms, negated, "a pattern longer than the ground block");
    // The agreeing case is not refuted either.
    let agreeing = pred(&mut terms, "str.suffixof", b, container);
    let negated = not(&mut terms, agreeing);
    reject_conflict(&terms, negated, "a pattern that matches the ground block");
    // A symbolic boundary block decides nothing.
    let symbolic = concat(&mut terms, &[b, x]);
    let lit = pred(&mut terms, "str.suffixof", b, symbolic);
    let negated = not(&mut terms, lit);
    reject_conflict(&terms, negated, "a symbolic trailing block");
}

#[test]
fn positive_polarity_is_rejected() {
    let mut terms = TermStore::new();
    let x = v(&mut terms, "x");
    let ab = sc(&mut terms, "ab");
    let c = sc(&mut terms, "c");
    let contained = concat(&mut terms, &[x, c]);
    // The theorem is the NEGATION. Asserting the containment positively is the
    // false claim, and must never be accepted.
    let lit = pred(&mut terms, "str.contains", ab, contained);
    reject_conflict(&terms, lit, "the unnegated containment");
}
