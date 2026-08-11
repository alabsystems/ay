// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A shape rule must try EVERY candidate literal, not just the first one.
//!
//! `validate_equiv_*`, `validate_ite_*` and `validate_xor_*` all begin by
//! locating the literal the rule is "about" — the equality, the ite, the xor.
//! They did that with `find_negated_app` / `find_app` / `find_ite` /
//! `find_negated_ite`, each of which returns the FIRST matching literal and
//! never backtracks.
//!
//! That is only safe if the target literal is the sole candidate. It is not,
//! whenever an operand is itself a term of the same shape: `equiv_pos1` over
//! `(= a (= p q))` emits the clause `(cl (not (= a (= p q))) a (not (= p q)))`,
//! which contains TWO literals of the form `(not (= ...))`. Nothing pins the
//! order — `clause_matches_expected` is deliberately unordered, precisely
//! because emitters do not agree on one — so when the decoy comes first the
//! rule decodes the wrong equality, the shape check fails, and a correct
//! `unsat` is published as `unknown`.
//!
//! Trying every candidate is not a relaxation. Each candidate still has to
//! satisfy the rule's complete shape predicate; the only thing that changes is
//! that a failure on one candidate no longer suppresses the others. The
//! rejecting-direction tests below hold that line: a clause built from decoys
//! with NO valid candidate must still be refused.

use crate::checker::*;
use ay_core::{AletheRule, ProofId, ProofStep, Sort, Symbol, TermId, TermStore};

fn eq(terms: &mut TermStore, lhs: TermId, rhs: TermId) -> TermId {
    terms.mk_app(Symbol::named("="), vec![lhs, rhs], Sort::Bool)
}

fn xor(terms: &mut TermStore, lhs: TermId, rhs: TermId) -> TermId {
    terms.mk_app(Symbol::named("xor"), vec![lhs, rhs], Sort::Bool)
}

fn boolvar(terms: &mut TermStore, name: &str) -> TermId {
    terms.mk_var(name, Sort::Bool)
}

fn intvar(terms: &mut TermStore, name: &str) -> TermId {
    terms.mk_var(name, Sort::Int)
}

fn validate(
    terms: &TermStore,
    rule: AletheRule,
    clause: Vec<TermId>,
) -> Result<(), ProofCheckError> {
    let step = ProofStep::Step {
        rule,
        clause,
        premises: vec![],
        args: vec![],
    };
    let mut derived: Vec<Option<Vec<TermId>>> = vec![];
    validate_step(terms, &mut derived, ProofId(0), &step, true, None)
}

// ---- equiv ----

/// `equiv_pos1` over `(= a (= p q))`, decoy equality listed FIRST.
///
/// The clause is correct: `(not (= a (= p q)))`, `a`, `(not (= p q))`. But
/// `(not (= p q))` is also of the form `(not (= ...))`, so a first-match
/// decode picks it, reads its operands as `p` and `q`, and rejects.
#[test]
fn equiv_pos1_tries_past_a_decoy_equality() {
    let mut terms = TermStore::new();
    let a = boolvar(&mut terms, "a");
    let p = intvar(&mut terms, "p");
    let q = intvar(&mut terms, "q");
    let inner_eq = eq(&mut terms, p, q);
    let outer_eq = eq(&mut terms, a, inner_eq);
    let not_outer = terms.mk_not(outer_eq);
    let not_inner = terms.mk_not(inner_eq);

    assert_ne!(
        not_inner, not_outer,
        "precondition: the decoy and the target must be distinct literals"
    );

    // Decoy first. The rule is order-insensitive by design, so this clause is
    // exactly as valid as the one with the target first.
    validate(&terms, AletheRule::EquivPos1, vec![not_inner, not_outer, a])
        .expect("equiv_pos1 must decode the equality its clause is actually about");
}

/// `equiv_neg1` over `(= (= p q) b)` — positive-equality side, decoy first.
///
/// Shape: `(cl (= (= p q) b) (not (= p q)) (not b))`. Only one literal is a
/// POSITIVE equality here, so the decoy has to be introduced the way real
/// proofs do: the expected literal `(not (= p q))` collapses to a bare
/// equality when the operand is itself negated.
#[test]
fn equiv_neg1_tries_past_a_decoy_equality() {
    let mut terms = TermStore::new();
    let b = boolvar(&mut terms, "b");
    let p = intvar(&mut terms, "p");
    let q = intvar(&mut terms, "q");
    let inner_eq = eq(&mut terms, p, q);
    let not_inner = terms.mk_not(inner_eq);
    let outer_eq = eq(&mut terms, not_inner, b);

    // `(not (not (= p q)))` folds back to `(= p q)`: a second POSITIVE equality
    // in the clause, and the one a first-match decode reaches first.
    let neg_first = terms.mk_not(not_inner);
    assert_eq!(neg_first, inner_eq, "precondition: double negation folds");
    let neg_second = terms.mk_not(b);

    validate(
        &terms,
        AletheRule::EquivNeg1,
        vec![neg_first, outer_eq, neg_second],
    )
    .expect("equiv_neg1 must decode the equality its clause is actually about");
}

/// REJECTING DIRECTION. Two decoys and no valid candidate: still refused.
#[test]
fn equiv_pos1_still_rejects_when_no_candidate_matches() {
    let mut terms = TermStore::new();
    let p = intvar(&mut terms, "p");
    let q = intvar(&mut terms, "q");
    let r = intvar(&mut terms, "r");
    let eq_pq = eq(&mut terms, p, q);
    let eq_qr = eq(&mut terms, q, r);
    let not_pq = terms.mk_not(eq_pq);
    let not_qr = terms.mk_not(eq_qr);
    let c = boolvar(&mut terms, "c");

    validate(&terms, AletheRule::EquivPos1, vec![not_pq, not_qr, c]).expect_err(
        "equiv_pos1 must reject a clause where NO equality candidate yields \
         the rule's shape — trying every candidate must not become a rubber \
         stamp",
    );
}

// ---- xor ----

/// `xor_pos2` over `(xor a (xor p q))`, decoy xor listed first.
///
/// Shape: `(cl (not (xor a (xor p q))) (not a) (not (xor p q)))`.
#[test]
fn xor_pos2_tries_past_a_decoy_xor() {
    let mut terms = TermStore::new();
    let a = boolvar(&mut terms, "a");
    let p = boolvar(&mut terms, "p");
    let q = boolvar(&mut terms, "q");
    let inner = xor(&mut terms, p, q);
    let outer = xor(&mut terms, a, inner);
    let not_outer = terms.mk_not(outer);
    let not_a = terms.mk_not(a);
    let not_inner = terms.mk_not(inner);

    validate(
        &terms,
        AletheRule::XorPos2,
        vec![not_inner, not_outer, not_a],
    )
    .expect("xor_pos2 must decode the xor its clause is actually about");
}

/// REJECTING DIRECTION for xor.
#[test]
fn xor_pos2_still_rejects_when_no_candidate_matches() {
    let mut terms = TermStore::new();
    let a = boolvar(&mut terms, "a");
    let p = boolvar(&mut terms, "p");
    let q = boolvar(&mut terms, "q");
    let x1 = xor(&mut terms, p, q);
    let x2 = xor(&mut terms, q, a);
    let not_x1 = terms.mk_not(x1);
    let not_x2 = terms.mk_not(x2);

    validate(&terms, AletheRule::XorPos2, vec![not_x1, not_x2, a])
        .expect_err("xor_pos2 must still reject a clause with no valid candidate");
}

// ---- ite ----

/// `ite_neg1` over an ite whose CONDITION is itself an ite — a nested Bool ite,
/// which is ordinary in real formulas.
///
/// Shape: `(cl (ite I2 t e) I2 (not e))`. Both the target and the condition are
/// positive ite literals, so `find_ite` has two candidates.
///
/// The `ite_pos*` rules cannot be exercised the same way, and not because they
/// lack the defect: they look for `(not (ite ...))`, and `TermStore::mk_not`
/// pushes negation THROUGH a Bool ite — `(not (ite c t e))` becomes
/// `(ite c (not t) (not e))` (`term/boolean.rs`, "ITE negation normalization").
/// That is a second, separate unconstructible-literal defect, of the same
/// family as the `(not (not X))` one, and it is not what this file pins.
#[test]
fn ite_neg1_tries_past_a_decoy_ite() {
    let mut terms = TermStore::new();
    let c2 = boolvar(&mut terms, "c2");
    let t2 = boolvar(&mut terms, "t2");
    let e2 = boolvar(&mut terms, "e2");
    let t = boolvar(&mut terms, "t");
    let e = boolvar(&mut terms, "e");
    let inner_ite = terms.mk_ite(c2, t2, e2);
    let outer_ite = terms.mk_ite(inner_ite, t, e);
    let not_e = terms.mk_not(e);

    assert_ne!(
        inner_ite, outer_ite,
        "precondition: mk_ite must not collapse either ite"
    );

    // Decoy (the condition) first.
    validate(
        &terms,
        AletheRule::IteNeg1,
        vec![inner_ite, outer_ite, not_e],
    )
    .expect("ite_neg1 must decode the ite its clause is actually about");
}

/// REJECTING DIRECTION for ite.
#[test]
fn ite_neg1_still_rejects_when_no_candidate_matches() {
    let mut terms = TermStore::new();
    let c2 = boolvar(&mut terms, "c2");
    let t2 = boolvar(&mut terms, "t2");
    let e2 = boolvar(&mut terms, "e2");
    let z = boolvar(&mut terms, "z");
    let i1 = terms.mk_ite(c2, t2, e2);
    let i2 = terms.mk_ite(t2, e2, c2);

    validate(&terms, AletheRule::IteNeg1, vec![i1, i2, z])
        .expect_err("ite_neg1 must still reject a clause with no valid candidate");
}
