// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The admission closer's COMPLEMENT, and why it is not `mk_not`.
//!
//! [`super::close_congruence_derivation`] turns a planned fragment into a
//! self-contained refutation so `check_proof_strict` can replay it: assume the
//! negation of each literal of the fragment's own conclusion, resolve it away,
//! finish on the empty clause. That closing resolution is SYNTACTIC, so the
//! assumed term has to be the literal's exact complement.
//!
//! `mk_not` is that complement for the literal shapes the closer was written
//! for — it wraps a positive literal and cancels the wrapper off a negative
//! one. It is NOT the complement for a literal that is itself an `and`/`or`,
//! because it returns the De Morgan DUAL. Measured on
//! `soundness_qf_uf_incremental/clearsy_0000_00307_falsesat13`: closing the
//! unit `(cl (or (= (bool p) (bool q)) (not (= p q))))` assumed
//! `(and (= p q) (not (= (bool p) (bool q))))` and the strict checker answered
//! `step t7 has invalid resolution derivation` — a false DECLINE of a fragment
//! every one of whose own steps replays.
//!
//! The direction of the fix matters and is pinned below: a wrong complement
//! can only make the closing resolution FAIL, so it can only ever decline a
//! fragment. It can never admit one — every step of the derivation is
//! validated by the untouched strict checker either way, which
//! `an_invalid_derivation_is_still_refused_when_it_closes` checks directly.

use super::CongruenceDerivation;
use crate::quality::check_proof_strict;
use ay_core::{AletheRule, ProofId, ProofStep, Sort, Symbol, TermId, TermStore};

fn var(terms: &mut TermStore, name: &str) -> TermId {
    terms.mk_var(name, Sort::Uninterpreted("U".to_string()))
}

fn eq(terms: &mut TermStore, lhs: TermId, rhs: TermId) -> TermId {
    terms.mk_app(Symbol::named("="), vec![lhs, rhs], Sort::Bool)
}

/// The term the closer assumes for a one-literal conclusion.
fn assumed_complement(terms: &mut TermStore, literal: TermId) -> TermId {
    let derivation = CongruenceDerivation {
        steps: vec![ProofStep::Step {
            rule: AletheRule::Trust,
            clause: vec![literal],
            premises: Vec::new(),
            args: Vec::new(),
        }],
        clause: vec![literal],
    };
    let closed = super::close_congruence_derivation(terms, &derivation);
    let Some(ProofStep::Assume(term)) = closed.steps.get(1) else {
        panic!("the closer assumes the complement immediately after the fragment");
    };
    *term
}

#[test]
fn a_positive_literal_is_closed_under_one_not_wrapper() {
    let mut terms = TermStore::new();
    let a = var(&mut terms, "a");
    let b = var(&mut terms, "b");
    let literal = eq(&mut terms, a, b);
    let complement = assumed_complement(&mut terms, literal);
    assert!(
        matches!(terms.get(complement), ay_core::TermData::Not(inner) if *inner == literal),
        "a positive literal closes under exactly one Not"
    );
}

#[test]
fn a_negated_literal_still_closes_under_the_cancelled_form() {
    let mut terms = TermStore::new();
    let a = var(&mut terms, "a");
    let b = var(&mut terms, "b");
    let equality = eq(&mut terms, a, b);
    let literal = terms.mk_not_raw(equality);
    let complement = assumed_complement(&mut terms, literal);
    assert_eq!(
        complement, equality,
        "a negated literal closes against the term inside it, not (not (not x))"
    );
}

/// The regression this file exists for: a DISJUNCTION literal must close under
/// a raw `Not`, never under its De Morgan dual.
#[test]
fn a_disjunction_literal_closes_under_a_raw_not_and_not_its_de_morgan_dual() {
    let mut terms = TermStore::new();
    let a = var(&mut terms, "a");
    let b = var(&mut terms, "b");
    let c = var(&mut terms, "c");
    let left = eq(&mut terms, a, b);
    let right = eq(&mut terms, b, c);
    let disjunction = terms.mk_app(Symbol::named("or"), vec![left, right], Sort::Bool);
    let complement = assumed_complement(&mut terms, disjunction);
    assert!(
        matches!(terms.get(complement), ay_core::TermData::Not(inner) if *inner == disjunction),
        "a disjunction closes under exactly one Not"
    );
    // And the shape it must NOT be: `mk_not` pushes the negation through `or`.
    let de_morgan = terms.mk_not(disjunction);
    assert_ne!(
        complement, de_morgan,
        "the De Morgan dual is Boolean-equivalent but is not a resolution \
         complement; the closing step is refused against it"
    );
    assert!(
        matches!(terms.get(de_morgan),
            ay_core::TermData::App(Symbol::Named(name), _) if name == "and"),
        "the fixture depends on mk_not producing the `and` dual here"
    );
}

/// End to end: a RE-PACK fragment — a congruence flattened, then rebuilt into
/// the packed unit by `or_neg` — closes and replays under the untouched strict
/// checker.
#[test]
fn a_repacked_congruence_fragment_closes_and_strict_checks() {
    let mut terms = TermStore::new();
    let sort = Sort::Uninterpreted("U".to_string());
    let a = var(&mut terms, "a");
    let b = var(&mut terms, "b");
    let fa = terms.mk_app(Symbol::named("f"), vec![a], sort.clone());
    let fb = terms.mk_app(Symbol::named("f"), vec![b], sort);
    let eq_ab = eq(&mut terms, a, b);
    let not_ab = terms.mk_not_raw(eq_ab);
    let eq_fab = eq(&mut terms, fa, fb);
    let not_fab = terms.mk_not_raw(eq_fab);
    let packed = terms.mk_app(Symbol::named("or"), vec![eq_fab, not_ab], Sort::Bool);

    let steps = vec![
        // t0 — the congruence, flat.
        ProofStep::Step {
            rule: AletheRule::EqCongruent,
            clause: vec![not_ab, eq_fab],
            premises: Vec::new(),
            args: Vec::new(),
        },
        // t1/t2 — resolve the first disjunct into the packed unit.
        ProofStep::Step {
            rule: AletheRule::OrNeg,
            clause: vec![packed, not_fab],
            premises: Vec::new(),
            args: Vec::new(),
        },
        ProofStep::Step {
            rule: AletheRule::ThResolution,
            clause: vec![not_ab, packed],
            premises: vec![ProofId(0), ProofId(1)],
            args: Vec::new(),
        },
        // t3/t4 — and the second.
        ProofStep::Step {
            rule: AletheRule::OrNeg,
            clause: vec![packed, eq_ab],
            premises: Vec::new(),
            args: Vec::new(),
        },
        ProofStep::Step {
            rule: AletheRule::ThResolution,
            clause: vec![packed],
            premises: vec![ProofId(2), ProofId(3)],
            args: Vec::new(),
        },
    ];
    let derivation = CongruenceDerivation {
        steps,
        clause: vec![packed],
    };
    let closed = super::close_congruence_derivation(&mut terms, &derivation);
    check_proof_strict(&closed, &terms)
        .expect("every step of a re-packed congruence fragment must replay");
}

/// The direction the closer's change can NOT go: an invalid derivation that
/// closes cleanly is still REFUSED, because every step of it is replayed.
///
/// The fixture claims `(cl (or (= a b) (= b c)))` from nothing, with the same
/// `or_neg` scaffolding as the valid fragment above but a `trust`-free lie in
/// place of the congruence: `eq_transitive` over two literals that are not a
/// transitivity. Falsifying assignment, CHECKED below: `a`, `b` and `c` in
/// three different classes makes both disjuncts false, so the claimed unit is
/// FALSE and no sound derivation of it exists.
#[test]
fn an_invalid_derivation_is_still_refused_when_it_closes() {
    let mut terms = TermStore::new();
    let a = var(&mut terms, "a");
    let b = var(&mut terms, "b");
    let c = var(&mut terms, "c");
    let eq_ab = eq(&mut terms, a, b);
    let eq_bc = eq(&mut terms, b, c);
    let packed = terms.mk_app(Symbol::named("or"), vec![eq_ab, eq_bc], Sort::Bool);
    // The falsifying assignment is three distinct classes: the three variables
    // are distinct terms and no hypothesis relates them.
    assert!(a != b && b != c && a != c);
    let derivation = CongruenceDerivation {
        steps: vec![ProofStep::Step {
            rule: AletheRule::EqTransitive,
            clause: vec![eq_ab, eq_bc],
            premises: Vec::new(),
            args: Vec::new(),
        }],
        clause: vec![eq_ab, eq_bc],
    };
    let closed = super::close_congruence_derivation(&mut terms, &derivation);
    assert!(
        check_proof_strict(&closed, &terms).is_err(),
        "a false clause must be refused however cleanly the closer closes it"
    );
    // And the same lie repacked into the unit is refused too.
    let repacked = CongruenceDerivation {
        steps: vec![
            ProofStep::Step {
                rule: AletheRule::EqTransitive,
                clause: vec![eq_ab, eq_bc],
                premises: Vec::new(),
                args: Vec::new(),
            },
            ProofStep::Step {
                rule: AletheRule::OrNeg,
                clause: vec![packed, terms.mk_not_raw(eq_ab)],
                premises: Vec::new(),
                args: Vec::new(),
            },
            ProofStep::Step {
                rule: AletheRule::ThResolution,
                clause: vec![eq_bc, packed],
                premises: vec![ProofId(0), ProofId(1)],
                args: Vec::new(),
            },
        ],
        clause: vec![eq_bc, packed],
    };
    let closed = super::close_congruence_derivation(&mut terms, &repacked);
    assert!(
        check_proof_strict(&closed, &terms).is_err(),
        "re-packing a false clause must not launder it"
    );
}
