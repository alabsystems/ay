// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! AY resolution acceptance must be a SUBSET of carcara's (#carcara-subset).
//!
//! Two confirmed shapes where AY once said yes and carcara said no.
//!
//! 1. `:args` were not validated. `checker/mod.rs` once passed `args.first()`
//!    as an optional pivot hint and the n-ary path ignored even that — but
//!    `alethe_printer::format_external_args` prints a resolution step's
//!    `:args` VERBATIM. So a junk annotation was certified by AY and printed
//!    for carcara to reject. Reproduced against carcara 1.1.0 with hand-built
//!    documents; the carcara text quoted in each test is REAL output, not a
//!    prediction:
//!
//!    ```text
//!    [ERROR] checking failed on step 't4' with rule 'resolution':
//!            expected 4 arguments, got 1
//!    ```
//!
//! 2. De Morgan pairs were treated as resolution complements. AY's `mk_not`
//!    interns `(not (and a b))` AS `(or (not a) (not b))`, and an earlier
//!    `are_complements` (built on `matches_negation_of_term`) paired the two
//!    back up. carcara resolves on ATOMS and does not:
//!
//!    ```text
//!    [ERROR] checking failed on step 't6' with rule 'resolution':
//!            pivot was not eliminated: '(and a b)'
//!    ```
//!
//!    The resolution checker now normalizes literals by leading-`not` parity
//!    only (`resolution_parity.rs`), so a De Morgan equivalent is a distinct
//!    atom; the tests in the second section pin that down.
//!
//! Every AY emitter passes `Vec::new()` for resolution args (re-audited: 60
//! constructor sites in `ay-dpll`/`ay-proof`, all empty), so the compact
//! `:args`-FREE form must keep passing and every rejecting test below is
//! paired with an accepting one. The malformed shapes are reported as
//! [`ProofCheckError::MalformedResolutionArgs`] — carcara's own count
//! complaint — not as a failed pivot search.

use crate::checker::*;
use ay_core::{AletheRule, Proof, ProofId, Sort, TermId, TermStore};

fn boolvar(terms: &mut TermStore, name: &str) -> TermId {
    terms.mk_var(name, Sort::Bool)
}

/// Run every step of `proof` through the real dispatcher.
fn check(terms: &TermStore, proof: &Proof) -> Result<(), ProofCheckError> {
    let mut derived: Vec<Option<Vec<TermId>>> = vec![];
    for (i, step) in proof.steps.iter().enumerate() {
        validate_step(terms, &mut derived, ProofId(i as u32), step, false, None)?;
    }
    Ok(())
}

/// The canonical valid chain: `{p}`, `{(not p), q}`, `{(not q)}` closing to
/// `(cl)`.
///
/// Returns the store, the proof with its three premise steps already added,
/// and the pivots `(p, q)` so a test can annotate the chain.
fn closing_chain() -> (TermStore, Proof, TermId, TermId) {
    let mut terms = TermStore::new();
    let p = boolvar(&mut terms, "p");
    let q = boolvar(&mut terms, "q");
    let np = terms.mk_not(p);
    let nq = terms.mk_not(q);

    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::Trust, vec![p], Vec::new(), Vec::new());
    proof.add_rule_step(AletheRule::Trust, vec![np, q], Vec::new(), Vec::new());
    proof.add_rule_step(AletheRule::Trust, vec![nq], Vec::new(), Vec::new());
    (terms, proof, p, q)
}

fn add_chain(proof: &mut Proof, clause: Vec<TermId>, args: Vec<TermId>) {
    proof.add_rule_step(
        AletheRule::ThResolution,
        clause,
        vec![ProofId(0), ProofId(1), ProofId(2)],
        args,
    );
}

// Divergence 1: `:args`
// ---------------------------------------------------------------------------

/// THE REGRESSION GUARD. AY emits chains with NO `:args`; that must not change.
#[test]
fn empty_args_chain_is_still_accepted() {
    let (terms, mut proof, _, _) = closing_chain();
    add_chain(&mut proof, vec![], Vec::new());

    check(&terms, &proof).expect(
        "the argument-free n-ary form is what every AY emitter produces \
         (`Vec::new()` for args) and carcara checks it as `valid`",
    );
}

/// The exact shape the review reported: a valid chain carrying a JUNK `:args`.
/// carcara: `expected 4 arguments, got 1`.
#[test]
fn junk_single_arg_on_a_chain_is_rejected() {
    let (terms, mut proof, p, _) = closing_chain();
    add_chain(&mut proof, vec![], vec![p]);

    let err = check(&terms, &proof).expect_err(
        "a 3-premise chain needs 4 arguments; one bare pivot is not an Alethe \
         annotation and carcara refuses the document",
    );
    assert!(
        matches!(
            err,
            ProofCheckError::MalformedResolutionArgs {
                expected: 4,
                got: 1,
                ..
            }
        ),
        "expected a malformed-args rejection, got {err}"
    );
}

/// A pivot WITH a polarity is still only one of the two pairs a 3-premise
/// chain needs. carcara: `expected 4 arguments, got 2`.
#[test]
fn one_complete_pair_on_a_two_link_chain_is_rejected() {
    let (mut terms, mut proof, p, _) = closing_chain();
    let t = terms.mk_bool(true);
    add_chain(&mut proof, vec![], vec![p, t]);

    let err = check(&terms, &proof).expect_err("two links require two pivot/polarity pairs");
    assert!(
        matches!(
            err,
            ProofCheckError::MalformedResolutionArgs {
                expected: 4,
                got: 2,
                ..
            }
        ),
        "expected a malformed-args rejection, got {err}"
    );
}

/// The BINARY path had the same hole — it took `args.first()` as a hint and
/// ignored the missing polarity. carcara: `expected 2 arguments, got 1`.
#[test]
fn junk_single_arg_on_a_binary_step_is_rejected() {
    let mut terms = TermStore::new();
    let p = boolvar(&mut terms, "p");
    let np = terms.mk_not(p);

    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::Trust, vec![p], Vec::new(), Vec::new());
    proof.add_rule_step(AletheRule::Trust, vec![np], Vec::new(), Vec::new());
    proof.add_rule_step(
        AletheRule::ThResolution,
        vec![],
        vec![ProofId(0), ProofId(1)],
        vec![p],
    );

    let err =
        check(&terms, &proof).expect_err("a binary resolution needs a (pivot, polarity) pair");
    assert!(
        matches!(
            err,
            ProofCheckError::MalformedResolutionArgs {
                expected: 2,
                got: 1,
                ..
            }
        ),
        "expected a malformed-args rejection, got {err}"
    );
}

/// ACCEPTING DIRECTION for the new path: a CORRECT annotation still checks.
/// Polarity `true` means the pivot occurs positively in the accumulator —
/// verified against carcara, which reports `pivot was not found in clause`
/// when it is flipped.
#[test]
fn well_formed_pivot_args_are_accepted() {
    let (mut terms, mut proof, p, q) = closing_chain();
    let t = terms.mk_bool(true);
    add_chain(&mut proof, vec![], vec![p, t, q, t]);

    check(&terms, &proof)
        .expect("`:args (p true q true)` names exactly the pivots this chain eliminates");
}

/// REJECTING DIRECTION. The annotation is well-FORMED but names the pivots in
/// the wrong order, so link 1 cannot eliminate `q`. carcara agrees:
/// `pivot was not found in clause: 'q'`.
#[test]
fn correctly_sized_but_wrongly_ordered_pivots_are_rejected() {
    let (mut terms, mut proof, p, q) = closing_chain();
    let t = terms.mk_bool(true);
    add_chain(&mut proof, vec![], vec![q, t, p, t]);

    let err = check(&terms, &proof)
        .expect_err("the first link resolves on `p`, not `q` — the annotation is wrong");
    assert!(
        matches!(err, ProofCheckError::InvalidResolution { .. }),
        "expected an invalid-resolution rejection, got {err}"
    );
}

/// REJECTING DIRECTION. Right pivots, wrong polarity.
#[test]
fn inverted_polarity_is_rejected() {
    let (mut terms, mut proof, p, q) = closing_chain();
    let t = terms.mk_bool(true);
    let f = terms.mk_bool(false);
    add_chain(&mut proof, vec![], vec![p, f, q, t]);

    let err = check(&terms, &proof)
        .expect_err("`p` occurs POSITIVELY in the first premise, so polarity `false` is wrong");
    assert!(
        matches!(err, ProofCheckError::InvalidResolution { .. }),
        "expected an invalid-resolution rejection, got {err}"
    );
}

/// A polarity slot that is not a Boolean constant is not an Alethe annotation.
#[test]
fn non_boolean_polarity_is_rejected() {
    let (terms, mut proof, p, q) = closing_chain();
    add_chain(&mut proof, vec![], vec![p, q, q, p]);

    let err = check(&terms, &proof).expect_err("polarity slots must hold `true` or `false`");
    assert!(
        matches!(err, ProofCheckError::MalformedResolutionArgs { .. }),
        "expected a malformed-args rejection, got {err}"
    );
}

/// Leading-`not` PARITY, the case that makes a naive "strip all negations"
/// pivot rule wrong. `(not (not x))` cancels `(not x)`, and the pivot is the
/// SHALLOWER literal with polarity `false`. carcara checks this exact document
/// as `valid`; it rejects the same step with pivot `x`.
#[test]
fn double_negation_parity_pivot_is_accepted() {
    let mut terms = TermStore::new();
    let x = boolvar(&mut terms, "x");
    let q = boolvar(&mut terms, "q");
    let nx = terms.mk_not(x);
    // `mk_not` COLLAPSES double negation, so build the depth-2 literal raw —
    // that is the only way AY can hold one at all.
    let nnx = terms.mk_not_raw(nx);
    let f = terms.mk_bool(false);

    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::Trust, vec![nnx, q], Vec::new(), Vec::new());
    proof.add_rule_step(AletheRule::Trust, vec![nx], Vec::new(), Vec::new());
    proof.add_rule_step(
        AletheRule::ThResolution,
        vec![q],
        vec![ProofId(0), ProofId(1)],
        vec![nx, f],
    );

    check(&terms, &proof).expect(
        "`(not (not x))` is the syntactic negation of `(not x)`, so pivot \
         `(not x)` with polarity `false` is the annotation carcara accepts",
    );
}

/// Build `{(and a b), (not r)}`, `{(or (not a) (not b)), s}`, `{r}` — the
/// review's example. AY used to fold this to `{s}`; carcara reports
/// `pivot was not eliminated: '(and a b)'`.
fn de_morgan_chain() -> (TermStore, Proof, TermId) {
    let mut terms = TermStore::new();
    let a = boolvar(&mut terms, "a");
    let b = boolvar(&mut terms, "b");
    let r = boolvar(&mut terms, "r");
    let s = boolvar(&mut terms, "s");
    let and_ab = terms.mk_and(vec![a, b]);
    // `mk_not` normalizes this to `(or (not a) (not b))` — that IS how AY
    // spells the negation of a conjunction.
    let or_nanb = terms.mk_not(and_ab);
    let nr = terms.mk_not(r);

    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::Trust, vec![and_ab, nr], Vec::new(), Vec::new());
    proof.add_rule_step(AletheRule::Trust, vec![or_nanb, s], Vec::new(), Vec::new());
    proof.add_rule_step(AletheRule::Trust, vec![r], Vec::new(), Vec::new());
    (terms, proof, s)
}

/// THE SOUNDNESS FIX, chain form. Fails closed: re-derivation is the designed
/// response and is cheaper than shipping a proof carcara rejects.
#[test]
fn de_morgan_pair_is_not_a_chain_resolution_complement() {
    let (terms, mut proof, s) = de_morgan_chain();
    add_chain(&mut proof, vec![s], Vec::new());

    let err = check(&terms, &proof).expect_err(
        "`(and a b)` and `(or (not a) (not b))` are distinct resolution atoms \
         to carcara, which reports `pivot was not eliminated`",
    );
    assert!(
        matches!(err, ProofCheckError::InvalidResolution { .. }),
        "expected an invalid-resolution rejection, got {err}"
    );
}

/// Same divergence through the BINARY path, which reached it via
/// `resolve_on_semantic_pivot`.
#[test]
fn de_morgan_pair_is_not_a_binary_resolution_complement() {
    let mut terms = TermStore::new();
    let a = boolvar(&mut terms, "a");
    let b = boolvar(&mut terms, "b");
    let s = boolvar(&mut terms, "s");
    let and_ab = terms.mk_and(vec![a, b]);
    let or_nanb = terms.mk_not(and_ab);

    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::Trust, vec![and_ab], Vec::new(), Vec::new());
    proof.add_rule_step(AletheRule::Trust, vec![or_nanb, s], Vec::new(), Vec::new());
    proof.add_rule_step(
        AletheRule::ThResolution,
        vec![s],
        vec![ProofId(0), ProofId(1)],
        Vec::new(),
    );

    let err =
        check(&terms, &proof).expect_err("the binary path must not bridge De Morgan forms either");
    assert!(
        matches!(err, ProofCheckError::InvalidResolution { .. }),
        "expected an invalid-resolution rejection, got {err}"
    );
}

/// GUARD AGAINST OVER-TIGHTENING. Narrowing the resolution complement must not
/// disturb ordinary syntactic resolution on the same connectives: an or-term
/// still cancels its own `not`.
#[test]
fn plain_negation_of_an_or_term_still_resolves() {
    let mut terms = TermStore::new();
    let a = boolvar(&mut terms, "a");
    let b = boolvar(&mut terms, "b");
    let s = boolvar(&mut terms, "s");
    let or_ab = terms.mk_or(vec![a, b]);
    // The negation of an OR normalizes to `(and (not a) (not b))`, so take the
    // complementary pair the other way round: a literal and its raw negation.
    let n_or_ab = terms.mk_not_raw(or_ab);

    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::Trust, vec![or_ab], Vec::new(), Vec::new());
    proof.add_rule_step(AletheRule::Trust, vec![n_or_ab, s], Vec::new(), Vec::new());
    proof.add_rule_step(
        AletheRule::ThResolution,
        vec![s],
        vec![ProofId(0), ProofId(1)],
        Vec::new(),
    );

    check(&terms, &proof).expect(
        "`(or a b)` and `(not (or a b))` are a syntactic complementary pair; \
         carcara resolves them and so must AY",
    );
}
