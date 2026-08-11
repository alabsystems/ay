// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! An AMBIGUOUS chain-resolution link must be searched, not refused.
//!
//! `validate_chain_resolution_rule` folded the premises left-to-right and, at
//! each link, demanded a UNIQUE complementary literal pair. Two pairs meant two
//! possible resolvents, and its comment says it "is rejected rather than
//! guessed, since guessing wrong would silently change the accumulated clause".
//!
//! The caution is right; the conclusion is not. Nothing has to be guessed,
//! because the fold is CHECKED at the end — `acc == dedup(clause)`. So the link
//! can branch, and a branch is accepted only if it reaches the clause the step
//! actually declares.
//!
//! That is sound for the same reason binary resolution is: a resolvent is
//! implied by its two premises whatever pivot is chosen, so a chain that ends at
//! the declared clause witnesses that the declared clause follows from the
//! premises. The pivot choice is a search detail; the entailment does not depend
//! on it.
//!
//! The comment also says `:args` could disambiguate. They cannot, here: every
//! n-ary `th_resolution` emitter in `ay-dpll` passes `Vec::new()` for args (see
//! `executor/proof_rewrite_division.rs`), so the pivots simply are not there to
//! read. Searching is the only route that works on AY's own proofs.
//!
//! Cost of getting this wrong: `pushscope_repro` computes a correct `unsat`,
//! the certifier rejects `step t110 has invalid th_resolution derivation`, and
//! the verdict is published as `unknown` — a caught-and-discarded refutation.

use crate::checker::*;
use ay_core::{AletheRule, Proof, ProofId, Sort, TermId, TermStore};

fn boolvar(terms: &mut TermStore, name: &str) -> TermId {
    terms.mk_var(name, Sort::Bool)
}

/// Build a 3-premise chain whose FIRST link is genuinely ambiguous.
///
/// * `t0 = (cl a b)`
/// * `t1 = (cl (not a) (not b) c)`  — complements BOTH `a` and `b`
/// * `t2 = (cl (not c) d)`
///
/// Resolving link 1 on `a` gives `{b, (not b), c}`, then on `c` gives
/// `{b, (not b), d}`. Resolving instead on `b` gives `{a, (not a), d}`. Both
/// are legitimate; which one the step means is fixed by the clause it declares.
fn ambiguous_chain(terms: &mut TermStore) -> (Proof, Vec<TermId>, Vec<TermId>) {
    let a = boolvar(terms, "a");
    let b = boolvar(terms, "b");
    let c = boolvar(terms, "c");
    let d = boolvar(terms, "d");
    let na = terms.mk_not(a);
    let nb = terms.mk_not(b);
    let nc = terms.mk_not(c);

    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::Trust, vec![a, b], Vec::new(), Vec::new());
    proof.add_rule_step(AletheRule::Trust, vec![na, nb, c], Vec::new(), Vec::new());
    proof.add_rule_step(AletheRule::Trust, vec![nc, d], Vec::new(), Vec::new());

    // The two reachable end clauses.
    (proof, vec![b, nb, d], vec![a, na, d])
}

fn check_chain(
    terms: &TermStore,
    proof: &mut Proof,
    clause: Vec<TermId>,
) -> Result<(), ProofCheckError> {
    proof.add_rule_step(
        AletheRule::ThResolution,
        clause,
        vec![ProofId(0), ProofId(1), ProofId(2)],
        Vec::new(),
    );
    let mut derived: Vec<Option<Vec<TermId>>> = vec![];
    for (i, step) in proof.steps.iter().enumerate() {
        validate_step(terms, &mut derived, ProofId(i as u32), step, false, None)?;
    }
    Ok(())
}

#[test]
fn ambiguous_link_resolving_on_the_first_pivot_is_accepted() {
    let mut terms = TermStore::new();
    let (mut proof, via_a, _) = ambiguous_chain(&mut terms);

    check_chain(&terms, &mut proof, via_a).expect(
        "the chain reaches this clause by resolving link 1 on `a`; the fold is \
         verified against the declared clause, so branching is checked, not guessed",
    );
}

#[test]
fn ambiguous_link_resolving_on_the_second_pivot_is_accepted() {
    let mut terms = TermStore::new();
    let (mut proof, _, via_b) = ambiguous_chain(&mut terms);

    check_chain(&terms, &mut proof, via_b)
        .expect("the same chain reaches this clause by resolving link 1 on `b` instead");
}

/// REJECTING DIRECTION — the whole point of the file. Searching the branches
/// must not turn the rule into a rubber stamp: a clause NO branch reaches is
/// still refused.
#[test]
fn a_clause_no_branch_reaches_is_still_rejected() {
    let mut terms = TermStore::new();
    let (mut proof, _, _) = ambiguous_chain(&mut terms);
    let e = boolvar(&mut terms, "e");
    let f = boolvar(&mut terms, "f");

    check_chain(&terms, &mut proof, vec![e, f]).expect_err(
        "no pivot choice resolves this chain to `(cl e f)` — branching must not \
         accept a clause the premises do not yield",
    );
}

/// REJECTING DIRECTION. A chain with a link that resolves on NOTHING is still
/// refused; branching only relaxes uniqueness, never existence.
#[test]
fn a_link_with_no_complementary_pair_is_still_rejected() {
    let mut terms = TermStore::new();
    let a = boolvar(&mut terms, "a");
    let b = boolvar(&mut terms, "b");
    let c = boolvar(&mut terms, "c");
    let d = boolvar(&mut terms, "d");

    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::Trust, vec![a, b], Vec::new(), Vec::new());
    // Shares no complement with `{a, b}`.
    proof.add_rule_step(AletheRule::Trust, vec![c, d], Vec::new(), Vec::new());
    proof.add_rule_step(AletheRule::Trust, vec![a, c], Vec::new(), Vec::new());

    let mut derived: Vec<Option<Vec<TermId>>> = vec![];
    proof.add_rule_step(
        AletheRule::ThResolution,
        vec![a, b, c, d],
        vec![ProofId(0), ProofId(1), ProofId(2)],
        Vec::new(),
    );
    let mut err = None;
    for (i, step) in proof.steps.iter().enumerate() {
        if let Err(e) = validate_step(&terms, &mut derived, ProofId(i as u32), step, false, None) {
            err = Some(e);
            break;
        }
    }
    assert!(
        err.is_some(),
        "a link with no complementary pair must stay a rejection"
    );
}

/// The ordinary UNAMBIGUOUS chain must keep working, and by the fast path.
#[test]
fn an_unambiguous_chain_is_unchanged() {
    let mut terms = TermStore::new();
    let a = boolvar(&mut terms, "a");
    let b = boolvar(&mut terms, "b");
    let c = boolvar(&mut terms, "c");
    let na = terms.mk_not(a);
    let nb = terms.mk_not(b);

    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::Trust, vec![a, c], Vec::new(), Vec::new());
    proof.add_rule_step(AletheRule::Trust, vec![na, b], Vec::new(), Vec::new());
    proof.add_rule_step(AletheRule::Trust, vec![nb], Vec::new(), Vec::new());

    check_chain(&terms, &mut proof, vec![c]).expect("plain chain resolution must still pass");
}
