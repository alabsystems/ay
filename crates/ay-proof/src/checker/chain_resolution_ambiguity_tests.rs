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
use ay_core::{AletheRule, Proof, ProofId, Sort, Symbol, TermId, TermStore};

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
    check_chain_with_args(terms, proof, clause, Vec::new())
}

fn check_chain_with_args(
    terms: &TermStore,
    proof: &mut Proof,
    clause: Vec<TermId>,
    args: Vec<TermId>,
) -> Result<(), ProofCheckError> {
    let premises = (0..proof.steps.len())
        .map(|index| ProofId(index as u32))
        .collect();
    proof.add_rule_step(AletheRule::ThResolution, clause, premises, args);
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

#[test]
fn unit_tail_chain_removes_each_complement_once() {
    let mut terms = TermStore::new();
    let atoms: Vec<TermId> = (0..128)
        .map(|index| boolvar(&mut terms, &format!("unit_tail_{index}")))
        .collect();
    let negated: Vec<TermId> = atoms.iter().map(|&atom| terms.mk_not(atom)).collect();
    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::Trust, atoms, Vec::new(), Vec::new());
    for literal in negated {
        proof.add_rule_step(AletheRule::Trust, vec![literal], Vec::new(), Vec::new());
    }

    check_chain(&terms, &mut proof, Vec::new())
        .expect("a complete unit tail must resolve the accumulator to empty");
}

#[test]
fn unit_tail_chain_rejects_a_repeated_removal() {
    let mut terms = TermStore::new();
    let a = boolvar(&mut terms, "unit_tail_repeat_a");
    let b = boolvar(&mut terms, "unit_tail_repeat_b");
    let not_a = terms.mk_not(a);
    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::Trust, vec![a, b], Vec::new(), Vec::new());
    proof.add_rule_step(AletheRule::Trust, vec![not_a], Vec::new(), Vec::new());
    proof.add_rule_step(AletheRule::Trust, vec![not_a], Vec::new(), Vec::new());

    check_chain(&terms, &mut proof, vec![b])
        .expect_err("one accumulator literal cannot be removed twice");
}

#[test]
fn unit_tail_chain_preserves_set_semantics_for_duplicate_end_clauses() {
    let mut terms = TermStore::new();
    let a = boolvar(&mut terms, "unit_tail_duplicate_a");
    let b = boolvar(&mut terms, "unit_tail_duplicate_b");
    let c = boolvar(&mut terms, "unit_tail_duplicate_c");
    let not_a = terms.mk_not(a);
    let not_b = terms.mk_not(b);
    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::Trust, vec![a, a, b, c], Vec::new(), Vec::new());
    proof.add_rule_step(AletheRule::Trust, vec![not_a], Vec::new(), Vec::new());
    proof.add_rule_step(AletheRule::Trust, vec![not_b], Vec::new(), Vec::new());

    check_chain(&terms, &mut proof, vec![c, c])
        .expect("argument-free resolution treats duplicate first/target literals as a set");
}

#[test]
fn annotated_chain_requires_one_pivot_polarity_pair_per_link() {
    let mut terms = TermStore::new();
    let a = boolvar(&mut terms, "a");
    let b = boolvar(&mut terms, "b");
    let na = terms.mk_not(a);
    let nb = terms.mk_not(b);
    let yes = terms.mk_bool(true);

    let build = || {
        let mut proof = Proof::new();
        proof.add_rule_step(AletheRule::Trust, vec![a, b], Vec::new(), Vec::new());
        proof.add_rule_step(AletheRule::Trust, vec![nb], Vec::new(), Vec::new());
        proof.add_rule_step(AletheRule::Trust, vec![na], Vec::new(), Vec::new());
        proof
    };

    check_chain_with_args(&terms, &mut build(), vec![], vec![b, yes, a, yes])
        .expect("the declared pivots eliminate b and then a");

    check_chain_with_args(&terms, &mut build(), vec![], vec![b])
        .expect_err("a partial :args annotation must not be silently ignored");

    check_chain_with_args(&terms, &mut build(), vec![], vec![a, yes, b, yes])
        .expect_err("a pivot that is absent from its link must be rejected");
}

#[test]
fn annotated_binary_resolution_honors_false_polarity() {
    let mut terms = TermStore::new();
    let a = boolvar(&mut terms, "a");
    let na = terms.mk_not(a);
    let no = terms.mk_bool(false);
    let mut proof = Proof::new();
    let left = proof.add_rule_step(AletheRule::Trust, vec![na], Vec::new(), Vec::new());
    let right = proof.add_rule_step(AletheRule::Trust, vec![a], Vec::new(), Vec::new());
    proof.add_rule_step(
        AletheRule::Resolution,
        vec![],
        vec![left, right],
        vec![a, no],
    );

    let mut derived = Vec::new();
    for (index, step) in proof.steps.iter().enumerate() {
        validate_step(
            &terms,
            &mut derived,
            ProofId(index as u32),
            step,
            false,
            None,
        )
        .expect("false means the negated pivot is in the accumulator");
    }
}

#[test]
fn argument_free_resolution_normalizes_leading_not_parity() {
    let mut terms = TermStore::new();
    let a = boolvar(&mut terms, "a");
    let not_a = terms.mk_not_raw(a);
    let not_not_a = terms.mk_not_raw(not_a);
    let not_not_not_a = terms.mk_not_raw(not_not_a);
    let mut proof = Proof::new();
    let left = proof.add_rule_step(
        AletheRule::Trust,
        vec![not_not_not_a],
        Vec::new(),
        Vec::new(),
    );
    let right = proof.add_rule_step(AletheRule::Trust, vec![a], Vec::new(), Vec::new());
    proof.add_rule_step(
        AletheRule::Resolution,
        vec![],
        vec![left, right],
        Vec::new(),
    );

    let mut derived = Vec::new();
    for (index, step) in proof.steps.iter().enumerate() {
        validate_step(
            &terms,
            &mut derived,
            ProofId(index as u32),
            step,
            false,
            None,
        )
        .expect("argument-free resolution retains Carcara's parity semantics");
    }
}

#[test]
fn demorgan_equivalence_is_not_a_resolution_pivot() {
    let mut terms = TermStore::new();
    let a = boolvar(&mut terms, "a");
    let b = boolvar(&mut terms, "b");
    let na = terms.mk_not(a);
    let nb = terms.mk_not(b);
    let conjunction = terms.mk_app(Symbol::Named("and".to_string()), [a, b], Sort::Bool);
    let negated_components = terms.mk_app(Symbol::Named("or".to_string()), [na, nb], Sort::Bool);
    let mut proof = Proof::new();
    let left = proof.add_rule_step(AletheRule::Trust, vec![conjunction], Vec::new(), Vec::new());
    let right = proof.add_rule_step(
        AletheRule::Trust,
        vec![negated_components],
        Vec::new(),
        Vec::new(),
    );
    proof.add_rule_step(
        AletheRule::Resolution,
        vec![],
        vec![left, right],
        Vec::new(),
    );

    let mut derived = Vec::new();
    let mut rejected = false;
    for (index, step) in proof.steps.iter().enumerate() {
        if validate_step(
            &terms,
            &mut derived,
            ProofId(index as u32),
            step,
            false,
            None,
        )
        .is_err()
        {
            rejected = true;
            break;
        }
    }
    assert!(
        rejected,
        "Alethe requires an explicit Boolean derivation between De Morgan equivalents"
    );
}

/// CHARGE PARITY for the bounded search.
///
/// The search charges each link as it explores it, so its cost is MEASURED
/// rather than pre-charged at the worst case. Two things must stay true: the
/// charges are actually levied (nothing became free), and a caller that refuses
/// stops the search with `ResourceLimit` instead of completing it unpaid.
#[test]
fn the_bounded_search_charges_every_link_and_stops_when_refused() {
    let mut terms = TermStore::new();
    let (mut proof, via_a, _) = ambiguous_chain(&mut terms);
    let premises: Vec<ProofId> = (0..proof.steps.len())
        .map(|index| ProofId(index as u32))
        .collect();
    proof.add_rule_step(AletheRule::ThResolution, via_a, premises, Vec::new());
    let premise_clauses: Vec<Vec<TermId>> = proof.steps[..proof.steps.len() - 1]
        .iter()
        .map(|premise| match premise {
            ProofStep::Step { clause, .. } => clause.clone(),
            other => panic!("unexpected premise shape: {other:?}"),
        })
        .collect();
    let views: Vec<&[TermId]> = premise_clauses.iter().map(Vec::as_slice).collect();
    let step = proof.steps.last().expect("the chain step");
    let ProofStep::Step { clause, rule, .. } = step else {
        panic!("unexpected step shape: {step:?}");
    };

    let mut charges: Vec<(usize, usize)> = Vec::new();
    resolution::validate_chain_resolution_rule(
        &terms,
        ProofId(3),
        rule,
        clause,
        &views,
        &mut |work, bytes| {
            charges.push((work, bytes));
            true
        },
    )
    .expect("the ambiguous chain reaches its declared clause");
    assert!(
        charges.len() >= 2,
        "every explored link must be charged: {charges:?}"
    );
    assert!(
        charges.iter().all(|&(work, bytes)| work > 0 && bytes > 0),
        "a link that materializes literal sets must charge work AND bytes: {charges:?}"
    );

    // Refusing the FIRST link aborts the search with the resource verdict, so a
    // budget that is genuinely spent still fails closed.
    let mut seen = 0_usize;
    let refused = resolution::validate_chain_resolution_rule(
        &terms,
        ProofId(3),
        rule,
        clause,
        &views,
        &mut |_, _| {
            seen += 1;
            false
        },
    );
    assert_eq!(refused, Err(ProofCheckError::ResourceLimit));
    assert_eq!(seen, 1, "the search must stop on the first refusal");
}
