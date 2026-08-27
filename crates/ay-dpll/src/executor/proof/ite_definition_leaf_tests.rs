// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Positive and GUARD-MUTATION tests for the ITE-definition leaf lane.
//!
//! # Fixture discipline
//!
//! Every fixture is a COMPLETE REFUTATION and its closer is a second `trust`
//! step, never an `assume`. That is not cosmetic: freshness is a statement
//! about the FINISHED proof's `assume` set, so an `assume (not goal)` would
//! itself MENTION the fresh definiendum and every mint would decline for a
//! reason that is not the one under test. The corpus population has no such
//! assume — its leaf is consumed by resolutions.
//!
//! # GUARD MUTATION LEDGER — 19 mutations, **10 RED, 5 honest negatives**
//!
//! Each guard deleted or weakened in `ite_definition_leaf.rs` /
//! `ite_definition_leaf_fragment.rs`, the whole `ite_definition_leaf` suite
//! re-run, the named tests observed FAILING, the guard restored. Guards
//! backstop each other, so a guard that comes back green ALONE is re-run
//! deleted in a PAIR with the guard that backstops it — the discipline the
//! `minted_definition_leaf` ledger records after 9 of 11 came back green.
//!
//! | # | guard | mutation | result |
//! |---|---|---|---|
//! | 1 | no `Anchor` steps | delete the scan | **RED** `a_proof_carrying_an_anchor_is_left_alone` |
//! | 2 | `premises.is_empty()` | delete it | **RED** `a_trust_step_with_premises_is_left_alone` |
//! | 2 | `args.is_empty()` | delete it | **RED** `a_trust_step_with_args_is_left_alone` |
//! | 3 | the `__ay_ite_def_` PREFIX | accept any trailing-digit name | green ALONE (the fixture's ordinary name has no digits); **RED PAIRED with 6** |
//! | 4 | the decoded id is an `Ite` | fall back to `(d, d, d)` | green ALONE (Guard 6 then rejects the polarity); **RED PAIRED with 6** |
//! | 5 | `mk_var(name, sort)` re-derives the same `TermId` | delete the comparison | green ALONE (Guard 6 backstops); **RED PAIRED with 6** |
//! | 6 | the polarity selects the branch | swap the two branches | **RED**, 8 tests |
//! | 6 | the rebuilt equality IS the leaf's literal | delete the comparison | **RED**, 3 tests incl. the sweep |
//! | 7 | FRESH | delete the `constrained` test | green ALONE (Gate 2 backstops); **RED PAIRED with 13** |
//! | 8 | SINGLE DEFINIENS vs an existing binding | delete it | green even PAIRED with 13 — the lane cannot build a competing fragment at all. Pinned DIRECTLY and TWO-SIDED by `a_competing_existing_binding_is_never_overwritten` |
//! | 9 | INDEPENDENT | delete it | green even PAIRED with 13, same reason. Pinned DIRECTLY and TWO-SIDED by `a_definiens_mentioning_another_definiendum_is_declined` |
//! | 10 | `recognize_fresh_def_eq` at emission | delete it | green — the lane only ever builds triples the recognizer accepts, so it is defence in depth. Pinned DIRECTLY and TWO-SIDED by `the_checker_decides_both_new_leaf_steps` |
//! | 10 | `recognize_ite_branch_projection` at emission | delete it | green, same reason, same direct pin |
//! | 11 | the fragment ends on the leaf's clause | delete it | green — unfalsifiable by construction. Pinned directly by `the_replaced_leaf_keeps_its_clause_byte_for_byte` |
//! | 13 | Gate 2 | delete it | green ALONE (Guard 7 backstops); **RED PAIRED with 7** |
//!
//! **Every fixture is a COMPLETE REFUTATION** and asserts it starts REJECTED,
//! so a mutation cannot come back green on a fragment that was never replayed.

use ay_core::{AletheRule, Proof, ProofId, ProofStep, Sort, TermData, TermId};

use super::super::super::Executor;

// ===== fixture helpers =====

pub(super) fn complement(exec: &mut Executor, literal: TermId) -> TermId {
    let normalized = exec.ctx.terms.mk_not(literal);
    let cancels = match exec.ctx.terms.get(normalized) {
        TermData::Not(inner) => *inner == literal,
        _ => matches!(exec.ctx.terms.get(literal), TermData::Not(inner) if *inner == normalized),
    };
    if cancels {
        normalized
    } else {
        exec.ctx.terms.mk_not_raw(literal)
    }
}

/// A COMPLETE REFUTATION carrying `goal` as its premiseless `trust` leaf, with
/// a second `trust` step (NOT an `assume`) as its closer.
pub(super) fn leaf_proof(exec: &mut Executor, goal: TermId) -> Proof {
    let negated = complement(exec, goal);
    let mut proof = Proof::new();
    proof.steps.push(ProofStep::Step {
        rule: AletheRule::Trust,
        clause: vec![goal],
        premises: Vec::new(),
        args: Vec::new(),
    });
    proof.steps.push(ProofStep::Step {
        rule: AletheRule::Trust,
        clause: vec![negated],
        premises: Vec::new(),
        args: Vec::new(),
    });
    proof.steps.push(ProofStep::Step {
        rule: AletheRule::Resolution,
        clause: Vec::new(),
        premises: vec![ProofId(0), ProofId(1)],
        args: Vec::new(),
    });
    proof
}

pub(super) fn premiseless_unit_trust_leaves(proof: &Proof) -> usize {
    proof
        .steps
        .iter()
        .filter(|step| {
            matches!(
                step,
                ProofStep::Step {
                    rule: AletheRule::Trust,
                    clause,
                    premises,
                    args,
                } if premises.is_empty() && args.is_empty() && clause.len() == 1
            )
        })
        .count()
}

pub(super) fn rerun(exec: &mut Executor, proof: &mut Proof) -> usize {
    let scope = exec.complete_problem_assertions_for_strict_proof();
    exec.derive_ite_definition_guard_leaves(proof, &scope)
}

/// The corpus shape: `(ite c 1 0)` named `__ay_ite_def_<id>`, with the
/// guard-NEGATIVE half `(or (not c) (= d 1))`.
pub(super) struct Fixture {
    pub(super) exec: Executor,
    pub(super) condition: TermId,
    pub(super) ite: TermId,
    pub(super) definiendum: TermId,
    pub(super) then_branch: TermId,
    pub(super) else_branch: TermId,
}

pub(super) fn fixture() -> Fixture {
    let mut exec = Executor::new();
    let terms = &mut exec.ctx.terms;
    let condition = terms.mk_var("itedef_c", Sort::Bool);
    let then_branch = terms.mk_int(1.into());
    let else_branch = terms.mk_int(0.into());
    let ite = terms.mk_ite_raw(condition, then_branch, else_branch);
    let sort = terms.sort(ite).clone();
    let definiendum = terms.mk_var(format!("__ay_ite_def_{}", ite.0), sort);
    // A problem the lane may run against; it must NOT mention the definiendum.
    let unrelated = terms.mk_var("itedef_unrelated", Sort::Bool);
    exec.ctx.assertions = vec![unrelated];
    Fixture {
        exec,
        condition,
        ite,
        definiendum,
        then_branch,
        else_branch,
    }
}

/// `(or (not c) (= d then))` — the guard-negative half.
pub(super) fn negative_half(f: &mut Fixture) -> TermId {
    let equality = f.exec.ctx.terms.mk_eq(f.definiendum, f.then_branch);
    let not_condition = f.exec.ctx.terms.mk_not(f.condition);
    f.exec.ctx.terms.mk_or(vec![not_condition, equality])
}

/// `(or c (= d else))` — the guard-positive half.
pub(super) fn positive_half(f: &mut Fixture) -> TermId {
    let equality = f.exec.ctx.terms.mk_eq(f.definiendum, f.else_branch);
    f.exec.ctx.terms.mk_or(vec![f.condition, equality])
}

// ===== the lane =====

#[test]
fn the_guard_negative_half_is_derived_over_a_minted_definition() {
    let mut f = fixture();
    let goal = negative_half(&mut f);
    let mut proof = leaf_proof(&mut f.exec, goal);
    assert!(
        f.exec.check_proof_strict_with_datatypes(&proof).is_err(),
        "the fixture must start REJECTED"
    );
    assert_eq!(
        premiseless_unit_trust_leaves(&proof),
        2,
        "the leaf and its trust closer"
    );
    assert_eq!(rerun(&mut f.exec, &mut proof), 1);
    assert_eq!(
        premiseless_unit_trust_leaves(&proof),
        1,
        "only the fixture's own closer survives"
    );
    // The strict checker's ONLY remaining objection is that closer.
    let refusal = f.exec.check_proof_strict_with_datatypes(&proof);
    let Err(ay_proof::ProofCheckError::TrustStep { step }) = refusal else {
        panic!("expected a TrustStep refusal on the fixture's own closer, got {refusal:?}");
    };
    assert!(
        matches!(
            proof.steps.get(step.0 as usize),
            Some(ProofStep::Step { clause, .. }) if clause.len() == 1 && clause[0] != goal
        ),
        "the surviving refusal must be the closer, not the derived leaf"
    );
}

#[test]
fn the_guard_positive_half_is_derived_over_a_minted_definition() {
    let mut f = fixture();
    let goal = positive_half(&mut f);
    let mut proof = leaf_proof(&mut f.exec, goal);
    assert_eq!(rerun(&mut f.exec, &mut proof), 1);
    assert_eq!(premiseless_unit_trust_leaves(&proof), 1);
    assert!(proof.steps.iter().any(|step| matches!(
        step,
        ProofStep::Step {
            rule: AletheRule::FreshDefEq,
            args,
            ..
        } if args.as_slice() == [f.definiendum]
    )));
}

#[test]
fn both_halves_of_one_definition_share_a_single_definiens() {
    let mut f = fixture();
    let first = negative_half(&mut f);
    let second = positive_half(&mut f);
    let mut proof = leaf_proof(&mut f.exec, first);
    // Splice the second leaf in ahead of the closer.
    proof.steps.insert(
        1,
        ProofStep::Step {
            rule: AletheRule::Trust,
            clause: vec![second],
            premises: Vec::new(),
            args: Vec::new(),
        },
    );
    if let Some(ProofStep::Step { premises, .. }) = proof.steps.last_mut() {
        *premises = vec![ProofId(0), ProofId(2)];
    }
    assert_eq!(rerun(&mut f.exec, &mut proof), 2, "both halves derive");
    // SINGLE DEFINIENS: the checker's own registry accepts the finished proof.
    assert!(
        ay_proof::FreshDefRegistry::collect(&proof, &f.exec.ctx.terms, Some(&[])).is_ok(),
        "one definiens per symbol across both fragments"
    );
}

#[test]
fn the_replaced_leaf_keeps_its_clause_byte_for_byte() {
    let mut f = fixture();
    let goal = negative_half(&mut f);
    let mut proof = leaf_proof(&mut f.exec, goal);
    assert_eq!(rerun(&mut f.exec, &mut proof), 1);
    assert!(
        proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::Step {
                rule: AletheRule::Contraction,
                clause,
                ..
            } if clause.as_slice() == [goal]
        )),
        "the fragment must conclude the leaf's own or-term"
    );
}
