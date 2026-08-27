// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The `ArrayRowChain` sub-schema (K) arm of the intrinsic-tautology battery.
//!
//! Kept out of `intrinsic_leaf_promotion_tests.rs` so neither file grows past
//! the workspace's line ceiling; the differential discipline is that file's.
//!
//! WHAT THIS FILE CLAIMS, and what it does not. These tests are about WIRING:
//! that the battery's new last arm relabels exactly the clauses sub-schema (K)
//! accepts, that the UNTOUCHED strict checker then re-decides the relabelled
//! leaf, and that a clause (K) declines keeps a byte-identical `trust` step.
//! The VALIDITY question — that every accepted clause is true in every array
//! model and every declined neighbour has a named falsifying assignment checked
//! by an independent bounded evaluator — belongs to
//! `ay_proof::checker::array_axiom::ite_eval`'s own three test files, which own
//! the exhaustive sweep and the adversarial negatives. Restating it here in a
//! crate with no array-model evaluator would be prose, not evidence.
//!
//! Both fixtures build RAW applications: `mk_eq` distributes over `ite` and
//! folds `(= x true)`, and `mk_select` folds read-over-write — so the ordinary
//! builders cannot express the very nodes this schema is about.

use super::*;

use ay_core::{ArraySort, Sort, Symbol, TermId};

fn index_sort() -> Sort {
    Sort::Uninterpreted("Index".to_string())
}

fn bool_array_sort() -> Sort {
    Sort::Array(Box::new(ArraySort::new(index_sort(), Sort::Bool)))
}

fn raw_eq(executor: &mut Executor, lhs: TermId, rhs: TermId) -> TermId {
    executor
        .ctx
        .terms
        .mk_app(Symbol::named("="), vec![lhs, rhs], Sort::Bool)
}

/// `(or (not (= E (store (const false) i true))) (= (select E j) (= i j)))`
///
/// The measured corpus shape from `smt/chc_multi_pred_array`: a read of a
/// one-store chain over a const-array base, under an array-equality premise,
/// whose value side is the chain's symbolic evaluation with `mk_ite`'s Bool
/// fold `(ite c true false) = c` already applied.
fn packed_ite_folded_chain_eval(executor: &mut Executor) -> TermId {
    let falsity = executor.ctx.terms.false_term();
    let truth = executor.ctx.terms.true_term();
    let base = executor.ctx.terms.mk_const_array(index_sort(), falsity);
    let i = executor.ctx.terms.mk_var("k_i", index_sort());
    let j = executor.ctx.terms.mk_var("k_j", index_sort());
    let root = executor.ctx.terms.mk_var("k_E", bool_array_sort());
    let chain = executor.ctx.terms.mk_app(
        Symbol::named("store"),
        vec![base, i, truth],
        bool_array_sort(),
    );
    let read = executor
        .ctx
        .terms
        .mk_app(Symbol::named("select"), vec![root, j], Sort::Bool);
    let value = raw_eq(executor, i, j);
    let premise_eq = raw_eq(executor, root, chain);
    let premise = executor.ctx.terms.mk_not_raw(premise_eq);
    let conclusion = raw_eq(executor, read, value);
    executor
        .ctx
        .terms
        .mk_app(Symbol::named("or"), vec![premise, conclusion], Sort::Bool)
}

/// The same clause with the array equality POSITIVE and the read NEGATED:
/// `(or (= E C) (not (= (select E j) V)))`.
///
/// This is the EXTENSIONALITY direction and it is NOT valid. FALSIFIED AT
/// `C = store(const(false), 0, true) = [true, false]`, `E = [true, true]`,
/// `i = 0`, `j = 0`: `select(E, 0) = true` and `V = (0 = 0) = true`, so the
/// conclusion literal is TRUE and its negation FALSE; and `E != C` because they
/// differ at index 1, so the positive array equality is FALSE too. That exact
/// assignment is CHECKED against the independent bounded array model in
/// `ay_proof`'s `the_extensionality_direction_is_refutable_and_declined`; it is
/// a theorem only when `j` is a Skolem extensionality witness minted for the
/// pair, which is authority and not shape.
fn packed_extensionality_direction(executor: &mut Executor) -> TermId {
    let falsity = executor.ctx.terms.false_term();
    let truth = executor.ctx.terms.true_term();
    let base = executor.ctx.terms.mk_const_array(index_sort(), falsity);
    let i = executor.ctx.terms.mk_var("x_i", index_sort());
    let j = executor.ctx.terms.mk_var("x_j", index_sort());
    let root = executor.ctx.terms.mk_var("x_E", bool_array_sort());
    let chain = executor.ctx.terms.mk_app(
        Symbol::named("store"),
        vec![base, i, truth],
        bool_array_sort(),
    );
    let read = executor
        .ctx
        .terms
        .mk_app(Symbol::named("select"), vec![root, j], Sort::Bool);
    let value = raw_eq(executor, i, j);
    let premise = raw_eq(executor, root, chain);
    let conclusion_eq = raw_eq(executor, read, value);
    let conclusion = executor.ctx.terms.mk_not_raw(conclusion_eq);
    executor
        .ctx
        .terms
        .mk_app(Symbol::named("or"), vec![premise, conclusion], Sort::Bool)
}

fn trust_leaf(clause: Vec<TermId>) -> ProofStep {
    ProofStep::Step {
        rule: AletheRule::Trust,
        clause,
        premises: Vec::new(),
        args: Vec::new(),
    }
}

/// Whether the LEAF validated, read from the error TEXT: a single-lemma proof
/// always fails the whole-proof check on its terminal clause, so the accept
/// signal is that the refusal does not name the lemma. The probe protocol
/// `intrinsic_leaf_promotion_tests` established.
fn leaf_validates_under_strict(executor: &Executor, proof: &Proof) -> bool {
    match executor.check_proof_strict_with_datatypes(proof) {
        Ok(_) => true,
        Err(error) => {
            let text = format!("{error}");
            !(text.contains("theory lemma") || text.contains("trust") || text.contains("array"))
        }
    }
}

#[test]
fn a_demoted_ite_folded_chain_leaf_is_promoted_and_strict_validates() {
    let mut executor = Executor::new();
    let packed = packed_ite_folded_chain_eval(&mut executor);
    let mut proof = Proof::new();
    proof.add_step(trust_leaf(vec![packed]));

    assert!(
        !leaf_validates_under_strict(&executor, &proof),
        "precondition: the demoted trust leaf must be strict-REJECTED"
    );

    assert_eq!(executor.promote_intrinsic_tautology_leaves(&mut proof), 1);
    match &proof.steps[0] {
        ProofStep::TheoryLemma { kind, clause, .. } => {
            assert_eq!(*kind, TheoryLemmaKind::ArrayRowChain);
            assert_eq!(clause, &vec![packed], "the clause is preserved verbatim");
        }
        other => panic!("expected a promoted theory lemma, got {other:?}"),
    }
    assert!(
        leaf_validates_under_strict(&executor, &proof),
        "the promoted leaf must be accepted by the UNTOUCHED strict checker"
    );
}

#[test]
fn the_extensionality_direction_leaf_is_left_byte_identical() {
    let mut executor = Executor::new();
    let packed = packed_extensionality_direction(&mut executor);
    let mut proof = Proof::new();
    proof.add_step(trust_leaf(vec![packed]));
    let before = format!("{:?}", proof.steps[0]);

    assert_eq!(
        executor.promote_intrinsic_tautology_leaves(&mut proof),
        0,
        "a clause sub-schema (K) declines must not be promoted"
    );
    assert_eq!(
        format!("{:?}", proof.steps[0]),
        before,
        "the declined leaf must keep its byte-identical trust step"
    );

    // …and had it been promoted anyway, the strict checker would refuse it —
    // so the decline is a closed door and not merely a missed opportunity.
    let mut forced = Proof::new();
    forced.add_step(ProofStep::TheoryLemma {
        theory: "arrays".to_string(),
        clause: vec![packed],
        farkas: None,
        kind: TheoryLemmaKind::ArrayRowChain,
        lia: None,
    });
    assert!(
        !leaf_validates_under_strict(&executor, &forced),
        "the strict checker must refuse a forced ArrayRowChain label on this clause"
    );
}

#[test]
fn the_new_arm_is_dead_last_and_changes_no_label_the_battery_already_produced() {
    // ORDER IS LOAD-BEARING: the (K) arm sits after every entry that predates
    // it, so a clause an earlier arm accepts keeps that arm's label. A plain
    // select CONGRUENCE clause is accepted by BOTH the EUF congruence arm and
    // `recognize_array_theory_lemma`'s sub-schema (D) — and must still come
    // back as the EUF label, because that is what the battery produced before.
    let mut executor = Executor::new();
    let a = executor.ctx.terms.mk_var("c_A", bool_array_sort());
    let b = executor.ctx.terms.mk_var("c_B", bool_array_sort());
    let j = executor.ctx.terms.mk_var("c_j", index_sort());
    let read_a = executor
        .ctx
        .terms
        .mk_app(Symbol::named("select"), vec![a, j], Sort::Bool);
    let read_b = executor
        .ctx
        .terms
        .mk_app(Symbol::named("select"), vec![b, j], Sort::Bool);
    let premise_eq = raw_eq(&mut executor, a, b);
    let premise = executor.ctx.terms.mk_not_raw(premise_eq);
    let conclusion = raw_eq(&mut executor, read_a, read_b);
    let packed =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("or"), vec![premise, conclusion], Sort::Bool);

    let mut proof = Proof::new();
    proof.add_step(trust_leaf(vec![packed]));
    assert_eq!(executor.promote_intrinsic_tautology_leaves(&mut proof), 1);
    match &proof.steps[0] {
        ProofStep::TheoryLemma { kind, .. } => assert_eq!(
            *kind,
            TheoryLemmaKind::EufCongruent,
            "the pre-existing EUF label must survive the new last arm"
        ),
        other => panic!("expected a promoted theory lemma, got {other:?}"),
    }
}
