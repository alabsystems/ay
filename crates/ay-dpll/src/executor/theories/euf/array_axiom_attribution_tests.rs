// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::{ArraySort, ProofStep, Sort, Symbol};

fn int_array_sort() -> Sort {
    Sort::Array(Box::new(ArraySort::new(Sort::Int, Sort::Int)))
}

#[test]
fn push_array_axiom_assertion_site_attributes_row1_as_positive() {
    let mut exec = Executor::new();
    exec.proof_tracker.enable();
    let a = exec.ctx.terms.mk_var("a", int_array_sort());
    let i = exec.ctx.terms.mk_var("i", Sort::Int);
    let v = exec.ctx.terms.mk_var("v", Sort::Int);
    let store = exec.ctx.terms.mk_store(a, i, v);
    // Preserve the primitive ROW1 syntax: `mk_select` intentionally folds
    // this exact read to `v` before proof attribution can inspect it.
    let select = exec
        .ctx
        .terms
        .mk_app(Symbol::named("select"), [store, i], Sort::Int);
    let row1 = exec.ctx.terms.mk_eq(select, v);

    exec.push_array_axiom_assertion_site(row1, "row1_trivial");
    let proof = exec.proof_tracker.take_proof();

    match &proof.steps[0] {
        ProofStep::TheoryLemma { kind, clause, .. } => {
            assert_eq!(*kind, TheoryLemmaKind::ArraySelectStore { index_eq: true });
            assert_eq!(clause, &vec![row1]);
        }
        other => panic!("expected theory lemma, got {other:?}"),
    }
}

#[test]
fn push_array_axiom_assertion_site_attributes_row2_as_negative() {
    let mut exec = Executor::new();
    exec.proof_tracker.enable();
    let a = exec.ctx.terms.mk_var("a", int_array_sort());
    let i = exec.ctx.terms.mk_var("i", Sort::Int);
    let j = exec.ctx.terms.mk_var("j", Sort::Int);
    let v = exec.ctx.terms.mk_var("v", Sort::Int);
    let store = exec.ctx.terms.mk_store(a, i, v);
    let select_store = exec.ctx.terms.mk_select(store, j);
    let select_base = exec.ctx.terms.mk_select(a, j);
    let idx_eq = exec.ctx.terms.mk_eq(i, j);
    let row2_eq = exec.ctx.terms.mk_eq(select_store, select_base);
    let row2 = exec.ctx.terms.mk_or(vec![idx_eq, row2_eq]);

    exec.push_array_axiom_assertion_site(row2, "row2_clause");
    let proof = exec.proof_tracker.take_proof();

    match &proof.steps[0] {
        ProofStep::TheoryLemma { kind, clause, .. } => {
            assert_eq!(*kind, TheoryLemmaKind::ArraySelectStore { index_eq: false });
            assert_eq!(clause, &vec![row2]);
        }
        other => panic!("expected theory lemma, got {other:?}"),
    }
}

#[test]
fn push_array_axiom_assertion_site_keeps_unchecked_extensionality_generic() {
    let mut exec = Executor::new();
    exec.proof_tracker.enable();
    let a = exec.ctx.terms.mk_var("a", int_array_sort());
    let b = exec.ctx.terms.mk_var("b", int_array_sort());
    let k = exec.ctx.terms.mk_var("k", Sort::Int);
    let array_eq = exec.ctx.terms.mk_eq(a, b);
    let sel_a = exec.ctx.terms.mk_select(a, k);
    let sel_b = exec.ctx.terms.mk_select(b, k);
    let sel_eq = exec.ctx.terms.mk_eq(sel_a, sel_b);
    let not_sel_eq = exec.ctx.terms.mk_not(sel_eq);
    let ext = exec.ctx.terms.mk_or(vec![array_eq, not_sel_eq]);

    exec.push_array_axiom_assertion_site(ext, "ext_axiom");
    let proof = exec.proof_tracker.take_proof();

    match &proof.steps[0] {
        ProofStep::TheoryLemma { kind, clause, .. } => {
            assert_eq!(*kind, TheoryLemmaKind::Generic);
            assert_eq!(clause, &vec![ext]);
        }
        other => panic!("expected theory lemma, got {other:?}"),
    }
}

#[test]
fn push_array_axiom_assertion_site_uses_shape_not_site_name() {
    let mut exec = Executor::new();
    exec.proof_tracker.enable();
    let a = exec.ctx.terms.mk_var("a", int_array_sort());
    let i = exec.ctx.terms.mk_var("i", Sort::Int);
    let j = exec.ctx.terms.mk_var("j", Sort::Int);
    let v = exec.ctx.terms.mk_var("v", Sort::Int);
    let store = exec.ctx.terms.mk_store(a, i, v);
    let select_store = exec.ctx.terms.mk_select(store, j);
    let select_base = exec.ctx.terms.mk_select(a, j);
    let idx_eq = exec.ctx.terms.mk_eq(i, j);
    let row2_eq = exec.ctx.terms.mk_eq(select_store, select_base);
    let row2 = exec.ctx.terms.mk_or(vec![idx_eq, row2_eq]);

    // Deliberately pass a ROW1-looking diagnostic label.  The exact clause
    // shape, not this string, must determine proof attribution.
    exec.push_array_axiom_assertion_site(row2, "row1_trivial");
    let proof = exec.proof_tracker.take_proof();

    match &proof.steps[0] {
        ProofStep::TheoryLemma { kind, clause, .. } => {
            assert_eq!(*kind, TheoryLemmaKind::ArraySelectStore { index_eq: false });
            assert_eq!(clause, &vec![row2]);
        }
        other => panic!("expected theory lemma, got {other:?}"),
    }
}

#[test]
fn push_array_axiom_assertion_site_skips_true_axioms() {
    let mut exec = Executor::new();
    exec.proof_tracker.enable();
    let assertions_before = exec.ctx.assertions.len();

    let truth = exec.ctx.terms.true_term();
    exec.push_array_axiom_assertion_site(truth, "store_value_cong");

    assert_eq!(exec.ctx.assertions.len(), assertions_before);
    assert_eq!(exec.proof_tracker.num_steps(), 0);
}
