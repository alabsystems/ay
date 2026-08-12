// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Array-extensionality ordering regression for certified EUF promotion.

use super::*;
use crate::executor::theories::{array_extensionality_witness, ArrayExtWitnessBinding};
use ay_core::{ProofStep, Sort, TheoryLemmaKind};
use ay_frontend::command::Term as FrontendTerm;

#[test]
fn generic_euf_rebuild_defers_real_extensionality_promotion() {
    let mut exec = Executor::new();
    let array_sort = Sort::array(Sort::Int, Sort::Int);
    let array_a = exec.ctx.terms.mk_var("deferred_ext_a", array_sort.clone());
    let array_b = exec.ctx.terms.mk_var("deferred_ext_b", array_sort);
    let witness = array_extensionality_witness(
        &mut exec.ctx.terms,
        &mut exec.array_ext_witness_cache,
        array_a,
        array_b,
    )
    .expect("fixture witness");
    let arrays_equal = exec.ctx.terms.mk_eq(array_a, array_b);
    let select_a = exec.ctx.terms.mk_select(array_a, witness);
    let select_b = exec.ctx.terms.mk_select(array_b, witness);
    let selects_equal = exec.ctx.terms.mk_eq(select_a, select_b);
    let selects_differ = exec.ctx.terms.mk_not_raw(selects_equal);
    let extensionality = exec.ctx.terms.mk_or(vec![arrays_equal, selects_differ]);
    assert!(exec.array_ext_witness_cache.record_generated_clause(
        &exec.ctx.terms,
        extensionality,
        vec![ArrayExtWitnessBinding {
            witness,
            array_a,
            array_b,
        }],
    ));

    let x = exec.ctx.terms.mk_var("deferred_euf_x", Sort::Int);
    let y = exec.ctx.terms.mk_var("deferred_euf_y", Sort::Int);
    let xy = exec.ctx.terms.mk_eq(x, y);
    let not_xy = exec.ctx.terms.mk_not_raw(xy);
    let px = exec
        .ctx
        .terms
        .mk_app(Symbol::named("deferred_euf_p"), [x], Sort::Bool);
    let py = exec
        .ctx
        .terms
        .mk_app(Symbol::named("deferred_euf_p"), [y], Sort::Bool);
    let not_px = exec.ctx.terms.mk_not_raw(px);
    let not_py = exec.ctx.terms.mk_not_raw(py);
    for authored in [xy, px, not_py] {
        exec.ctx
            .add_assertion_with_parsed(authored, FrontendTerm::Symbol("problem".to_string()));
    }
    exec.ctx.assertions.push(extensionality);

    let mut proof = Proof::new();
    proof.add_theory_lemma("array", vec![extensionality]);
    let h_xy = proof.add_assume(xy, None);
    let h_px = proof.add_assume(px, None);
    let h_not_py = proof.add_assume(not_py, None);
    let generic =
        proof.add_theory_lemma_with_kind("EUF", vec![not_xy, not_px, py], TheoryLemmaKind::Generic);
    let without_xy = proof.add_resolution(vec![not_px, py], xy, generic, h_xy);
    let py_unit = proof.add_resolution(vec![py], px, without_xy, h_px);
    proof.add_resolution(Vec::new(), py, py_unit, h_not_py);

    exec.promote_certified_generic_euf_leaves(&mut proof);

    assert!(proof.steps.iter().any(|step| matches!(
        step,
        ProofStep::TheoryLemma { clause, kind, .. }
            if clause == &[extensionality] && kind.is_trust()
    )));
    assert!(proof.steps.iter().all(|step| !matches!(
        step,
        ProofStep::TheoryLemma { clause, kind: TheoryLemmaKind::Generic, .. }
            if clause == &[not_xy, not_px, py]
    )));
    assert!(
        exec.check_proof_strict_derivation_with_datatypes(&proof)
            .is_err(),
        "real extensionality promotion remains deferred"
    );

    exec.promote_array_extensionality_axioms(&mut proof);
    exec.check_proof_strict_derivation_with_datatypes(&proof)
        .expect("the final authenticated extensionality pass completes the proof");
}
