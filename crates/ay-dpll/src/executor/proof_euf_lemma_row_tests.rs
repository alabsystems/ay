// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Read-over-write bridge pins for certified EUF promotion
//! (#implied-forall-ground-inst).
//!
//! The planned shape is the MEASURED #7956 same-context-probe conflict: a
//! `Generic` array+EUF theory lemma whose only non-congruence content is one
//! read of an array that the hypotheses equate to a store, at an index the
//! hypotheses equate to the store's index. The bridge must spend no trust:
//! the emitted proof carries one `ArraySelectStore` leaf the UNTOUCHED strict
//! checker re-validates from the clause alone, plus ordinary
//! `eq_congruent`/`eq_transitive` steps.

use super::*;
use ay_core::{ProofStep, Sort, TheoryLemmaKind};

/// `a = store(b, 0, v)`, `0 = i`, `x = select(a, i)` entail `x = v`.
///
/// MUTATION: remove the ROW-under-equality saturation loop in
/// `plan_euf_lemma_inner` (or make it never union) and this fails — the
/// closure cannot link `select(a, i)` to `v` by congruence alone, the leaf
/// stays `Generic`, and the strict check keeps rejecting the proof.
#[test]
fn a_read_under_a_store_equality_promotes_through_an_array_leaf() {
    let mut exec = Executor::new();
    let terms = &mut exec.ctx.terms;
    let array_sort = Sort::array(Sort::Int, Sort::Int);
    let a = terms.mk_var("row_bridge_a", array_sort.clone());
    let b = terms.mk_var("row_bridge_b", array_sort);
    let v = terms.mk_var("row_bridge_v", Sort::Int);
    let x = terms.mk_var("row_bridge_x", Sort::Int);
    let i = terms.mk_var("row_bridge_i", Sort::Int);
    let zero = terms.mk_int(0.into());
    let store = terms.mk_store(b, zero, v);
    let select = terms.mk_app(Symbol::named("select"), [a, i], Sort::Int);

    let eq_a_store = terms.mk_eq(a, store);
    let eq_zero_i = terms.mk_eq(zero, i);
    let eq_x_select = terms.mk_eq(x, select);
    let eq_x_v = terms.mk_eq(x, v);
    let not_eq_a_store = terms.mk_not_raw(eq_a_store);
    let not_eq_zero_i = terms.mk_not_raw(eq_zero_i);
    let not_eq_x_select = terms.mk_not_raw(eq_x_select);
    let not_eq_x_v = terms.mk_not_raw(eq_x_v);

    let mut proof = Proof::new();
    let h1 = proof.add_assume(eq_a_store, None);
    let h2 = proof.add_assume(eq_zero_i, None);
    let h3 = proof.add_assume(eq_x_select, None);
    let h4 = proof.add_assume(not_eq_x_v, None);
    let generic = proof.add_theory_lemma_with_kind(
        "AUFLIA",
        vec![not_eq_a_store, not_eq_zero_i, not_eq_x_select, eq_x_v],
        TheoryLemmaKind::Generic,
    );
    let r1 = proof.add_resolution(
        vec![not_eq_zero_i, not_eq_x_select, eq_x_v],
        eq_a_store,
        generic,
        h1,
    );
    let r2 = proof.add_resolution(vec![not_eq_x_select, eq_x_v], eq_zero_i, r1, h2);
    let r3 = proof.add_resolution(vec![eq_x_v], eq_x_select, r2, h3);
    proof.add_resolution(Vec::new(), eq_x_v, r3, h4);

    assert!(ay_proof::check_proof_strict(&proof, terms).is_err());
    exec.ctx
        .assertions
        .extend([eq_a_store, eq_zero_i, eq_x_select, not_eq_x_v]);
    exec.promote_certified_generic_euf_leaves(&mut proof);

    assert!(
        proof.steps.iter().all(|step| !matches!(
            step,
            ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::Generic,
                ..
            }
        )),
        "the fused Generic conflict must be replaced"
    );
    assert!(
        proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::ArraySelectStore { index_eq: true },
                ..
            }
        )),
        "the replacement must reach the read through a checkable array leaf"
    );
    assert!(
        proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::Step {
                rule: AletheRule::EqTransitive,
                ..
            }
        )),
        "the bridge joins the congruent read and the leaf by eq_transitive"
    );
    ay_proof::check_proof_strict(&proof, &exec.ctx.terms)
        .expect("the promoted row-bridge proof must pass the untouched strict checker");
}

/// FALSIFY ONCE. Plant the byte-identical leaf/cong/trans shape over a
/// SATISFIABLE variant — the store holds `v` but the leaf claims the read is
/// the UNRELATED `w` — and show (1) the planner proposes nothing for the
/// non-entailed conclusion, and (2) the forged leaf itself is rejected by the
/// UNTOUCHED strict checker.
///
/// MUTATION: make `plan_row` (or the saturation) use the store's VALUE slot
/// without re-deriving it and case (1) can silently plan an unsound bridge;
/// case (2) pins that even then the strict checker refuses the planted leaf.
#[test]
fn a_forged_read_value_is_refused_by_the_untouched_checker() {
    let mut exec = Executor::new();
    let terms = &mut exec.ctx.terms;
    let array_sort = Sort::array(Sort::Int, Sort::Int);
    let a = terms.mk_var("row_forge_a", array_sort.clone());
    let b = terms.mk_var("row_forge_b", array_sort);
    let v = terms.mk_var("row_forge_v", Sort::Int);
    let w = terms.mk_var("row_forge_w", Sort::Int);
    let x = terms.mk_var("row_forge_x", Sort::Int);
    let i = terms.mk_var("row_forge_i", Sort::Int);
    let zero = terms.mk_int(0.into());
    let store = terms.mk_store(b, zero, v);
    let select = terms.mk_app(Symbol::named("select"), [a, i], Sort::Int);

    let eq_a_store = terms.mk_eq(a, store);
    let eq_zero_i = terms.mk_eq(zero, i);
    let eq_x_select = terms.mk_eq(x, select);
    // SATISFIABLE twin: the conclusion names `w`, which nothing pins to the
    // stored value. The planner must decline.
    let eq_x_w = terms.mk_eq(x, w);
    let not_eq_a_store = terms.mk_not_raw(eq_a_store);
    let not_eq_zero_i = terms.mk_not_raw(eq_zero_i);
    let not_eq_x_select = terms.mk_not_raw(eq_x_select);
    let clause = vec![not_eq_a_store, not_eq_zero_i, not_eq_x_select, eq_x_w];
    assert!(
        exec.plan_euf_lemma(&clause).is_none(),
        "a non-entailed conclusion must plan nothing"
    );

    // The forged leaf: byte-identical shape to the sound bridge's leaf, but
    // claiming the read of the store is `w` instead of the stored `v`.
    let terms = &mut exec.ctx.terms;
    let select_store = terms.mk_app(Symbol::named("select"), [store, i], Sort::Int);
    let forged_row_eq = terms.mk_eq(select_store, w);
    let guard = terms.mk_not_raw(eq_zero_i);
    let mut forged = Proof::new();
    forged.add_step(ProofStep::TheoryLemma {
        theory: "Arrays".to_string(),
        clause: vec![guard, forged_row_eq],
        farkas: None,
        kind: TheoryLemmaKind::ArraySelectStore { index_eq: true },
        lia: None,
    });
    assert!(
        ay_proof::check_proof_strict(&forged, terms).is_err(),
        "the untouched strict checker must refuse a read-over-write leaf \
         whose value is not the stored one"
    );
}
