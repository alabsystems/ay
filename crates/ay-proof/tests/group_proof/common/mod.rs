// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Shared helpers are compiled into each integration-test binary separately, so
// any given test target legitimately uses only a subset of this module.
// Dead code warnings suppressed at module declaration in group_proof.rs

use ay_core::{FarkasAnnotation, Proof, Sort, Symbol, TermStore, TheoryLemmaKind};
use num_bigint::BigInt;

/// Build a structurally valid but semantically unsound proof:
/// x, y, FAKE_THEORY: (not x \/ not y) |- false.
pub(crate) fn build_unsound_theory_lemma_proof() -> (TermStore, Proof) {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let y = terms.mk_var("y", Sort::Bool);
    let not_x = terms.mk_not(x);
    let not_y = terms.mk_not(y);

    let mut proof = Proof::new();
    let h0 = proof.add_assume(x, None);
    let h1 = proof.add_assume(y, None);
    let tl = proof.add_theory_lemma("FAKE_THEORY", vec![not_x, not_y]);
    let r0 = proof.add_resolution(vec![not_y], x, tl, h0);
    proof.add_resolution(vec![], y, r0, h1);

    (terms, proof)
}

/// Build a semantically valid LRA Farkas proof:
/// x <= 5, x >= 10, LRA lemma: (not x<=5 \/ not x>=10) |- false.
pub(crate) fn build_valid_lra_farkas_proof() -> (TermStore, Proof) {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let five = terms.mk_rational(BigInt::from(5).into());
    let ten = terms.mk_rational(BigInt::from(10).into());

    let x_le_5 = terms.mk_le(x, five);
    let x_ge_10 = terms.mk_ge(x, ten);
    let not_x_le_5 = terms.mk_not(x_le_5);
    let not_x_ge_10 = terms.mk_not(x_ge_10);

    let mut proof = Proof::new();
    let h0 = proof.add_assume(x_le_5, None);
    let h1 = proof.add_assume(x_ge_10, None);
    let lemma = proof.add_theory_lemma_with_farkas_and_kind(
        "LRA",
        vec![not_x_le_5, not_x_ge_10],
        FarkasAnnotation::from_ints(&[1, 1]),
        TheoryLemmaKind::LraFarkas,
    );
    let r0 = proof.add_resolution(vec![not_x_ge_10], x_le_5, lemma, h0);
    proof.add_resolution(vec![], x_ge_10, r0, h1);

    (terms, proof)
}

/// Build a valid EUF transitive chain proof:
/// a=b, b=c, EUF lemma: (not a=b) \/ (not b=c) \/ (a=c) |- false.
pub(crate) fn build_valid_euf_transitive_proof() -> (TermStore, Proof) {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let c = terms.mk_var("c", Sort::Int);

    let a_eq_b = terms.mk_eq(a, b);
    let b_eq_c = terms.mk_eq(b, c);
    let a_eq_c = terms.mk_eq(a, c);
    let not_a_eq_b = terms.mk_not(a_eq_b);
    let not_b_eq_c = terms.mk_not(b_eq_c);
    let not_a_eq_c = terms.mk_not(a_eq_c);

    let mut proof = Proof::new();
    let h0 = proof.add_assume(a_eq_b, None);
    let h1 = proof.add_assume(b_eq_c, None);
    let h2 = proof.add_assume(not_a_eq_c, None);
    let lemma = proof.add_theory_lemma_with_kind(
        "EUF",
        vec![not_a_eq_b, not_b_eq_c, a_eq_c],
        TheoryLemmaKind::EufTransitive,
    );
    let r0 = proof.add_resolution(vec![not_b_eq_c, a_eq_c], a_eq_b, lemma, h0);
    let r1 = proof.add_resolution(vec![a_eq_c], b_eq_c, r0, h1);
    proof.add_resolution(vec![], a_eq_c, r1, h2);

    (terms, proof)
}

/// Build a valid EUF congruence proof:
/// a=b, EUF lemma: (not a=b) \/ f(a)=f(b) |- false.
pub(crate) fn build_valid_euf_congruent_proof() -> (TermStore, Proof) {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let a_eq_b = terms.mk_eq(a, b);
    let not_a_eq_b = terms.mk_not(a_eq_b);

    // f(a) and f(b) — uninterpreted function Int -> Int
    let f_sym = Symbol::Named("f".to_string());
    let fa = terms.mk_app(f_sym.clone(), vec![a], Sort::Int);
    let fb = terms.mk_app(f_sym, vec![b], Sort::Int);
    let fa_eq_fb = terms.mk_eq(fa, fb);
    let not_fa_eq_fb = terms.mk_not(fa_eq_fb);

    let mut proof = Proof::new();
    let h0 = proof.add_assume(a_eq_b, None);
    let h1 = proof.add_assume(not_fa_eq_fb, None);
    let lemma = proof.add_theory_lemma_with_kind(
        "EUF",
        vec![not_a_eq_b, fa_eq_fb],
        TheoryLemmaKind::EufCongruent,
    );
    let r0 = proof.add_resolution(vec![fa_eq_fb], a_eq_b, lemma, h0);
    proof.add_resolution(vec![], fa_eq_fb, r0, h1);

    (terms, proof)
}

/// Build a valid EUF congruent_pred proof:
/// a=b, p(a), EUF lemma: (not a=b) \/ (not p(a)) \/ p(b) |- false.
pub(crate) fn build_valid_euf_congruent_pred_proof() -> (TermStore, Proof) {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let a_eq_b = terms.mk_eq(a, b);
    let not_a_eq_b = terms.mk_not(a_eq_b);

    // p(a) and p(b) — uninterpreted predicate Int -> Bool
    let p_sym = Symbol::Named("p".to_string());
    let pa = terms.mk_app(p_sym.clone(), vec![a], Sort::Bool);
    let pb = terms.mk_app(p_sym, vec![b], Sort::Bool);
    let not_pa = terms.mk_not(pa);
    let not_pb = terms.mk_not(pb);

    let mut proof = Proof::new();
    let h0 = proof.add_assume(a_eq_b, None);
    let h1 = proof.add_assume(pa, None);
    let h2 = proof.add_assume(not_pb, None);
    let lemma = proof.add_theory_lemma_with_kind(
        "EUF",
        vec![not_a_eq_b, not_pa, pb],
        TheoryLemmaKind::EufCongruentPred,
    );
    let r0 = proof.add_resolution(vec![not_pa, pb], a_eq_b, lemma, h0);
    let r1 = proof.add_resolution(vec![pb], pa, r0, h1);
    proof.add_resolution(vec![], pb, r1, h2);

    (terms, proof)
}

/// Build a broken EUF transitive proof: a=b, c=d |- a=d (chain gap).
pub(crate) fn build_broken_euf_transitive_proof() -> (TermStore, Proof) {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let c = terms.mk_var("c", Sort::Int);
    let d = terms.mk_var("d", Sort::Int);

    let a_eq_b = terms.mk_eq(a, b);
    let c_eq_d = terms.mk_eq(c, d);
    let a_eq_d = terms.mk_eq(a, d);
    let not_a_eq_b = terms.mk_not(a_eq_b);
    let not_c_eq_d = terms.mk_not(c_eq_d);

    let mut proof = Proof::new();
    proof.add_assume(a_eq_b, None);
    proof.add_assume(c_eq_d, None);
    // This lemma is invalid: a=b, c=d does not connect a to d
    proof.add_theory_lemma_with_kind(
        "EUF",
        vec![not_a_eq_b, not_c_eq_d, a_eq_d],
        TheoryLemmaKind::EufTransitive,
    );

    (terms, proof)
}

/// Build a broken EUF congruent proof: a=b |- f(a)=g(b) (wrong symbol).
pub(crate) fn build_broken_euf_congruent_wrong_symbol_proof() -> (TermStore, Proof) {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let a_eq_b = terms.mk_eq(a, b);
    let not_a_eq_b = terms.mk_not(a_eq_b);

    let f_sym = Symbol::Named("f".to_string());
    let g_sym = Symbol::Named("g".to_string());
    let fa = terms.mk_app(f_sym, vec![a], Sort::Int);
    let gb = terms.mk_app(g_sym, vec![b], Sort::Int);
    let fa_eq_gb = terms.mk_eq(fa, gb);

    let mut proof = Proof::new();
    proof.add_assume(a_eq_b, None);
    proof.add_theory_lemma_with_kind(
        "EUF",
        vec![not_a_eq_b, fa_eq_gb],
        TheoryLemmaKind::EufCongruent,
    );

    (terms, proof)
}

/// Build a broken EUF congruent_pred proof with arity mismatch:
/// a=b, p(a,x) |- p(b) — different arities.
pub(crate) fn build_broken_euf_congruent_pred_arity_proof() -> (TermStore, Proof) {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let x = terms.mk_var("x", Sort::Int);
    let a_eq_b = terms.mk_eq(a, b);
    let not_a_eq_b = terms.mk_not(a_eq_b);

    let p_sym = Symbol::Named("p".to_string());
    let pa_x = terms.mk_app(p_sym.clone(), vec![a, x], Sort::Bool);
    let pb = terms.mk_app(p_sym, vec![b], Sort::Bool);
    let not_pa_x = terms.mk_not(pa_x);

    let mut proof = Proof::new();
    proof.add_assume(a_eq_b, None);
    proof.add_assume(pa_x, None);
    proof.add_theory_lemma_with_kind(
        "EUF",
        vec![not_a_eq_b, not_pa_x, pb],
        TheoryLemmaKind::EufCongruentPred,
    );

    (terms, proof)
}
