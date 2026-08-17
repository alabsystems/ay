// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// ============================================================================
// ArrayRowChain — sub-schema (A), chain evaluation
// ============================================================================

#[test]
fn row_chain_accepts_chain_read_with_all_skips_justified() {
    // (cl (= i0 i2) (= i0 i1) (= (select (store (store (store a i0 v0) i1 v1) i2 v2) i0) v0))
    // Reading at i0 skips the i2 and i1 writes; both skips carry their literal.
    let mut f = Fixture::new(3);
    let a = f.a;
    let chain = f.chain(a, &[0, 1, 2]);
    let i0 = f.idx[0];
    let v0 = f.val[0];
    let read = select(&mut f.terms, chain, i0);
    let conclusion = eq(&mut f.terms, read, v0);
    let (i1, i2) = (f.idx[1], f.idx[2]);
    let skip1 = eq(&mut f.terms, i0, i1);
    let skip2 = eq(&mut f.terms, i0, i2);

    validate_strict(
        &f.terms,
        vec![skip2, skip1, conclusion],
        TheoryLemmaKind::ArrayRowChain,
    )
    .expect("a fully-justified chain read must certify");
}

#[test]
fn row_chain_rejects_chain_read_with_an_unjustified_skip() {
    // NEGATIVE: the `(= i0 i1)` literal is missing, so nothing rules out
    // i0 = i1, under which the read yields v1, not v0.
    let mut f = Fixture::new(3);
    let a = f.a;
    let chain = f.chain(a, &[0, 1, 2]);
    let i0 = f.idx[0];
    let v0 = f.val[0];
    let read = select(&mut f.terms, chain, i0);
    let conclusion = eq(&mut f.terms, read, v0);
    let i2 = f.idx[2];
    let skip2 = eq(&mut f.terms, i0, i2);

    let err = validate_strict(
        &f.terms,
        vec![skip2, conclusion],
        TheoryLemmaKind::ArrayRowChain,
    )
    .expect_err("an unjustified store skip must be rejected");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { .. }),
        "expected InvalidTheoryLemma, got {err:?}"
    );
}

#[test]
fn row_chain_rejects_wrong_evaluated_value() {
    // NEGATIVE: every skip is justified, but the clause claims the read equals
    // v1 rather than the actual v0.
    let mut f = Fixture::new(3);
    let a = f.a;
    let chain = f.chain(a, &[0, 1, 2]);
    let i0 = f.idx[0];
    let v1 = f.val[1];
    let read = select(&mut f.terms, chain, i0);
    let conclusion = eq(&mut f.terms, read, v1);
    let (i1, i2) = (f.idx[1], f.idx[2]);
    let skip1 = eq(&mut f.terms, i0, i1);
    let skip2 = eq(&mut f.terms, i0, i2);

    let err = validate_strict(
        &f.terms,
        vec![skip2, skip1, conclusion],
        TheoryLemmaKind::ArrayRowChain,
    )
    .expect_err("a mis-evaluated chain read must be rejected");
    assert!(
        matches!(err, ProofCheckError::InvalidTheoryLemma { .. }),
        "expected InvalidTheoryLemma, got {err:?}"
    );
}

#[test]
fn row_chain_accepts_read_falling_through_to_the_base_array() {
    // Every write is skipped, so the read is the base array's own read.
    let mut f = Fixture::new(3);
    let a = f.a;
    let chain = f.chain(a, &[1, 2]);
    let i0 = f.idx[0];
    let read = select(&mut f.terms, chain, i0);
    let base_read = select(&mut f.terms, a, i0);
    let conclusion = eq(&mut f.terms, read, base_read);
    let (i1, i2) = (f.idx[1], f.idx[2]);
    let skip1 = eq(&mut f.terms, i0, i1);
    let skip2 = eq(&mut f.terms, i0, i2);

    validate_strict(
        &f.terms,
        vec![skip1, skip2, conclusion],
        TheoryLemmaKind::ArrayRowChain,
    )
    .expect("a fully-skipped chain read must reduce to the base read");
}

// ============================================================================
// ArrayRowChain — sub-schema (B), read-out under an array equality
// ============================================================================

#[test]
fn row_chain_accepts_read_out_under_array_equality() {
    // read5's shape:
    //   (cl (= i0 i2) (not (= (store (store a i0 v0) i2 v2) b))
    //       (= v0 (select b i0)))
    // If the two arrays are equal and i0 != i2, reading both at i0 gives
    // v0 on the left and (select b i0) on the right.
    let mut f = Fixture::new(3);
    let a = f.a;
    let b = f.terms.mk_var("b", array_sort());
    let left = f.chain(a, &[0, 2]);
    let premise_eq = eq(&mut f.terms, left, b);
    let premise = f.terms.mk_not(premise_eq);
    let i0 = f.idx[0];
    let i2 = f.idx[2];
    let v0 = f.val[0];
    let base_read = select(&mut f.terms, b, i0);
    let conclusion = eq(&mut f.terms, v0, base_read);
    let skip = eq(&mut f.terms, i0, i2);

    validate_strict(
        &f.terms,
        vec![skip, premise, conclusion],
        TheoryLemmaKind::ArrayRowChain,
    )
    .expect("a justified read-out under an array equality must certify");
}

#[test]
fn row_chain_accepts_one_folded_and_one_exact_root_read() {
    // This is the shape emitted by sequence-layout proofs:
    //   L = store(B, x, v), R = store(B, y, v)
    //   (cl (not (= L R)) (= v (select R x)))
    // Under L = R, congruence transports the checked ROW1 fact L[x] = v to
    // R[x].  Evaluating R[x] itself would incorrectly require x != y; it is
    // deliberately retained as the exact root read.
    let mut f = Fixture::new(2);
    let b = f.a;
    let (x, y, v) = (f.idx[0], f.idx[1], f.val[0]);
    let left = store(&mut f.terms, b, x, v);
    let right = store(&mut f.terms, b, y, v);
    let premise_eq = eq(&mut f.terms, left, right);
    let premise = f.terms.mk_not(premise_eq);
    let right_read = select(&mut f.terms, right, x);
    let conclusion = eq(&mut f.terms, v, right_read);
    let clause = vec![premise, conclusion];

    assert_eq!(
        recognize_array_theory_lemma(&f.terms, &clause),
        Some(TheoryLemmaKind::ArrayRowChain)
    );
    validate_strict(&f.terms, clause.clone(), TheoryLemmaKind::ArrayRowChain)
        .expect("one checked ROW side plus one exact root read must certify");
    assert!(
        array_row_chain_printer_terms(&f.terms, &clause).is_some(),
        "the external printer must be able to replay the same exact schema"
    );
}

#[test]
fn row_chain_accepts_guarded_fallthrough_to_const_array_fill() {
    //   (cl (not (= A (store (const-array 0) 0 v)))
    //       (= 0 x)
    //       (= 0 (select A x)))
    // When A equals the store and x != 0, ROW2 reaches the constant-array
    // root, whose read is exactly its fill value.
    let mut terms = TermStore::new();
    let zero = terms.mk_int(0.into());
    let x = terms.mk_var("x", Sort::Int);
    let v = terms.mk_var("v", Sort::Int);
    let constant = terms.mk_const_array(Sort::Int, zero);
    let folded = store(&mut terms, constant, zero, v);
    let a = terms.mk_var("A", array_sort());
    let premise_eq = eq(&mut terms, a, folded);
    let premise = terms.mk_not(premise_eq);
    let guard = eq(&mut terms, zero, x);
    let read = select(&mut terms, a, x);
    let conclusion = eq(&mut terms, zero, read);
    let clause = vec![premise, guard, conclusion];

    assert_eq!(
        recognize_array_theory_lemma(&terms, &clause),
        Some(TheoryLemmaKind::ArrayRowChain)
    );
    validate_strict(&terms, clause, TheoryLemmaKind::ArrayRowChain)
        .expect("a guarded store fallthrough to its const-array fill must certify");
}

#[test]
fn row_chain_rejects_unjustified_or_wrong_const_array_fallthrough() {
    let mut terms = TermStore::new();
    let zero = terms.mk_int(0.into());
    let one = terms.mk_int(1.into());
    let x = terms.mk_var("x", Sort::Int);
    let v = terms.mk_var("v", Sort::Int);
    let constant = terms.mk_const_array(Sort::Int, zero);
    let folded = store(&mut terms, constant, zero, v);
    let a = terms.mk_var("A", array_sort());
    let premise_eq = eq(&mut terms, a, folded);
    let premise = terms.mk_not(premise_eq);
    let read = select(&mut terms, a, x);
    let conclusion = eq(&mut terms, zero, read);

    validate_strict(
        &terms,
        vec![premise, conclusion],
        TheoryLemmaKind::ArrayRowChain,
    )
    .expect_err("falling through a store requires its exact index-disequality guard");

    let guard = eq(&mut terms, zero, x);
    let wrong_conclusion = eq(&mut terms, one, read);
    validate_strict(
        &terms,
        vec![premise, guard, wrong_conclusion],
        TheoryLemmaKind::ArrayRowChain,
    )
    .expect_err("a const-array fallthrough must use the exact fill value");
}

#[test]
fn row_chain_accepts_equal_distinct_stores_forcing_base_alias() {
    let mut f = Fixture::new(2);
    let b = f.a;
    let a = f.terms.mk_var("store-alias-a", array_sort());
    let (i, j, v) = (f.idx[0], f.idx[1], f.val[0]);
    let store_i = store(&mut f.terms, b, i, v);
    let store_j = store(&mut f.terms, b, j, v);
    let a_eq_i = eq(&mut f.terms, a, store_i);
    let not_a_eq_i = f.terms.mk_not(a_eq_i);
    let j_eq_a = eq(&mut f.terms, store_j, a);
    let not_j_eq_a = f.terms.mk_not(j_eq_a);
    let index_guard = eq(&mut f.terms, j, i);
    let base_alias = eq(&mut f.terms, a, b);
    let clause = vec![not_j_eq_a, base_alias, index_guard, not_a_eq_i];

    assert_eq!(
        recognize_array_theory_lemma(&f.terms, &clause),
        Some(TheoryLemmaKind::ArrayRowChain)
    );
    validate_strict(&f.terms, clause, TheoryLemmaKind::ArrayRowChain)
        .expect("equal same-value stores at distinct indices force the base alias");
}

#[test]
fn row_chain_rejects_forged_equal_stores_base_alias_variants() {
    let mut f = Fixture::new(3);
    let b = f.a;
    let other_base = f.terms.mk_var("store-alias-other-base", array_sort());
    let a = f.terms.mk_var("store-alias-a", array_sort());
    let other_anchor = f.terms.mk_var("store-alias-other-a", array_sort());
    let (i, j, wrong_index, v, wrong_value) = (f.idx[0], f.idx[1], f.idx[2], f.val[0], f.val[1]);
    let store_i = store(&mut f.terms, b, i, v);
    let store_j = store(&mut f.terms, b, j, v);
    let base_clause = |terms: &mut TermStore,
                       second_store: TermId,
                       second_anchor: TermId,
                       guard_rhs: TermId,
                       alias_base: TermId| {
        let first_eq = eq(terms, a, store_i);
        let first = terms.mk_not(first_eq);
        let second_eq = eq(terms, second_anchor, second_store);
        let second = terms.mk_not(second_eq);
        let guard = eq(terms, i, guard_rhs);
        let alias = eq(terms, alias_base, a);
        vec![first, second, guard, alias]
    };

    for (label, clause) in [
        (
            "different anchor",
            base_clause(&mut f.terms, store_j, other_anchor, j, b),
        ),
        (
            "wrong index guard",
            base_clause(&mut f.terms, store_j, a, wrong_index, b),
        ),
        (
            "wrong base conclusion",
            base_clause(&mut f.terms, store_j, a, j, other_base),
        ),
        ("different store base", {
            let other_store = store(&mut f.terms, other_base, j, v);
            base_clause(&mut f.terms, other_store, a, j, b)
        }),
        ("different stored value", {
            let other_store = store(&mut f.terms, b, j, wrong_value);
            base_clause(&mut f.terms, other_store, a, j, b)
        }),
    ] {
        validate_strict(&f.terms, clause, TheoryLemmaKind::ArrayRowChain).expect_err(label);
    }
}

#[test]
fn row_chain_accepts_root_read_schema_with_swapped_orientations() {
    let mut f = Fixture::new(2);
    let b = f.a;
    let (x, y, v) = (f.idx[0], f.idx[1], f.val[0]);
    let left = store(&mut f.terms, b, x, v);
    let right = store(&mut f.terms, b, y, v);
    let premise_eq = eq(&mut f.terms, right, left);
    let premise = f.terms.mk_not(premise_eq);
    let right_read = select(&mut f.terms, right, x);
    let conclusion = eq(&mut f.terms, right_read, v);
    let clause = vec![conclusion, premise];

    validate_strict(&f.terms, clause.clone(), TheoryLemmaKind::ArrayRowChain)
        .expect("equality and clause orientation must not affect the schema");
    assert!(array_row_chain_printer_terms(&f.terms, &clause).is_some());
}

#[test]
fn row_chain_accepts_exact_pure_root_read_congruence() {
    let mut f = Fixture::new(2);
    let b = f.a;
    let (x, y, v) = (f.idx[0], f.idx[1], f.val[0]);
    let left = store(&mut f.terms, b, x, v);
    let right = store(&mut f.terms, b, y, v);
    let premise_eq = eq(&mut f.terms, left, right);
    let premise = f.terms.mk_not(premise_eq);
    let left_read = select(&mut f.terms, left, y);
    let right_read = select(&mut f.terms, right, y);
    let conclusion = eq(&mut f.terms, left_read, right_read);
    let clause = vec![premise, conclusion];

    validate_strict(&f.terms, clause.clone(), TheoryLemmaKind::ArrayRowChain)
        .expect("the exact two-literal select-congruence schema must certify");
    assert!(array_row_chain_printer_terms(&f.terms, &clause).is_some());

    // Replay the lemma inside a complete strict proof, rather than testing
    // only the isolated theory-step validator.
    let mut proof = Proof::new();
    let lemma = proof.add_theory_lemma_with_kind("arrays", clause, TheoryLemmaKind::ArrayRowChain);
    let guard = proof.add_assume(premise_eq, None);
    let unit_conclusion = proof.add_resolution(vec![conclusion], premise_eq, lemma, guard);
    let not_conclusion = f.terms.mk_not(conclusion);
    let contrary = proof.add_assume(not_conclusion, None);
    proof.add_resolution(vec![], conclusion, unit_conclusion, contrary);
    crate::check_proof_strict(&proof, &f.terms)
        .expect("exact select congruence must survive strict whole-proof replay");
}

#[test]
fn row_chain_rejects_near_miss_pure_root_read_congruence() {
    let mut f = Fixture::new(3);
    let a = f.a;
    let b = f.terms.mk_var("b", array_sort());
    let other = f.terms.mk_var("other", array_sort());
    let (i, j) = (f.idx[0], f.idx[1]);
    let premise_eq = eq(&mut f.terms, a, b);
    let premise = f.terms.mk_not(premise_eq);
    let read_a_i = select(&mut f.terms, a, i);
    let read_b_i = select(&mut f.terms, b, i);
    let read_b_j = select(&mut f.terms, b, j);
    let read_other_i = select(&mut f.terms, other, i);
    let exact = eq(&mut f.terms, read_a_i, read_b_i);
    let wrong_index = eq(&mut f.terms, read_a_i, read_b_j);
    let wrong_root = eq(&mut f.terms, read_a_i, read_other_i);
    let wrong_guard_eq = eq(&mut f.terms, a, other);
    let wrong_guard = f.terms.mk_not(wrong_guard_eq);
    let bool_index = f.terms.mk_var("bool_index", Sort::Bool);
    let ill_sorted_read = f
        .terms
        .mk_app(Symbol::named("select"), vec![b, bool_index], Sort::Int);
    let wrong_sort = eq(&mut f.terms, read_a_i, ill_sorted_read);
    let extra = eq(&mut f.terms, i, j);

    for (label, clause) in [
        ("wrong guard", vec![wrong_guard, exact]),
        ("wrong index", vec![premise, wrong_index]),
        ("wrong root", vec![premise, wrong_root]),
        ("wrong sort", vec![premise, wrong_sort]),
        ("extra literal", vec![premise, exact, extra]),
    ] {
        validate_strict(&f.terms, clause.clone(), TheoryLemmaKind::ArrayRowChain).expect_err(label);
        assert!(
            array_row_chain_printer_terms(&f.terms, &clause).is_none(),
            "{label}"
        );
    }
}

#[test]
fn row_chain_accepts_exact_const_array_read_under_equality() {
    let mut f = Fixture::new(1);
    let a = f.a;
    let i = f.idx[0];
    let fill = f.val[0];
    let constant = f.terms.mk_const_array(Sort::Int, fill);
    let premise_eq = eq(&mut f.terms, constant, a);
    let premise = f.terms.mk_not(premise_eq);
    let read = select(&mut f.terms, a, i);
    let conclusion = eq(&mut f.terms, fill, read);
    let clause = vec![conclusion, premise];

    validate_strict(&f.terms, clause.clone(), TheoryLemmaKind::ArrayRowChain)
        .expect("an exact root read under equality with a const-array must certify");

    let mut proof = Proof::new();
    let lemma = proof.add_theory_lemma_with_kind("arrays", clause, TheoryLemmaKind::ArrayRowChain);
    let guard = proof.add_assume(premise_eq, None);
    let unit_conclusion = proof.add_resolution(vec![conclusion], premise_eq, lemma, guard);
    let not_conclusion = f.terms.mk_not(conclusion);
    let contrary = proof.add_assume(not_conclusion, None);
    proof.add_resolution(vec![], conclusion, unit_conclusion, contrary);
    crate::check_proof_strict(&proof, &f.terms)
        .expect("const-array equality read must survive strict whole-proof replay");
}

#[test]
fn row_chain_rejects_const_array_read_near_misses() {
    let mut f = Fixture::new(3);
    let a = f.a;
    let b = f.terms.mk_var("b", array_sort());
    let (i, j, fill, wrong_fill) = (f.idx[0], f.idx[1], f.val[0], f.val[1]);
    let constant = f.terms.mk_const_array(Sort::Int, fill);
    let premise_eq = eq(&mut f.terms, a, constant);
    let premise = f.terms.mk_not(premise_eq);
    let wrong_guard_eq = eq(&mut f.terms, a, b);
    let wrong_guard = f.terms.mk_not(wrong_guard_eq);
    let read_a_i = select(&mut f.terms, a, i);
    let read_a_j = select(&mut f.terms, a, j);
    let read_b_i = select(&mut f.terms, b, i);
    let exact = eq(&mut f.terms, read_a_i, fill);
    let wrong_guard_conclusion = eq(&mut f.terms, read_a_i, fill);
    let wrong_root = eq(&mut f.terms, read_b_i, fill);
    let wrong_fill_conclusion = eq(&mut f.terms, read_a_i, wrong_fill);
    let extra = eq(&mut f.terms, read_a_j, fill);

    for (label, clause) in [
        ("wrong guard", vec![wrong_guard, wrong_guard_conclusion]),
        ("wrong root", vec![premise, wrong_root]),
        ("wrong fill", vec![premise, wrong_fill_conclusion]),
        ("extra literal", vec![premise, exact, extra]),
    ] {
        validate_strict(&f.terms, clause, TheoryLemmaKind::ArrayRowChain).expect_err(label);
    }
}
