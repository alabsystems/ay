// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn row_chain_accepts_exact_store_congruence_direct_and_packed() {
    let mut f = Fixture::new(2);
    let a = f.a;
    let b = f.terms.mk_var("b", array_sort());
    let (index, value) = (f.idx[0], f.val[0]);
    let premise_eq = eq(&mut f.terms, a, b);
    let premise = f.terms.mk_not(premise_eq);
    let store_a = store(&mut f.terms, a, index, value);
    let store_b = store(&mut f.terms, b, index, value);
    let conclusion = eq(&mut f.terms, store_b, store_a);
    let direct = vec![premise, conclusion];

    validate_strict(&f.terms, direct.clone(), TheoryLemmaKind::ArrayRowChain)
        .expect("exact same-index/same-value store congruence must certify");
    assert!(
        array_row_chain_printer_terms(&f.terms, &direct).is_none(),
        "the ROW printer must fail closed on an unsupported store-congruence primitive"
    );

    let packed = f
        .terms
        .mk_app(Symbol::named("or"), direct.clone(), Sort::Bool);
    validate_strict(&f.terms, vec![packed], TheoryLemmaKind::ArrayRowChain)
        .expect("the exact packed-OR form emitted by AY must certify");

    let mut proof = Proof::new();
    let lemma = proof.add_theory_lemma_with_kind("arrays", direct, TheoryLemmaKind::ArrayRowChain);
    let guard = proof.add_assume(premise_eq, None);
    let unit_conclusion = proof.add_resolution(vec![conclusion], premise_eq, lemma, guard);
    let not_conclusion = f.terms.mk_not(conclusion);
    let contrary = proof.add_assume(not_conclusion, None);
    proof.add_resolution(vec![], conclusion, unit_conclusion, contrary);
    crate::check_proof_strict(&proof, &f.terms)
        .expect("exact store congruence must survive strict whole-proof replay");
}

#[test]
fn row_chain_rejects_packed_non_bool_equality_child() {
    let mut f = Fixture::new(1);
    let a = f.a;
    let b = f.terms.mk_var("b", array_sort());
    let (index, value) = (f.idx[0], f.val[0]);
    let premise_eq = eq(&mut f.terms, a, b);
    let premise = f.terms.mk_not_raw(premise_eq);
    let store_a = store(&mut f.terms, a, index, value);
    let store_b = store(&mut f.terms, b, index, value);
    let malformed_conclusion =
        f.terms
            .mk_app(Symbol::named("="), vec![store_a, store_b], Sort::Int);
    let packed = f.terms.mk_app(
        Symbol::named("or"),
        vec![premise, malformed_conclusion],
        Sort::Bool,
    );

    assert_eq!(
        recognize_array_theory_lemma(&f.terms, &[packed]),
        None,
        "classification must reject malformed packed children"
    );
    validate_strict(&f.terms, vec![packed], TheoryLemmaKind::ArrayRowChain)
        .expect_err("strict row replay must reject malformed packed children");
}

#[test]
fn row_chain_rejects_store_congruence_near_misses() {
    let mut f = Fixture::new(3);
    let a = f.a;
    let b = f.terms.mk_var("b", array_sort());
    let other = f.terms.mk_var("other", array_sort());
    let (index, wrong_index, value, wrong_value) = (f.idx[0], f.idx[1], f.val[0], f.val[1]);
    let premise_eq = eq(&mut f.terms, a, b);
    let premise = f.terms.mk_not(premise_eq);
    let wrong_guard_eq = eq(&mut f.terms, a, other);
    let wrong_guard = f.terms.mk_not(wrong_guard_eq);
    let store_a = store(&mut f.terms, a, index, value);
    let store_b = store(&mut f.terms, b, index, value);
    let store_b_wrong_index = store(&mut f.terms, b, wrong_index, value);
    let store_b_wrong_value = store(&mut f.terms, b, index, wrong_value);
    let store_other = store(&mut f.terms, other, index, value);
    let exact = eq(&mut f.terms, store_a, store_b);
    let wrong_root = eq(&mut f.terms, store_a, store_other);
    let wrong_index_conclusion = eq(&mut f.terms, store_a, store_b_wrong_index);
    let wrong_value_conclusion = eq(&mut f.terms, store_a, store_b_wrong_value);
    let bool_index = f.terms.mk_var("bool_store_index", Sort::Bool);
    let ill_sorted_store = f.terms.mk_app(
        Symbol::named("store"),
        vec![b, bool_index, value],
        array_sort(),
    );
    let wrong_sort = eq(&mut f.terms, store_a, ill_sorted_store);
    let extra = eq(&mut f.terms, index, wrong_index);

    for (label, clause) in [
        ("wrong guard", vec![wrong_guard, exact]),
        ("wrong root", vec![premise, wrong_root]),
        ("wrong index", vec![premise, wrong_index_conclusion]),
        ("wrong value", vec![premise, wrong_value_conclusion]),
        ("wrong sort", vec![premise, wrong_sort]),
        ("extra literal", vec![premise, exact, extra]),
    ] {
        validate_strict(&f.terms, clause, TheoryLemmaKind::ArrayRowChain).expect_err(label);
    }
}

#[test]
fn row_chain_accepts_exact_store_idempotence_under_equality() {
    let mut f = Fixture::new(2);
    let a = f.a;
    let b = f.terms.mk_var("b", array_sort());
    let (index, value) = (f.idx[0], f.val[0]);
    let stored = store(&mut f.terms, b, index, value);
    let premise_eq = eq(&mut f.terms, stored, a);
    let premise = f.terms.mk_not(premise_eq);
    let rewritten = store(&mut f.terms, a, index, value);
    let conclusion = eq(&mut f.terms, stored, rewritten);
    let clause = vec![conclusion, premise];

    validate_strict(&f.terms, clause.clone(), TheoryLemmaKind::ArrayRowChain)
        .expect("the exact depth-one store-idempotence rewrite must certify");
    assert!(array_row_chain_printer_terms(&f.terms, &clause).is_none());

    let mut proof = Proof::new();
    let lemma = proof.add_theory_lemma_with_kind("arrays", clause, TheoryLemmaKind::ArrayRowChain);
    let guard = proof.add_assume(premise_eq, None);
    let unit_conclusion = proof.add_resolution(vec![conclusion], premise_eq, lemma, guard);
    let not_conclusion = f.terms.mk_not(conclusion);
    let contrary = proof.add_assume(not_conclusion, None);
    proof.add_resolution(vec![], conclusion, unit_conclusion, contrary);
    crate::check_proof_strict(&proof, &f.terms)
        .expect("store idempotence must survive strict whole-proof replay");
}

#[test]
fn row_chain_rejects_store_idempotence_near_misses() {
    let mut f = Fixture::new(3);
    let a = f.a;
    let b = f.terms.mk_var("b", array_sort());
    let other = f.terms.mk_var("other", array_sort());
    let (index, wrong_index, value, wrong_value) = (f.idx[0], f.idx[1], f.val[0], f.val[1]);
    let stored = store(&mut f.terms, b, index, value);
    let premise_eq = eq(&mut f.terms, a, stored);
    let premise = f.terms.mk_not(premise_eq);
    let rewritten = store(&mut f.terms, a, index, value);
    let exact = eq(&mut f.terms, stored, rewritten);
    let wrong_splice_store = store(&mut f.terms, other, index, value);
    let wrong_splice = eq(&mut f.terms, stored, wrong_splice_store);
    let wrong_index_store = store(&mut f.terms, a, wrong_index, value);
    let wrong_index_conclusion = eq(&mut f.terms, stored, wrong_index_store);
    let wrong_value_store = store(&mut f.terms, a, index, wrong_value);
    let wrong_value_conclusion = eq(&mut f.terms, stored, wrong_value_store);
    let inner = store(&mut f.terms, b, wrong_index, wrong_value);
    let depth_two = store(&mut f.terms, inner, index, value);
    let depth_guard_eq = eq(&mut f.terms, a, depth_two);
    let depth_guard = f.terms.mk_not(depth_guard_eq);
    let depth_rewritten = store(&mut f.terms, a, index, value);
    let depth_conclusion = eq(&mut f.terms, depth_two, depth_rewritten);
    let bool_index = f.terms.mk_var("bool_idempotence_index", Sort::Bool);
    let ill_sorted = f.terms.mk_app(
        Symbol::named("store"),
        vec![a, bool_index, value],
        array_sort(),
    );
    let wrong_sort = eq(&mut f.terms, stored, ill_sorted);
    let negated_conclusion = f.terms.mk_not(exact);
    let extra = eq(&mut f.terms, index, wrong_index);

    for (label, clause) in [
        ("positive guard", vec![premise_eq, exact]),
        ("negative conclusion", vec![premise, negated_conclusion]),
        ("wrong A/B splice", vec![premise, wrong_splice]),
        ("different index", vec![premise, wrong_index_conclusion]),
        ("different value", vec![premise, wrong_value_conclusion]),
        ("depth-two stored term", vec![depth_guard, depth_conclusion]),
        ("ill-sorted raw store", vec![premise, wrong_sort]),
        ("extra literal", vec![premise, exact, extra]),
    ] {
        validate_strict(&f.terms, clause, TheoryLemmaKind::ArrayRowChain).expect_err(label);
    }
}

#[test]
fn row_chain_accepts_exact_guarded_matching_outer_store_reads() {
    let mut f = Fixture::new(3);
    let a = f.a;
    let c_root = f.terms.mk_var("c_root", array_sort());
    // Keep C non-atomic, as in the Seq proof. The generic ROW-chain lane
    // cannot walk through this inner store without another guard; schema (H)
    // must treat C as the exact outer-store base and inspect nothing below it.
    let c = store(&mut f.terms, c_root, f.idx[2], f.val[2]);
    let (store_index, read_index, value) = (f.idx[0], f.idx[1], f.val[0]);
    let left_store = store(&mut f.terms, a, store_index, value);
    let right_store = store(&mut f.terms, c, store_index, value);
    let premise_eq = eq(&mut f.terms, left_store, right_store);
    let premise = f.terms.mk_not(premise_eq);
    let guard = eq(&mut f.terms, store_index, read_index);
    let right_base_read = select(&mut f.terms, c, read_index);
    let left_store_read = select(&mut f.terms, left_store, read_index);
    let conclusion = eq(&mut f.terms, right_base_read, left_store_read);
    let direct = vec![guard, premise, conclusion];

    assert_eq!(
        recognize_array_theory_lemma(&f.terms, &direct),
        Some(TheoryLemmaKind::ArrayRowChain)
    );
    validate_strict(&f.terms, direct.clone(), TheoryLemmaKind::ArrayRowChain)
        .expect("the exact store/base form emitted by the Seq proof must certify");
    assert!(
        array_row_chain_printer_terms(&f.terms, &direct).is_none(),
        "the external printer must fail closed until it has an independent lowering"
    );

    let packed = f
        .terms
        .mk_app(Symbol::named("or"), direct.clone(), Sort::Bool);
    validate_strict(&f.terms, vec![packed], TheoryLemmaKind::ArrayRowChain)
        .expect("the packed-OR form must use the same exact checker lane");

    // Also cover the base/base form and equality orientations. The checker
    // treats each endpoint independently but keeps them on opposite sides.
    let left_base_read = select(&mut f.terms, a, read_index);
    let base_conclusion = eq(&mut f.terms, right_base_read, left_base_read);
    let reversed_premise_eq = eq(&mut f.terms, right_store, left_store);
    let reversed_premise = f.terms.mk_not(reversed_premise_eq);
    validate_strict(
        &f.terms,
        vec![base_conclusion, reversed_premise, guard],
        TheoryLemmaKind::ArrayRowChain,
    )
    .expect("the exact base/base and reversed-orientation form must certify");

    let mut proof = Proof::new();
    let lemma = proof.add_theory_lemma_with_kind("arrays", direct, TheoryLemmaKind::ArrayRowChain);
    let premise_assumption = proof.add_assume(premise_eq, None);
    let after_premise = proof.add_resolution(
        vec![guard, conclusion],
        premise_eq,
        lemma,
        premise_assumption,
    );
    let not_guard = f.terms.mk_not(guard);
    let guard_assumption = proof.add_assume(not_guard, None);
    let unit_conclusion =
        proof.add_resolution(vec![conclusion], guard, after_premise, guard_assumption);
    let not_conclusion = f.terms.mk_not(conclusion);
    let contrary = proof.add_assume(not_conclusion, None);
    proof.add_resolution(vec![], conclusion, unit_conclusion, contrary);
    crate::check_proof_strict(&proof, &f.terms)
        .expect("the guarded store-read lemma must survive strict whole-proof replay");
}

#[test]
fn row_chain_rejects_guarded_matching_outer_store_read_near_misses() {
    let mut f = Fixture::new(4);
    let a = f.a;
    let c_root = f.terms.mk_var("c_root", array_sort());
    let c = store(&mut f.terms, c_root, f.idx[3], f.val[2]);
    let other = f.terms.mk_var("other", array_sort());
    let (store_index, read_index, wrong_index, value, wrong_value) =
        (f.idx[0], f.idx[1], f.idx[2], f.val[0], f.val[1]);
    let left_store = store(&mut f.terms, a, store_index, value);
    let right_store = store(&mut f.terms, c, store_index, value);
    let premise_eq = eq(&mut f.terms, left_store, right_store);
    let premise = f.terms.mk_not(premise_eq);
    let guard = eq(&mut f.terms, store_index, read_index);
    let wrong_guard = eq(&mut f.terms, wrong_index, read_index);
    let negative_guard = f.terms.mk_not(guard);
    let left_store_read = select(&mut f.terms, left_store, read_index);
    let right_base_read = select(&mut f.terms, c, read_index);
    let exact = eq(&mut f.terms, left_store_read, right_base_read);
    let negative_conclusion = f.terms.mk_not(exact);
    let wrong_root_read = select(&mut f.terms, other, read_index);
    let wrong_root = eq(&mut f.terms, left_store_read, wrong_root_read);
    let right_wrong_read = select(&mut f.terms, c, wrong_index);
    let wrong_read_index = eq(&mut f.terms, left_store_read, right_wrong_read);
    let right_wrong_outer_index = store(&mut f.terms, c, wrong_index, value);
    let wrong_index_premise_eq = eq(&mut f.terms, left_store, right_wrong_outer_index);
    let wrong_index_premise = f.terms.mk_not(wrong_index_premise_eq);
    let right_wrong_value = store(&mut f.terms, c, store_index, wrong_value);
    let wrong_value_premise_eq = eq(&mut f.terms, left_store, right_wrong_value);
    let wrong_value_premise = f.terms.mk_not(wrong_value_premise_eq);
    let extra = eq(&mut f.terms, read_index, wrong_index);

    for (label, clause) in [
        ("missing guard", vec![premise, exact]),
        ("wrong guard", vec![wrong_guard, premise, exact]),
        ("negative guard", vec![negative_guard, premise, exact]),
        ("positive premise", vec![guard, premise_eq, exact]),
        (
            "different outer index",
            vec![guard, wrong_index_premise, exact],
        ),
        (
            "different outer value",
            vec![guard, wrong_value_premise, exact],
        ),
        ("wrong read root", vec![guard, premise, wrong_root]),
        (
            "different read indices",
            vec![guard, premise, wrong_read_index],
        ),
        (
            "negative conclusion",
            vec![guard, premise, negative_conclusion],
        ),
        ("extra literal", vec![guard, premise, exact, extra]),
    ] {
        validate_strict(&f.terms, clause, TheoryLemmaKind::ArrayRowChain).expect_err(label);
    }
}
