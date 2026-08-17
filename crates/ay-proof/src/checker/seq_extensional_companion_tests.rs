// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::{ProofId, Sort, TermId, TermStore};
use num_bigint::BigInt;
use num_traits::Zero;

use super::{recognize, validate};

struct Fixture {
    terms: TermStore,
    roots: [TermId; 5],
    lower: TermId,
    len: TermId,
    other_len: TermId,
    c1: TermId,
    c2: TermId,
    a: TermId,
    b: TermId,
    equality: TermId,
    positive_len: TermId,
    tail_equality: TermId,
}

fn guarded_pin(
    terms: &mut TermStore,
    lower: TermId,
    len: TermId,
    companion: TermId,
    equality_first: bool,
) -> TermId {
    let nat = terms.mk_bv2nat(companion);
    let equality = terms.mk_eq(len, nat);
    let not_lower = terms.mk_not_raw(lower);
    let disjuncts = if equality_first {
        vec![equality, not_lower]
    } else {
        vec![not_lower, equality]
    };
    terms.mk_or(disjuncts)
}

fn pointwise(
    terms: &mut TermStore,
    binder_name: &str,
    companion: TermId,
    a: TermId,
    b: TermId,
) -> TermId {
    pointwise_with_triggers(terms, binder_name, companion, a, b, false)
}

fn pointwise_with_triggers(
    terms: &mut TermStore,
    binder_name: &str,
    companion: TermId,
    a: TermId,
    b: TermId,
    triggered: bool,
) -> TermId {
    let sort = terms.sort(companion).clone();
    let index = terms.mk_var(binder_name, sort);
    pointwise_from_index(terms, binder_name, index, companion, a, b, triggered)
}

fn pointwise_from_index(
    terms: &mut TermStore,
    binder_name: &str,
    index: TermId,
    companion: TermId,
    a: TermId,
    b: TermId,
    triggered: bool,
) -> TermId {
    pointwise_from_index_with_trigger_layout(
        terms,
        binder_name,
        index,
        companion,
        a,
        b,
        if triggered { 1 } else { 0 },
    )
}

fn pointwise_from_index_with_trigger_layout(
    terms: &mut TermStore,
    binder_name: &str,
    index: TermId,
    companion: TermId,
    a: TermId,
    b: TermId,
    trigger_layout: u8,
) -> TermId {
    let left = terms.mk_select(a, index);
    let right = terms.mk_select(b, index);
    let elements_equal = terms.mk_eq(left, right);
    let in_bounds = terms.mk_bvult(index, companion);
    let not_in_bounds = terms.mk_not_raw(in_bounds);
    let body = terms.mk_or(vec![elements_equal, not_in_bounds]);
    let triggers = match trigger_layout {
        0 => Vec::new(),
        1 => vec![vec![left], vec![right]],
        2 => vec![vec![right], vec![left]],
        3 => vec![vec![left], vec![right], vec![left]],
        4 => vec![vec![left], vec![left]],
        5 => vec![Vec::new(); super::PAIR_WORK_LIMIT + 1],
        _ => unreachable!("test trigger layout"),
    };
    terms.mk_forall_with_triggers(
        vec![(binder_name.to_string(), terms.sort(index).clone())],
        body,
        triggers,
    )
}

fn roots_with_quantifiers(f: &mut Fixture, q1: TermId, q2: TermId) -> [TermId; 5] {
    let not_positive_len = f.terms.mk_not_raw(f.positive_len);
    let tail = f.terms.mk_or(vec![f.tail_equality, not_positive_len]);
    let positive = f.terms.mk_and(vec![f.equality, q1, tail]);
    let not_equality = f.terms.mk_not_raw(f.equality);
    let not_tail = f.terms.mk_not_raw(f.tail_equality);
    let tail_dual = f.terms.mk_and(vec![f.positive_len, not_tail]);
    let not_q2 = f.terms.mk_not_raw(q2);
    let negative = f.terms.mk_or(vec![not_equality, tail_dual, not_q2]);
    [f.lower, f.roots[1], f.roots[2], positive, negative]
}

fn fixture() -> Fixture {
    let mut terms = TermStore::new();
    let len = terms.mk_var("seq_len", Sort::Int);
    let other_len = terms.mk_var("seq_other_len", Sort::Int);
    let zero = terms.mk_int(BigInt::zero());
    let lower = terms.mk_le(zero, len);
    let c1 = terms.mk_var("seq_companion_1", Sort::bitvec(8));
    let c2 = terms.mk_var("seq_companion_2", Sort::bitvec(8));
    let pin1 = guarded_pin(&mut terms, lower, len, c1, true);
    let pin2 = guarded_pin(&mut terms, lower, len, c2, false);

    let array_sort = Sort::array(Sort::bitvec(8), Sort::Int);
    let a = terms.mk_var("seq_array_a", array_sort.clone());
    let b = terms.mk_var("seq_array_b", array_sort);
    let q1 = pointwise(&mut terms, "seq_q1_i", c1, a, b);
    let q2 = pointwise(&mut terms, "seq_q2_i", c2, a, b);
    let equality = terms.mk_eq(len, other_len);
    let positive_len = terms.mk_lt(zero, len);
    let tail_equality = terms.mk_eq(a, b);
    let not_positive_len = terms.mk_not_raw(positive_len);
    let tail = terms.mk_or(vec![tail_equality, not_positive_len]);
    let positive = terms.mk_and(vec![equality, q1, tail]);
    let not_equality = terms.mk_not_raw(equality);
    let not_tail = terms.mk_not_raw(tail_equality);
    let tail_dual = terms.mk_and(vec![positive_len, not_tail]);
    let not_q2 = terms.mk_not_raw(q2);
    let negative = terms.mk_or(vec![not_equality, tail_dual, not_q2]);

    Fixture {
        terms,
        roots: [lower, pin1, pin2, positive, negative],
        lower,
        len,
        other_len,
        c1,
        c2,
        a,
        b,
        equality,
        positive_len,
        tail_equality,
    }
}

fn clause(terms: &mut TermStore, roots: &[TermId; 5]) -> Vec<TermId> {
    roots.iter().map(|&root| terms.mk_not_raw(root)).collect()
}

#[test]
fn exact_schema_accepts_both_pin_operand_orders_and_public_subset() {
    let mut f = fixture();
    let exact_clause = clause(&mut f.terms, &f.roots);
    validate(&f.terms, ProofId(0), &exact_clause).expect("exact theorem must validate");

    let unrelated = f.terms.mk_eq(f.other_len, f.other_len);
    let mut public = vec![unrelated];
    public.extend(f.roots);
    assert_eq!(recognize(&f.terms, &public), Some(f.roots));

    let reversed_pins = [f.roots[0], f.roots[2], f.roots[1], f.roots[3], f.roots[4]];
    assert_eq!(
        recognize(&f.terms, &reversed_pins),
        Some(f.roots),
        "public root order must not assign the two companion roles"
    );
}

#[test]
fn schema_rejects_width_guard_and_pointwise_near_misses() {
    let mut f = fixture();

    let wrong_width = f.terms.mk_var("seq_companion_wide", Sort::bitvec(16));
    let wrong_pin = guarded_pin(&mut f.terms, f.lower, f.len, wrong_width, true);
    let not_equality = f.terms.mk_not_raw(f.equality);
    let not_tail = f.terms.mk_not_raw(f.tail_equality);
    let tail_dual = f.terms.mk_and(vec![f.positive_len, not_tail]);
    let roots = [f.lower, f.roots[1], wrong_pin, f.roots[3], f.roots[4]];
    let forged = clause(&mut f.terms, &roots);
    assert!(validate(&f.terms, ProofId(0), &forged).is_err());

    let other_zero = f.terms.mk_int(BigInt::zero());
    let other_lower = f.terms.mk_le(other_zero, f.other_len);
    let wrong_guard_pin = guarded_pin(&mut f.terms, other_lower, f.len, f.c2, true);
    let roots = [f.lower, f.roots[1], wrong_guard_pin, f.roots[3], f.roots[4]];
    let forged = clause(&mut f.terms, &roots);
    assert!(validate(&f.terms, ProofId(0), &forged).is_err());

    let other_array = f
        .terms
        .mk_var("seq_other_array", Sort::array(Sort::bitvec(8), Sort::Int));
    let changed_q = pointwise(&mut f.terms, "seq_changed_i", f.c2, f.a, other_array);
    let not_changed_q = f.terms.mk_not_raw(changed_q);
    let changed_negative = f.terms.mk_or(vec![not_equality, tail_dual, not_changed_q]);
    let roots = [
        f.lower,
        f.roots[1],
        f.roots[2],
        f.roots[3],
        changed_negative,
    ];
    let forged = clause(&mut f.terms, &roots);
    assert!(validate(&f.terms, ProofId(0), &forged).is_err());
}

#[test]
fn schema_rejects_missing_duplicate_and_non_public_roots() {
    let mut f = fixture();
    let mut duplicate = f.roots;
    duplicate[2] = duplicate[1];
    let forged = clause(&mut f.terms, &duplicate);
    assert!(validate(&f.terms, ProofId(0), &forged).is_err());

    let absent = f.terms.mk_var("absent_public_root", Sort::Bool);
    let public = [f.roots[0], f.roots[1], f.roots[2], f.roots[3], absent];
    assert!(recognize(&f.terms, &public).is_none());

    let malformed_clause = vec![f.roots[0]; 5];
    assert!(validate(&f.terms, ProofId(0), &malformed_clause).is_err());
}

#[test]
fn schema_accepts_matching_trigger_annotations() {
    let mut f = fixture();
    let q1 = pointwise_with_triggers(&mut f.terms, "seq_trigger_1", f.c1, f.a, f.b, true);
    let q2 = pointwise_with_triggers(&mut f.terms, "seq_trigger_2", f.c2, f.a, f.b, true);
    let roots = roots_with_quantifiers(&mut f, q1, q2);
    let exact = clause(&mut f.terms, &roots);
    validate(&f.terms, ProofId(0), &exact).expect("matching trigger renaming must validate");
    assert_eq!(recognize(&f.terms, &roots), Some(roots));
}

#[test]
fn schema_rejects_trigger_mismatches_and_companion_shadowing() {
    let mut f = fixture();

    let triggered =
        pointwise_with_triggers(&mut f.terms, "seq_trigger_mismatch", f.c2, f.a, f.b, true);
    let plain_q1 = pointwise(&mut f.terms, "seq_trigger_plain_1", f.c1, f.a, f.b);
    let roots = roots_with_quantifiers(&mut f, plain_q1, triggered);
    let forged = clause(&mut f.terms, &roots);
    assert!(validate(&f.terms, ProofId(0), &forged).is_err());

    for layout in [2, 3, 4, 5] {
        let sort = f.terms.sort(f.c1).clone();
        let index1 = f.terms.mk_var("seq_trigger_order_1", sort.clone());
        let index2 = f.terms.mk_var("seq_trigger_order_2", sort);
        let q1 = pointwise_from_index_with_trigger_layout(
            &mut f.terms,
            "seq_trigger_order_1",
            index1,
            f.c1,
            f.a,
            f.b,
            if layout == 5 { 5 } else { 1 },
        );
        let q2 = pointwise_from_index_with_trigger_layout(
            &mut f.terms,
            "seq_trigger_order_2",
            index2,
            f.c2,
            f.a,
            f.b,
            layout,
        );
        let roots = roots_with_quantifiers(&mut f, q1, q2);
        let forged = clause(&mut f.terms, &roots);
        assert!(validate(&f.terms, ProofId(0), &forged).is_err());
    }

    let shadowed = pointwise_with_triggers(&mut f.terms, "seq_companion_2", f.c2, f.a, f.b, false);
    let plain_q1 = pointwise(&mut f.terms, "seq_shadow_plain_1", f.c1, f.a, f.b);
    let roots = roots_with_quantifiers(&mut f, plain_q1, shadowed);
    let forged = clause(&mut f.terms, &roots);
    assert!(validate(&f.terms, ProofId(0), &forged).is_err());
}

#[test]
fn schema_rejects_binder_capture_inside_shared_subterm() {
    let mut f = fixture();
    let binder1 = f.terms.mk_var("seq_capture_i1", Sort::bitvec(8));
    let binder2 = f.terms.mk_var("seq_capture_i2", Sort::bitvec(8));
    let condition = f.terms.mk_eq(binder1, f.c2);
    let shared_array = f.terms.mk_ite(condition, f.a, f.b);
    let q1 = pointwise_from_index(
        &mut f.terms,
        "seq_capture_i1",
        binder1,
        f.c1,
        shared_array,
        f.b,
        false,
    );
    let q2 = pointwise_from_index(
        &mut f.terms,
        "seq_capture_i2",
        binder2,
        f.c2,
        shared_array,
        f.b,
        false,
    );
    let not_positive_len = f.terms.mk_not_raw(f.positive_len);
    let tail = f.terms.mk_or(vec![f.tail_equality, not_positive_len]);
    let positive = f.terms.mk_and(vec![f.equality, q1, tail]);
    let not_equality = f.terms.mk_not_raw(f.equality);
    let not_tail = f.terms.mk_not_raw(f.tail_equality);
    let tail_dual = f.terms.mk_and(vec![f.positive_len, not_tail]);
    let not_q2 = f.terms.mk_not_raw(q2);
    let negative = f.terms.mk_or(vec![not_equality, tail_dual, not_q2]);
    let roots = [f.lower, f.roots[1], f.roots[2], positive, negative];
    let forged = clause(&mut f.terms, &roots);
    assert!(validate(&f.terms, ProofId(0), &forged).is_err());
}
