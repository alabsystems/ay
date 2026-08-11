// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Adversarial tests for provenance-authenticated arithmetic ITE planning.

use ay_core::{Sort, TermStore};
use num_bigint::BigInt;

use super::proof_trust_surgery_provenance::branch_resolution_shape_unambiguous;
use super::Executor;

#[test]
fn ite_branch_resolution_rejects_guard_and_literal_collisions() {
    let mut terms = TermStore::new();
    let goal = terms.mk_var("goal", Sort::Bool);
    let cond = terms.mk_var("cond", Sort::Bool);
    let source = terms.mk_var("source", Sort::Bool);
    let lifted = terms.mk_var("lifted", Sort::Bool);
    let not_cond = terms.mk_not_raw(cond);
    let not_source = terms.mk_not_raw(source);

    assert!(branch_resolution_shape_unambiguous(
        &mut terms,
        goal,
        not_cond,
        source,
        lifted,
        &[not_source, lifted],
    ));

    // A retained support equal to either polarity of the guard would be
    // erased early by set-resolution and invalidate ordered bookkeeping.
    assert!(!branch_resolution_shape_unambiguous(
        &mut terms,
        goal,
        not_cond,
        source,
        lifted,
        &[not_source, not_cond, lifted],
    ));
    assert!(!branch_resolution_shape_unambiguous(
        &mut terms,
        goal,
        not_cond,
        source,
        lifted,
        &[not_source, cond, lifted],
    ));

    // Duplicate and complementary signed literals are equally ambiguous.
    assert!(!branch_resolution_shape_unambiguous(
        &mut terms,
        goal,
        not_cond,
        source,
        lifted,
        &[not_source, not_source, lifted],
    ));
    assert!(!branch_resolution_shape_unambiguous(
        &mut terms,
        goal,
        not_cond,
        source,
        lifted,
        &[not_source, source, lifted],
    ));

    // Leading-not parity, rather than one syntactic Not, defines a resolution
    // atom. With `cond = (not p)`, the then guard is `(not (not p))` and both
    // polarities of a `p` support still collide with that guard.
    let p = terms.mk_var("p", Sort::Bool);
    let negated_cond = terms.mk_not_raw(p);
    let double_negated_cond = terms.mk_not_raw(negated_cond);
    assert!(!branch_resolution_shape_unambiguous(
        &mut terms,
        goal,
        double_negated_cond,
        source,
        lifted,
        &[not_source, p, lifted],
    ));
    assert!(!branch_resolution_shape_unambiguous(
        &mut terms,
        goal,
        double_negated_cond,
        source,
        lifted,
        &[not_source, negated_cond, lifted],
    ));
}

#[test]
fn ite_farkas_plan_prunes_irrelevant_bool_support() {
    let mut executor = Executor::new();
    let x = executor.ctx.terms.mk_var("x", Sort::Int);
    let irrelevant = executor.ctx.terms.mk_var("irrelevant", Sort::Bool);
    let zero = executor.ctx.terms.mk_int(BigInt::from(0));
    let one = executor.ctx.terms.mk_int(BigInt::from(1));
    let source = executor.ctx.terms.mk_le(x, zero);
    let conclusion = executor.ctx.terms.mk_le(x, one);

    let lemma = executor
        .plan_provenance_farkas_implication(source, &[irrelevant], conclusion)
        .expect("linear implication should ignore the Bool support");

    assert!(lemma.supports.is_empty());
    assert_eq!(lemma.clause.len(), 2);
    assert_eq!(lemma.farkas.coefficients.len(), 2);
    assert!(lemma
        .farkas
        .coefficients
        .iter()
        .all(|coefficient| *coefficient != 0.into()));
}
