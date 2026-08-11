// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Leading-`not` syntax at the Alethe resolution boundary.
//!
//! These cases mirror pinned Carcara 1.1.0 (`fecb422`) controls with explicit
//! `(pivot, polarity)` arguments: the exact resolvent is accepted, while a
//! parity-equivalent replacement and a triple-`not` pivot are rejected. They
//! also lock the distinct argument-free behavior: Carcara falls back to RUP
//! there and accepts parity-equivalent literals.

use crate::checker::resolution::{
    is_valid_binary_resolution, is_valid_rup_step, validate_chain_resolution_rule,
    validate_resolution_rule,
};
use ay_core::{AletheRule, ProofId, Sort, TermStore};

#[test]
fn only_directed_resolution_requires_the_exact_untouched_literal_depth() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let not_a = terms.mk_not_raw(a);
    let not_b = terms.mk_not_raw(b);
    let not_not_b = terms.mk_not_raw(not_b);
    let yes = terms.mk_bool(true);
    let left = [a, b];
    let right = [not_a];

    assert!(is_valid_binary_resolution(
        &terms,
        &left,
        &right,
        &[b],
        None,
    ));
    assert!(is_valid_binary_resolution(
        &terms,
        &left,
        &right,
        &[not_not_b],
        None,
    ));
    assert!(is_valid_binary_resolution(
        &terms,
        &left,
        &right,
        &[not_not_b],
        Some(a),
    ));

    let premises: [&[ay_core::TermId]; 2] = [&left, &right];
    validate_resolution_rule(
        &terms,
        ProofId(2),
        &AletheRule::Resolution,
        &[b],
        &premises,
        &[a, yes],
    )
    .expect("the exact explicit-pivot Carcara control must pass");
    validate_resolution_rule(
        &terms,
        ProofId(2),
        &AletheRule::Resolution,
        &[not_not_b],
        &premises,
        &[a, yes],
    )
    .expect_err("directed resolution must not rewrite an untouched b to (not (not b))");
}

#[test]
fn directed_resolution_rejects_a_triple_not_for_an_atom_pivot() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let not_a = terms.mk_not_raw(a);
    let not_not_a = terms.mk_not_raw(not_a);
    let not_not_not_a = terms.mk_not_raw(not_not_a);
    let yes = terms.mk_bool(true);
    let no = terms.mk_bool(false);
    let left = [not_not_not_a];
    let right = [a];
    let premises: [&[ay_core::TermId]; 2] = [&left, &right];

    for polarity in [yes, no] {
        validate_resolution_rule(
            &terms,
            ProofId(2),
            &AletheRule::Resolution,
            &[],
            &premises,
            &[a, polarity],
        )
        .expect_err("a triple-not term is neither exact polarity of the declared atom pivot");
    }
}

#[test]
fn only_directed_resolution_rejects_duplicate_literal_count_skew() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let not_a = terms.mk_not_raw(a);
    let yes = terms.mk_bool(true);
    let left = [a, b];
    let duplicate_pivot_right = [not_a, not_a];
    let duplicate_residual_right = [not_a, b];

    for right in [&duplicate_pivot_right[..], &duplicate_residual_right[..]] {
        let premises: [&[ay_core::TermId]; 2] = [&left, right];
        validate_resolution_rule(
            &terms,
            ProofId(2),
            &AletheRule::Resolution,
            &[b],
            &premises,
            &[a, yes],
        )
        .expect_err("directed resolution must not collapse a duplicate pivot or residual literal");
    }

    let premises: [&[ay_core::TermId]; 2] = [&left, &duplicate_pivot_right];
    validate_resolution_rule(
        &terms,
        ProofId(2),
        &AletheRule::Resolution,
        &[b],
        &premises,
        &[],
    )
    .expect("argument-free resolution deliberately retains its parity/set fallback");
}

#[test]
fn argument_free_chain_retains_leading_not_parity() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let c = terms.mk_var("c", Sort::Bool);
    let not_a = terms.mk_not_raw(a);
    let not_b = terms.mk_not_raw(b);
    let not_not_b = terms.mk_not_raw(not_b);
    let not_c = terms.mk_not_raw(c);
    let first = [a, b];
    let second = [not_a, c];
    let third = [not_c];
    let premises: [&[ay_core::TermId]; 3] = [&first, &second, &third];

    validate_chain_resolution_rule(
        &terms,
        ProofId(3),
        &AletheRule::ThResolution,
        &[b],
        &premises,
    )
    .expect("the exact chain resolvent must pass");
    validate_chain_resolution_rule(
        &terms,
        ProofId(3),
        &AletheRule::ThResolution,
        &[not_not_b],
        &premises,
    )
    .expect("argument-free chain resolution retains the established parity fallback");
}

#[test]
fn rup_deliberately_keeps_leading_not_parity_semantics() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let not_a = terms.mk_not_raw(a);
    let not_not_a = terms.mk_not_raw(not_a);
    let prior = vec![Some(vec![a])];

    assert!(
        is_valid_rup_step(&terms, &[not_not_a], &prior),
        "RUP is semantic propagation, so even leading-not parity remains intentional"
    );
}
