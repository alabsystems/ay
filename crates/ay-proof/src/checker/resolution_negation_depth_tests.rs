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
        &mut |_, _| true,
    )
    .expect("the exact explicit-pivot Carcara control must pass");
    validate_resolution_rule(
        &terms,
        ProofId(2),
        &AletheRule::Resolution,
        &[not_not_b],
        &premises,
        &[a, yes],
        &mut |_, _| true,
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
            &mut |_, _| true,
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
            &mut |_, _| true,
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
        &mut |_, _| true,
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
        &mut |_, _| true,
    )
    .expect("the exact chain resolvent must pass");
    validate_chain_resolution_rule(
        &terms,
        ProofId(3),
        &AletheRule::ThResolution,
        &[not_not_b],
        &premises,
        &mut |_, _| true,
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

/// The metered arg-free path must return the SAME verdict as the reference
/// `is_valid_binary_resolution(.., None)` on every shape — clean, parity,
/// pivot-in-both-clauses, empty resolvent, two complementary pairs, and
/// no-pivot — because the fast path only short-circuits through the same
/// `resolves_to` predicate and otherwise falls back to the identical search.
#[test]
fn metered_argfree_matches_the_reference_verdict_on_every_shape() {
    use crate::checker::resolution::argfree_binary_resolution_metered;
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let c = terms.mk_var("c", Sort::Bool);
    let na = terms.mk_not_raw(a);
    let nb = terms.mk_not_raw(b);
    let nc = terms.mk_not_raw(c);
    let nna = terms.mk_not_raw(na);
    let nnb = terms.mk_not_raw(nb);

    let cases: Vec<(
        Vec<ay_core::TermId>,
        Vec<ay_core::TermId>,
        Vec<ay_core::TermId>,
    )> = vec![
        (vec![a, b], vec![na], vec![b]),                       // clean valid
        (vec![a, b], vec![na], vec![a]),                       // clean invalid conclusion
        (vec![a, b], vec![na], vec![nnb]),                     // parity-equivalent conclusion
        (vec![a, b], vec![na, b], vec![b]),                    // pivot's mate present in both
        (vec![a, b], vec![c], vec![a, b, c]),                  // no complementary pair -> false
        (vec![a, b], vec![na, nb], vec![b, nb]),               // resolve on a
        (vec![a, b], vec![na, nb], vec![a, na]), // two complementary pairs, resolve on b
        (vec![a], vec![na], vec![]),             // empty resolvent
        (vec![nna, b], vec![na], vec![b]),       // deep-not pivot
        (vec![a, b, c], vec![na, nb, nc], vec![b, nb, c, nc]), // resolve on a
    ];

    for (c1, c2, concl) in cases {
        let reference = is_valid_binary_resolution(&terms, &c1, &c2, &concl, None);
        let metered = argfree_binary_resolution_metered(&terms, &c1, &c2, &concl, &mut |_, _| true)
            .expect("permissive meter never refuses");
        assert_eq!(
            metered, reference,
            "metered/reference disagree on c1={c1:?} c2={c2:?} concl={concl:?}"
        );
    }
}

/// The metered fallback fails closed: a meter that refuses after a fixed number
/// of pivot trials must return `ResourceLimit`, never silently accept or run
/// unbounded — this is what lets the caller drop the `input*total` precharge.
#[test]
fn metered_argfree_fails_closed_when_the_meter_refuses() {
    use crate::checker::resolution::argfree_binary_resolution_metered;
    use crate::ProofCheckError;
    let mut terms = TermStore::new();
    // A clause pair with MANY complementary pairs and a non-clean-shaped
    // conclusion so the fast path finds no accepting candidate and the metered
    // fallback engages.
    let atoms: Vec<ay_core::TermId> = (0..64)
        .map(|i| terms.mk_var(format!("m{i}"), Sort::Bool))
        .collect();
    let negs: Vec<ay_core::TermId> = atoms.iter().map(|&x| terms.mk_not_raw(x)).collect();
    let c1 = atoms.clone();
    let c2 = negs.clone();
    // Conclusion equal to c1 (no valid single-pivot resolvent yields it), so the
    // search exhausts.
    let concl = atoms.clone();

    let mut budget = 3usize;
    let result = argfree_binary_resolution_metered(&terms, &c1, &c2, &concl, &mut |_, _| {
        if budget == 0 {
            return false;
        }
        budget -= 1;
        true
    });
    assert_eq!(
        result,
        Err(ProofCheckError::ResourceLimit),
        "a refusing meter must make the fallback fail closed"
    );
}
