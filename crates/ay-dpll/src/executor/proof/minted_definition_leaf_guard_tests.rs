// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! DIRECT unit pins on the MINTED-DEFINITION lane's alignment and its minting
//! guards.
//!
//! Split out of `minted_definition_leaf_negative_tests.rs` so each file stays
//! inside the repository's 500-line ceiling. The GUARD MUTATION LEDGER, which
//! names the test each mutation turns red, lives in that file.

use ay_core::{AletheRule, ProofStep, TermId};

use super::tests::{boolvar, ff, leaf_proof, rerun, shape, solve, PURIFY};
use crate::Executor;

// ===== DIRECT unit pins on the alignment and the minting guards =====
//
// Every guard below is backstopped by `commit_bridge_fragments`' whole-proof
// `check_proof` (which runs the checker's OWN `FreshDefRegistry`) or by Gate 2,
// so deleting one alone leaves the lane's OUTPUT unchanged and a
// derivation-count assertion cannot observe it. These tests therefore ask the
// guard directly, which is what makes each one mutation-checkable. The
// backstops are still there and are pinned separately by
// `gate_two_reverts_a_splice_the_checkers_registry_declines`.

/// The vetting inputs for one fixture, built exactly as the lane builds them.
fn vetting(
    exec: &mut Executor,
    proof: &ay_core::Proof,
) -> (
    ay_core::kani_compat::DetHashSet<String>,
    ay_core::kani_compat::DetHashMap<String, TermId>,
) {
    let scope = exec.complete_problem_assertions_for_strict_proof();
    (
        exec.minted_constrained_names(proof, &scope),
        exec.existing_fresh_definitions(proof),
    )
}

#[test]
fn the_alignment_stops_at_a_not_and_records_the_whole_node() {
    let mut exec = solve(PURIFY);
    let pp = boolvar(&mut exec, "pp");
    let g = boolvar(&mut exec, "g");
    let h = boolvar(&mut exec, "h");
    let k = boolvar(&mut exec, "k");
    let conjunction = exec.ctx.terms.mk_and(vec![g, h]);
    let not_conjunction = exec.ctx.terms.mk_not_raw(conjunction);
    let not_pp = exec.ctx.terms.mk_not_raw(pp);
    let root = ff(&mut exec, not_conjunction, k);
    let leaf = ff(&mut exec, not_pp, k);
    let mut pairs: Vec<(TermId, TermId)> = Vec::new();
    let mut budget = 4096usize;
    assert!(super::align(
        &exec.ctx.terms,
        leaf,
        root,
        &mut pairs,
        &mut budget
    ));
    assert_eq!(
        pairs,
        vec![(not_pp, not_conjunction)],
        "the alignment must stop AT the `not`, not descend through it"
    );
    // TWO-SIDED: above the `not`, the same substitution aligns to the atom.
    let above_root = ff(&mut exec, conjunction, k);
    let above_leaf = ff(&mut exec, pp, k);
    let mut pairs: Vec<(TermId, TermId)> = Vec::new();
    let mut budget = 4096usize;
    assert!(super::align(
        &exec.ctx.terms,
        above_leaf,
        above_root,
        &mut pairs,
        &mut budget
    ));
    assert_eq!(pairs, vec![(pp, conjunction)]);
}

#[test]
fn the_minter_refuses_a_definiendum_the_problem_constrains() {
    let mut exec = solve(PURIFY);
    let g = boolvar(&mut exec, "g");
    let h = boolvar(&mut exec, "h");
    let k = boolvar(&mut exec, "k");
    let conjunction = exec.ctx.terms.mk_and(vec![g, h]);
    let root = ff(&mut exec, conjunction, k);
    let pp = boolvar(&mut exec, "pp");
    let leaf = ff(&mut exec, pp, k);
    let proof = leaf_proof(&mut exec, leaf);
    let (constrained, existing) = vetting(&mut exec, &proof);
    // FRESH holds for `pp`, so the minter accepts.
    assert!(exec
        .mint_definitions_for(leaf, root, &constrained, &existing)
        .is_some());
    // `k` is AUTHORED and does NOT occur in the definiens, so FRESH is the
    // ONLY guard that can refuse it — which is what makes FRESH observable.
    // (`g` would also be refused, but by INDEPENDENT, since `g` occurs inside
    // `(and g h)`; a fixture using `g` cannot distinguish the two guards.)
    let leaf_over_k = ff(&mut exec, k, k);
    assert!(
        !constrained.contains("pp"),
        "the fixture's fresh symbol must be fresh"
    );
    assert!(
        constrained.contains("k"),
        "the fixture's authored symbol must be constrained"
    );
    assert!(
        exec.mint_definitions_for(leaf_over_k, root, &constrained, &existing)
            .is_none(),
        "an authored symbol is not a fresh definiendum"
    );
}

#[test]
fn the_minter_refuses_a_second_definiens_for_one_symbol() {
    let mut exec = solve(PURIFY);
    let g = boolvar(&mut exec, "g");
    let h = boolvar(&mut exec, "h");
    let k = boolvar(&mut exec, "k");
    let pp = boolvar(&mut exec, "pp");
    let conjunction = exec.ctx.terms.mk_and(vec![g, h]);
    let root = ff(&mut exec, conjunction, k);
    let leaf = ff(&mut exec, pp, k);
    let mut proof = leaf_proof(&mut exec, leaf);
    let (constrained, existing) = vetting(&mut exec, &proof);
    assert!(exec
        .mint_definitions_for(leaf, root, &constrained, &existing)
        .is_some());
    // Now the proof carries a DIFFERENT definiens for `pp`.
    let other = exec.ctx.terms.mk_or(vec![g, h]);
    let other_definition = exec.ctx.terms.mk_eq(pp, other);
    proof.steps.push(ProofStep::Step {
        rule: AletheRule::FreshDefEq,
        clause: vec![other_definition],
        premises: Vec::new(),
        args: vec![pp],
    });
    let (constrained, existing) = vetting(&mut exec, &proof);
    assert_eq!(existing.len(), 1, "the existing binding must be visible");
    assert!(
        exec.mint_definitions_for(leaf, root, &constrained, &existing)
            .is_none(),
        "a second definiens for one symbol is refused, never competed with"
    );
}

#[test]
fn the_minter_refuses_a_definiendum_that_occurs_in_a_definiens() {
    let mut exec = solve(PURIFY);
    let g = boolvar(&mut exec, "g");
    let k = boolvar(&mut exec, "k");
    let pp = boolvar(&mut exec, "pp");
    // `pp := (and g pp)` — the definiendum occurs INSIDE its own definiens,
    // which is exactly what INDEPENDENT forbids. It is the ONLY guard that can
    // refuse this: `pp` is fresh, the sorts match, and there is no competing
    // binding.
    let inner = exec.ctx.terms.mk_and(vec![g, pp]);
    let root = ff(&mut exec, inner, k);
    let leaf = ff(&mut exec, pp, k);
    let proof = leaf_proof(&mut exec, leaf);
    let (constrained, existing) = vetting(&mut exec, &proof);
    assert!(!constrained.contains("pp"), "`pp` is fresh");
    assert!(existing.is_empty(), "no competing binding");
    assert_eq!(
        *exec.ctx.terms.sort(pp),
        *exec.ctx.terms.sort(inner),
        "the sorts match, so SORT cannot be what refuses"
    );
    assert!(
        exec.mint_definitions_for(leaf, root, &constrained, &existing)
            .is_none(),
        "a definiendum may never occur inside its own definiens"
    );
    // TWO-SIDED: with the definiens no longer mentioning `pp`, the SAME
    // definiendum IS minted.
    let h = boolvar(&mut exec, "h");
    let clean = exec.ctx.terms.mk_and(vec![g, h]);
    let clean_root = ff(&mut exec, clean, k);
    assert!(
        exec.mint_definitions_for(leaf, clean_root, &constrained, &existing)
            .is_some(),
        "the refusal is about the OCCURRENCE, not about the shape"
    );
    // And `pp := (not pp)` — the unsatisfiable self-definition — is refused by
    // the ALIGNMENT before INDEPENDENT is even consulted, because a `Not` is
    // not an `App` descent.
    let not_pp = exec.ctx.terms.mk_not_raw(pp);
    let self_root = ff(&mut exec, not_pp, k);
    assert!(
        exec.mint_definitions_for(leaf, self_root, &constrained, &existing)
            .is_none(),
        "`pp := (not pp)` is never written"
    );
}

#[test]
fn the_minter_refuses_a_sort_mismatch() {
    let mut exec = solve(
        r#"
        (set-logic QF_UFLIA)
        (declare-fun g () Bool)
        (declare-fun h () Bool)
        (declare-fun k () Bool)
        (declare-fun zz () Bool)
        (declare-fun ff (Bool Bool) Bool)
        (declare-fun gg (Int Bool) Bool)
        (assert (gg 3 k))
        (assert zz)
        (assert (not zz))
        (check-sat)
    "#,
    );
    let k = boolvar(&mut exec, "k");
    let pp = boolvar(&mut exec, "pp");
    let three = exec.ctx.terms.mk_int(num_bigint::BigInt::from(3));
    let root = exec.ctx.terms.mk_app(
        ay_core::Symbol::named("gg"),
        vec![three, k],
        ay_core::Sort::Bool,
    );
    // A Bool definiendum against an Int definiens: the assignment
    // `pp := 3` does not exist, so SORT refuses.
    let leaf = exec.ctx.terms.mk_app(
        ay_core::Symbol::named("gg"),
        vec![pp, k],
        ay_core::Sort::Bool,
    );
    let proof = leaf_proof(&mut exec, leaf);
    let (constrained, existing) = vetting(&mut exec, &proof);
    assert!(
        exec.mint_definitions_for(leaf, root, &constrained, &existing)
            .is_none(),
        "a Bool definiendum may not be defined by an Int term"
    );
}

#[test]
fn a_leaf_whose_differing_position_is_a_compound_term_is_left_alone() {
    let mut exec = solve(PURIFY);
    let g = boolvar(&mut exec, "g");
    let k = boolvar(&mut exec, "k");
    // `(ff (or g h) k)` differs from the root at a position that is NOT an
    // atomic variable, so there is no definiendum to define.
    let h = boolvar(&mut exec, "h");
    let compound = exec.ctx.terms.mk_or(vec![g, h]);
    let atom = ff(&mut exec, compound, k);
    let mut proof = leaf_proof(&mut exec, atom);
    let before = shape(&proof);
    assert_eq!(rerun(&mut exec, &mut proof), 0);
    assert_eq!(shape(&proof), before);
}
