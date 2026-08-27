// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Guard tests for the packed-EUF `reordering` lane — section 3 of
//! `packed_euf_reordering_tests.rs`, split out only to keep each file inside
//! the repository's 500-line ceiling. The `GUARD_MUTATION_LEDGER` these pin is
//! in that file's module documentation.

use super::super::*;
use super::{chain, is_reordering_of, or_step, or_term, trust_leaf};

use ay_core::FarkasAnnotation;

// ==========================================================================
// 3. Guards (mutation ledger above)
// ==========================================================================

/// A `trust` step WITH premises is a failed derivation, not a leaf claiming
/// its clause is valid on its own; rewriting it would drop the premises its
/// consumer still references.
#[test]
fn a_trust_step_with_premises_is_left_alone() {
    let mut executor = Executor::new();
    let link = chain(&mut executor, "withprem");
    let flat = vec![link.not_ab, link.eq_cb, link.not_ca];
    let packed = or_term(&mut executor, flat.clone());
    let mut proof = Proof::new();
    proof.add_step(ProofStep::Assume(link.eq_ab));
    proof.add_step(ProofStep::Step {
        rule: AletheRule::Trust,
        clause: vec![packed],
        premises: vec![ProofId(0)],
        args: Vec::new(),
    });
    proof.add_step(or_step(flat, 1));
    let before = format!("{:?}", proof.steps);
    assert_eq!(
        executor.derive_packed_euf_transitive_reorderings(&mut proof),
        0
    );
    assert_eq!(format!("{:?}", proof.steps), before);
}

/// Same for `:args`.
#[test]
fn a_trust_step_with_args_is_left_alone() {
    let mut executor = Executor::new();
    let link = chain(&mut executor, "withargs");
    let flat = vec![link.not_ab, link.eq_cb, link.not_ca];
    let packed = or_term(&mut executor, flat.clone());
    let mut proof = Proof::new();
    proof.add_step(ProofStep::Step {
        rule: AletheRule::Trust,
        clause: vec![packed],
        premises: Vec::new(),
        args: vec![link.eq_ab],
    });
    proof.add_step(or_step(flat, 0));
    let before = format!("{:?}", proof.steps);
    assert_eq!(
        executor.derive_packed_euf_transitive_reorderings(&mut proof),
        0
    );
    assert_eq!(format!("{:?}", proof.steps), before);
}

/// The consumer must be the `or` step. Any other rule consumes the PACKED unit
/// for its own reasons, and replacing the leaf's clause would silently change
/// what that rule was applied to.
#[test]
fn a_leaf_whose_consumer_is_not_an_or_step_is_left_alone() {
    let mut executor = Executor::new();
    let link = chain(&mut executor, "notor");
    let flat = vec![link.not_ab, link.eq_cb, link.not_ca];
    let packed = or_term(&mut executor, flat.clone());
    let mut proof = Proof::new();
    proof.add_step(trust_leaf(vec![packed]));
    proof.add_step(ProofStep::Step {
        rule: AletheRule::Contraction,
        clause: flat,
        premises: vec![ProofId(0)],
        args: Vec::new(),
    });
    let before = format!("{:?}", proof.steps);
    assert_eq!(
        executor.derive_packed_euf_transitive_reorderings(&mut proof),
        0
    );
    assert_eq!(format!("{:?}", proof.steps), before);
}

/// The `or` consumer's clause must be EXACTLY the flattened children. A
/// consumer that concluded something else was not the flattening of this leaf,
/// and re-labelling it `reordering` would claim a permutation that is not one.
#[test]
fn a_consumer_whose_clause_is_not_the_flattened_children_is_left_alone() {
    let mut executor = Executor::new();
    let link = chain(&mut executor, "mismatch");
    let flat = vec![link.not_ab, link.eq_cb, link.not_ca];
    let packed = or_term(&mut executor, flat.clone());
    let mut proof = Proof::new();
    proof.add_step(trust_leaf(vec![packed]));
    // one literal dropped: this is a strengthening, not a flattening
    proof.add_step(or_step(vec![link.not_ab, link.eq_cb], 0));
    let before = format!("{:?}", proof.steps);
    assert_eq!(
        executor.derive_packed_euf_transitive_reorderings(&mut proof),
        0
    );
    assert_eq!(format!("{:?}", proof.steps), before);
}

/// A second consumer still needs the PACKED unit clause. Rewriting the leaf
/// would leave that consumer citing a clause that no longer exists.
#[test]
fn a_leaf_with_a_second_consumer_is_left_alone() {
    let mut executor = Executor::new();
    let link = chain(&mut executor, "twocons");
    let flat = vec![link.not_ab, link.eq_cb, link.not_ca];
    let packed = or_term(&mut executor, flat.clone());
    let mut proof = Proof::new();
    proof.add_step(trust_leaf(vec![packed]));
    proof.add_step(or_step(flat.clone(), 0));
    proof.add_step(ProofStep::Step {
        rule: AletheRule::Contraction,
        clause: vec![packed],
        premises: vec![ProofId(0)],
        args: Vec::new(),
    });
    let before = format!("{:?}", proof.steps);
    assert_eq!(
        executor.derive_packed_euf_transitive_reorderings(&mut proof),
        0
    );
    assert_eq!(format!("{:?}", proof.steps), before);
}

/// A leaf with NO consumer is not this shape either: the `or` step is what
/// makes the flattened clause available, and without it nothing licenses the
/// permutation being introduced.
#[test]
fn a_leaf_with_no_consumer_is_left_alone() {
    let mut executor = Executor::new();
    let link = chain(&mut executor, "nocons");
    let flat = vec![link.not_ab, link.eq_cb, link.not_ca];
    let packed = or_term(&mut executor, flat);
    let mut proof = Proof::new();
    proof.add_step(trust_leaf(vec![packed]));
    let before = format!("{:?}", proof.steps);
    assert_eq!(
        executor.derive_packed_euf_transitive_reorderings(&mut proof),
        0
    );
    assert_eq!(format!("{:?}", proof.steps), before);
}

/// The consumer must come LATER than the leaf: the strict checker validates in
/// order and reads a premise from the clauses already derived.
#[test]
fn a_consumer_that_precedes_its_leaf_is_left_alone() {
    let mut executor = Executor::new();
    let link = chain(&mut executor, "backref");
    let flat = vec![link.not_ab, link.eq_cb, link.not_ca];
    let packed = or_term(&mut executor, flat.clone());
    let mut proof = Proof::new();
    proof.add_step(or_step(flat, 1));
    proof.add_step(trust_leaf(vec![packed]));
    let before = format!("{:?}", proof.steps);
    assert_eq!(
        executor.derive_packed_euf_transitive_reorderings(&mut proof),
        0
    );
    assert_eq!(format!("{:?}", proof.steps), before);
}

/// A surface override that re-spells a hypothesis as something other than
/// `(not ..)`/`(distinct ..)` makes the promoted lemma UNPRINTABLE, and
/// `demote_unrenderable_eq_transitive_lemmas` would turn it into a `hole` two
/// lanes later. That trades a rescuable `trust` rejection for a hard one, so
/// the lane declines and the pair stays byte-identical.
#[test]
fn a_leaf_whose_hypothesis_prints_unrenderably_is_left_alone() {
    let mut executor = Executor::new();
    let link = chain(&mut executor, "surface");
    let flat = vec![link.not_ab, link.eq_cb, link.not_ca];
    let packed = or_term(&mut executor, flat.clone());
    let mut overrides = ay_core::kani_compat::DetHashMap::default();
    overrides.insert(link.not_ab, "(= (= a b) false)".to_string());
    executor.last_proof_term_overrides = Some(overrides);
    let mut proof = Proof::new();
    proof.add_step(trust_leaf(vec![packed]));
    proof.add_step(or_step(flat, 0));
    let before = format!("{:?}", proof.steps);
    assert_eq!(
        executor.derive_packed_euf_transitive_reorderings(&mut proof),
        0
    );
    assert_eq!(format!("{:?}", proof.steps), before);
}

/// The same clause with a `(distinct ..)` override IS renderable — the
/// printer's resugaring bridge handles it — so the lane proceeds. Pins that
/// the guard above is the demotion's exact predicate and not a blanket refusal
/// whenever any override exists.
#[test]
fn a_distinct_override_is_still_renderable_and_the_lane_proceeds() {
    let mut executor = Executor::new();
    let link = chain(&mut executor, "distinct");
    let flat = vec![link.not_ab, link.eq_cb, link.not_ca];
    let packed = or_term(&mut executor, flat.clone());
    let mut overrides = ay_core::kani_compat::DetHashMap::default();
    overrides.insert(link.not_ab, "(distinct a b)".to_string());
    executor.last_proof_term_overrides = Some(overrides);
    let mut proof = Proof::new();
    proof.add_step(trust_leaf(vec![packed]));
    proof.add_step(or_step(flat.clone(), 0));
    assert_eq!(
        executor.derive_packed_euf_transitive_reorderings(&mut proof),
        1
    );
    assert!(is_reordering_of(&proof.steps[1], &flat, 0));
}

/// A leaf the EXISTING intrinsic sweep already accepts AS RECORDED (conclusion
/// already last) is not this lane's business: that pass runs earlier and owns
/// it, so this lane declines and the pair stays byte-identical. This is what
/// makes the lane strictly ADDITIVE — it can only ever see leaves the earlier
/// sweep refused.
#[test]
fn a_leaf_already_in_validator_order_is_left_to_the_intrinsic_sweep() {
    let mut executor = Executor::new();
    let link = chain(&mut executor, "already");
    let flat = vec![link.not_ab, link.not_ca, link.eq_cb];
    let packed = or_term(&mut executor, flat.clone());
    assert!(
        ay_proof::recognize_euf_transitive(&executor.ctx.terms, &[packed]),
        "precondition: the recorded order is already accepted"
    );
    let mut proof = Proof::new();
    proof.add_step(trust_leaf(vec![packed]));
    proof.add_step(or_step(flat, 0));
    let before = format!("{:?}", proof.steps);
    assert_eq!(
        executor.derive_packed_euf_transitive_reorderings(&mut proof),
        0
    );
    assert_eq!(format!("{:?}", proof.steps), before);
    // ... and the sweep that DOES own it still promotes it in place.
    assert_eq!(executor.promote_intrinsic_tautology_leaves(&mut proof), 1);
}

/// A `TheoryLemma` carrying an arithmetic payload is not a `trust` STEP and is
/// outside this lane entirely — the payload stays with its own producer.
#[test]
fn a_theory_lemma_with_a_payload_is_not_touched() {
    let mut executor = Executor::new();
    let link = chain(&mut executor, "payload");
    let flat = vec![link.not_ab, link.eq_cb, link.not_ca];
    let packed = or_term(&mut executor, flat.clone());
    let mut proof = Proof::new();
    proof.add_step(ProofStep::TheoryLemma {
        theory: "LIA".to_string(),
        clause: vec![packed],
        farkas: Some(FarkasAnnotation {
            coefficients: vec![],
        }),
        kind: TheoryLemmaKind::Generic,
        lia: None,
    });
    proof.add_step(or_step(flat, 0));
    let before = format!("{:?}", proof.steps);
    assert_eq!(
        executor.derive_packed_euf_transitive_reorderings(&mut proof),
        0
    );
    assert_eq!(format!("{:?}", proof.steps), before);
}
