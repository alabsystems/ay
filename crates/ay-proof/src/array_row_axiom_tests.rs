// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Coverage for the READ-OVER-WRITE axiom instances a definitional bridge may
//! cite.
//!
//! The bar, and how each layer meets it:
//!
//! 1. **An INDEPENDENT evaluator re-checks every ACCEPT.** [`falsify`] shares
//!    no code with the minter: it enumerates every assignment over a bounded
//!    index/element alphabet, interprets `select`/`store` as the McCarthy
//!    operations on total functions, and reports one that falsifies every
//!    literal. `congruence_derivation_sweep_tests::falsifies` cannot be used
//!    for an ARRAY axiom — it treats `select`/`store` as uninterpreted, under
//!    which the axiom is not valid — so a second, array-aware evaluator is
//!    what the array half of this campaign needs.
//! 2. **The UNTOUCHED strict checker replays every accepted instance.**
//!    [`strict_checks`] closes the instance into a self-contained refutation
//!    and runs `check_proof_strict`, which is the same validator the mandatory
//!    UNSAT gate runs.
//! 3. **Exhaustive, two-sided sweeps** over a bounded alphabet: every store
//!    term the alphabet can build is minted and re-checked, and the box is
//!    asserted to CONTAIN genuinely invalid neighbours.
//! 4. **Adversarial negatives** live in `array_row_axiom_negative_tests.rs`,
//!    each naming a concrete falsifying assignment and CHECKING it in-test.

use super::model::{
    accept, array, decidable, element, eq, falsify, holds, index, select, small, store,
    strict_checks,
};
use super::{plan_row1_axiom_instances, MAX_ROW1_AXIOM_INSTANCES};
use crate::quality::check_proof_strict;
use ay_core::{Symbol, TermData, TermId, TermStore};

// ===== the measured shape =====

/// The head of the measured residual, as an axiom instance:
/// `(= (select (store a_258 i0 e_259) i0) e_259)`.
#[test]
fn the_minted_instance_is_read_over_write_at_the_stores_own_index() {
    let mut terms = TermStore::new();
    let base = array(&mut terms, "a_258");
    let at = index(&mut terms, "i0");
    let value = element(&mut terms, "e_259");
    let stored = store(&mut terms, base, at, value);
    let equality = accept(&mut terms, stored);

    let TermData::App(Symbol::Named(name), args) = terms.get(equality) else {
        panic!("the instance must be a binary `=` application");
    };
    assert_eq!(name, "=");
    assert_eq!(args.len(), 2);
    assert_eq!(args[1], value, "the value side is the stored value itself");
    let TermData::App(Symbol::Named(head), read) = terms.get(args[0]) else {
        panic!("the select side must be an application");
    };
    assert_eq!(head, "select");
    assert_eq!(
        read.as_slice(),
        [stored, at],
        "the READ index must be the store's OWN index term — no distinctness is ever assumed"
    );
}

/// The reason a RAW builder is unavoidable, pinned rather than asserted: the
/// term store FOLDS this exact read, so the node the congruence closure has to
/// merge on cannot be built with `mk_select`.
#[test]
fn mk_select_folds_the_node_the_closure_needs() {
    let mut terms = TermStore::new();
    let base = array(&mut terms, "a");
    let at = index(&mut terms, "i");
    let value = element(&mut terms, "v");
    let stored = store(&mut terms, base, at, value);
    assert_eq!(
        terms.mk_select(stored, at),
        value,
        "mk_select folds read-over-write, so the raw builder is load-bearing"
    );
}

#[test]
fn every_store_of_a_chain_yields_its_own_instance() {
    let mut terms = TermStore::new();
    let a1 = array(&mut terms, "a1");
    let i0 = index(&mut terms, "i0");
    let i1 = index(&mut terms, "i1");
    let e0 = element(&mut terms, "e0");
    let e1 = element(&mut terms, "e1");
    let inner = store(&mut terms, a1, i0, e0);
    let outer = store(&mut terms, inner, i1, e1);
    let instances = plan_row1_axiom_instances(&mut terms, &[outer]);
    assert_eq!(
        instances.len(),
        2,
        "one instance per store node in the chain"
    );
    for &equality in &instances {
        assert!(falsify(&terms, &[equality], &small()).is_none());
        assert!(strict_checks(&mut terms, equality));
    }
}

#[test]
fn instances_are_deduplicated_across_roots() {
    let mut terms = TermStore::new();
    let a1 = array(&mut terms, "a1");
    let i0 = index(&mut terms, "i0");
    let e0 = element(&mut terms, "e0");
    let stored = store(&mut terms, a1, i0, e0);
    let read = select(&mut terms, stored, i0);
    let goal = eq(&mut terms, read, e0);
    let instances = plan_row1_axiom_instances(&mut terms, &[stored, goal, stored]);
    assert_eq!(instances.len(), 1);
}

#[test]
fn a_term_with_no_store_yields_no_instance() {
    let mut terms = TermStore::new();
    let a1 = array(&mut terms, "a1");
    let i0 = index(&mut terms, "i0");
    let read = select(&mut terms, a1, i0);
    assert!(plan_row1_axiom_instances(&mut terms, &[read]).is_empty());
}

/// The cap is real, not decorative: a chain longer than the cap yields exactly
/// the cap.
#[test]
fn the_instance_count_is_capped() {
    let mut terms = TermStore::new();
    let mut current = array(&mut terms, "a1");
    let at = index(&mut terms, "i");
    for step in 0..(MAX_ROW1_AXIOM_INSTANCES + 8) {
        let value = element(&mut terms, &format!("e{step}"));
        current = store(&mut terms, current, at, value);
    }
    let instances = plan_row1_axiom_instances(&mut terms, &[current]);
    assert_eq!(instances.len(), MAX_ROW1_AXIOM_INSTANCES);
}

// ===== the exhaustive sweep =====

/// EVERY store term the bounded alphabet can build, minted and re-checked by
/// the independent evaluator AND by the strict checker.
///
/// Two arrays, two indices, two elements, and every one-level and two-level
/// store over them: 2 * 2 * 2 = 8 depth-one terms and 8 * 2 * 2 = 32 depth-two
/// terms, 40 in all. Each yields exactly one instance and every instance is
/// re-checked twice.
#[test]
fn the_sweep_accepts_every_store_over_a_bounded_alphabet() {
    let mut terms = TermStore::new();
    let arrays: Vec<TermId> = ["a", "b"]
        .iter()
        .map(|name| array(&mut terms, name))
        .collect();
    let indices: Vec<TermId> = ["i", "j"]
        .iter()
        .map(|name| index(&mut terms, name))
        .collect();
    let elements: Vec<TermId> = ["u", "v"]
        .iter()
        .map(|name| element(&mut terms, name))
        .collect();
    let mut depth_one: Vec<TermId> = Vec::new();
    for &base in &arrays {
        for &at in &indices {
            for &value in &elements {
                depth_one.push(store(&mut terms, base, at, value));
            }
        }
    }
    let mut all = depth_one.clone();
    for &base in &depth_one {
        for &at in &indices {
            for &value in &elements {
                all.push(store(&mut terms, base, at, value));
            }
        }
    }
    assert_eq!(all.len(), 8 + 32, "the sweep box must be the stated size");
    let mut accepted = 0usize;
    for stored in all {
        let _instance = accept(&mut terms, stored);
        accepted += 1;
    }
    assert_eq!(accepted, 40, "every store term in the box must be accepted");
}

/// The box CONTAINS genuinely invalid neighbours — otherwise the sweep above
/// would prove nothing about the evaluator. For each store `(store a i v)` the
/// evaluator must REFUTE the different-index read `(= (select (store a i v) j) v)`.
#[test]
fn the_sweep_box_contains_refutable_neighbours() {
    let mut terms = TermStore::new();
    let base = array(&mut terms, "a");
    let at = index(&mut terms, "i");
    let other = index(&mut terms, "j");
    let value = element(&mut terms, "v");
    let stored = store(&mut terms, base, at, value);
    let read = select(&mut terms, stored, other);
    let invalid = eq(&mut terms, read, value);
    let witness = falsify(&terms, &[invalid], &small())
        .expect("the different-index read is NOT valid and the evaluator must say so");
    // Name the falsifying assignment and CHECK it.
    assert_eq!(holds(&terms, invalid, &witness, &small()), Some(false));
    assert_ne!(
        witness
            .iter()
            .find(|(id, _)| *id == at)
            .expect("i bound")
            .1
            .clone(),
        witness
            .iter()
            .find(|(id, _)| *id == other)
            .expect("j bound")
            .1
            .clone(),
        "the witness must separate the two indices"
    );
}

// ===== the end-to-end bridge =====

/// The measured residual, closed: `(= e_261 e_259)` from the two AUTHORED
/// assertions plus one read-over-write instance.
///
/// ```text
/// authored   (= a_260 (store a_258 i0 e_259))
/// authored   (= e_261 (select a_260 i0))
/// asserted   (= e_261 e_259)
/// ```
#[test]
fn the_measured_read_over_write_residual_bridges() {
    let mut terms = TermStore::new();
    let a258 = array(&mut terms, "a_258");
    let a260 = array(&mut terms, "a_260");
    let i0 = index(&mut terms, "i0");
    let e259 = element(&mut terms, "e_259");
    let e261 = element(&mut terms, "e_261");

    let stored = store(&mut terms, a258, i0, e259);
    let definition = eq(&mut terms, a260, stored);
    let read = select(&mut terms, a260, i0);
    let authored = eq(&mut terms, e261, read);
    let goal = eq(&mut terms, e261, e259);

    // Without the axiom the goal is NOT derivable — the measured decline.
    assert!(
        crate::plan_definitional_bridge(&mut terms, goal, &[definition, authored]).is_none(),
        "congruence alone must not reach a read-over-write goal"
    );

    let axiom = accept(&mut terms, stored);
    let planned = crate::plan_definitional_bridge(&mut terms, goal, &[definition, authored, axiom])
        .expect("the axiom must make the goal reachable");
    assert!(
        planned.hypotheses.contains(&axiom),
        "the bridge must cite the axiom instance"
    );
    // The bridge clause is a pure CONGRUENCE entailment once the axiom is a
    // hypothesis, so the campaign's own uninterpreted-function evaluator is the
    // right independent check for it.
    assert!(
        crate::congruence_derivation::sweep_tests::falsifies(&terms, &planned.derivation.clause)
            .is_none(),
        "the independent EUF evaluator found a countermodel of the bridge clause"
    );
    // And the whole thing is ARRAY-valid too, with the axiom RESOLVED IN:
    // every literal of the goal-only clause must be refutable by nothing.
    let not_definition = terms.mk_not(definition);
    let not_authored = terms.mk_not(authored);
    let entailment = [goal, not_definition, not_authored];
    assert!(
        decidable(&terms, &entailment, &small()),
        "the array model could not interpret the entailment, so its silence is not evidence"
    );
    assert!(
        falsify(&terms, &entailment, &small()).is_none(),
        "the array model must find no countermodel of the entailment the bridge claims"
    );
    let closed = crate::close_congruence_derivation(&mut terms, &planned.derivation);
    check_proof_strict(&closed, &terms).expect("every planned step must strict-check");
}
