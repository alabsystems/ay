// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::mem::size_of;

use ay_core::{ProofStep, Sort, TermId};

use crate::incremental_state::IncrementalSubsystem;

use super::checkpoint_budget::CheckpointCloneError;
use super::{ProofId, ProofTracker};

#[path = "checkpoint_payload_tests.rs"]
mod payload_tests;

fn assert_internal_id_invariants(tracker: &ProofTracker) {
    let len = u32::try_from(tracker.proof.steps.len()).expect("test proof fits u32");
    assert!(tracker.assumption_map.values().all(|id| id.0 < len));
    assert!(tracker.lemma_map.values().all(|id| id.0 < len));
    assert!(tracker.proof.named_steps.values().all(|id| id.0 < len));
}

fn add_outer_entries(tracker: &mut ProofTracker) -> (ProofId, ProofId) {
    let assumption = tracker
        .add_assumption(TermId(1), Some("h_outer".to_string()))
        .expect("tracking is enabled");
    let lemma = tracker
        .add_explicit_trust_lemma(vec![TermId(10)])
        .expect("tracking is enabled");
    (assumption, lemma)
}

fn assert_outer_entries_dedup(
    tracker: &mut ProofTracker,
    expected_assumption: ProofId,
    expected_lemma: ProofId,
) {
    assert_eq!(
        tracker
            .add_assumption(TermId(1), Some("h_outer_again".to_string()))
            .expect("tracking is enabled"),
        expected_assumption
    );
    assert_eq!(
        tracker
            .add_explicit_trust_lemma(vec![TermId(10)])
            .expect("tracking is enabled"),
        expected_lemma
    );
}

#[test]
fn dynamic_checkpoint_charge_has_exact_fail_closed_boundary() {
    let mut tracker = ProofTracker::new();
    tracker.enable();
    tracker
        .add_assumption(TermId(7), Some("dynamic_checkpoint_name".to_string()))
        .expect("tracking is enabled");
    tracker
        .add_explicit_trust_lemma(vec![TermId(8), TermId(9), TermId(10)])
        .expect("tracking is enabled");
    let charge = tracker
        .checkpoint_clone_charge_for_test()
        .expect("small dynamic ledger footprint is representable");

    assert!(matches!(
        tracker.rollback_checkpoint_bounded(charge - 1),
        Err(CheckpointCloneError::LimitExceeded)
    ));
    let (_, actual) = tracker
        .rollback_checkpoint_bounded(charge)
        .expect("the exact footprint must be admitted");
    assert_eq!(actual, charge);
}

#[test]
fn overdeep_sort_fails_closed_but_tiny_limit_stops_before_payload_walk() {
    let mut sort = Sort::Int;
    for _ in 0..=257 {
        sort = Sort::seq(sort);
    }
    let mut tracker = ProofTracker::new();
    tracker.proof.steps.push(ProofStep::Anchor {
        end_step: ProofId(0),
        variables: vec![("deep".to_string(), sort)],
    });

    // Admit the checkpoint header itself, but stop one byte before accounting
    // the first top-level `ProofStep` slot. The deep sort must not be visited.
    let before_step_payload =
        size_of::<super::ProofTrackerCheckpoint>() + size_of::<ProofStep>() + 64 - 1;
    assert!(matches!(
        tracker.rollback_checkpoint_bounded(before_step_payload),
        Err(CheckpointCloneError::LimitExceeded)
    ));
    assert!(matches!(
        tracker.rollback_checkpoint_bounded(usize::MAX),
        Err(CheckpointCloneError::UnsupportedPayload)
    ));
}

#[test]
fn tracker_reset_invalidates_an_existing_checkpoint() {
    let mut tracker = ProofTracker::new();
    let outer = tracker
        .rollback_checkpoint()
        .expect("empty tracker footprint is representable");

    tracker.reset_session();
    assert!(
        !tracker.rollback_to(outer),
        "reset changed the ledger epoch"
    );
}

#[test]
fn checkpoint_from_distinct_same_epoch_tracker_is_rejected() {
    let tracker = ProofTracker::new();
    let checkpoint = tracker
        .rollback_checkpoint()
        .expect("empty tracker footprint is representable");
    let mut replacement = ProofTracker::new();
    let replacement_checkpoint = replacement
        .rollback_checkpoint()
        .expect("empty replacement footprint is representable");
    replacement.enable();
    replacement
        .add_assumption(TermId(99), None)
        .expect("tracking is enabled");

    assert!(!replacement.rollback_to(checkpoint));
    assert_eq!(replacement.num_steps(), 0);
    assert!(
        !replacement.rollback_to(replacement_checkpoint),
        "a foreign rollback must invalidate older checkpoints of the replacement ledger"
    );
}

#[test]
fn checkpointed_maps_do_not_use_tombstone_creating_mutation() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let tracker_source = std::fs::read_to_string(root.join("src/proof_tracker/mod.rs"))
        .expect("read proof tracker source");
    let dedup_source = std::fs::read_to_string(root.join("src/proof_tracker/lemma_dedup.rs"))
        .expect("read lemma dedup source");
    let proof_source =
        std::fs::read_to_string(root.join("../ay-core/src/proof.rs")).expect("read proof source");
    let compact = tracker_source
        .chars()
        .chain(dedup_source.chars())
        .chain(proof_source.chars())
        .filter(|ch| !ch.is_whitespace())
        .collect::<String>();
    for field in [
        "assumption_map",
        "lemma_map",
        "scope_assumption_maps",
        "scope_lemma_maps",
        "scope_named_steps",
        "named_steps",
        "buckets",
    ] {
        for method in [
            "remove",
            "remove_entry",
            "retain",
            "extract_if",
            "drain",
            "entry",
        ] {
            assert!(
                !compact.contains(&format!("{field}.{method}(")),
                "{field}.{method} can leave tombstones; revise checkpoint map accounting first"
            );
        }
    }
}

#[test]
fn rollback_restores_steps_removed_by_a_speculative_pop() {
    let mut tracker = ProofTracker::new();
    tracker.enable();
    tracker
        .add_assumption(TermId(1), None)
        .expect("tracking is enabled");
    tracker.push();
    tracker
        .add_assumption(TermId(2), None)
        .expect("tracking is enabled");
    let checkpoint = tracker
        .rollback_checkpoint()
        .expect("small test ledger fits checkpoint budget");

    assert!(tracker.pop());
    assert_eq!(tracker.num_steps(), 1);
    assert!(tracker.rollback_to(checkpoint));
    assert_eq!(tracker.num_steps(), 2);
    assert!(tracker.pop(), "checkpointed scope must also be restored");
    assert_eq!(tracker.num_steps(), 1);
}

#[test]
fn checkpoint_rollback_restores_entire_proof_ledger() {
    let mut tracker = ProofTracker::new();
    tracker.enable();
    tracker.set_theory("LIA");
    tracker.push();
    let (outer_assumption, outer_lemma) = add_outer_entries(&mut tracker);
    let checkpoint = tracker.rollback_checkpoint().expect("small ledger fits");

    tracker
        .add_assumption(TermId(2), Some("discarded_assumption".to_string()))
        .expect("tracking is enabled");
    tracker.push();
    tracker
        .add_explicit_trust_lemma(vec![TermId(20), TermId(21)])
        .expect("tracking is enabled");
    tracker.set_theory("BV");
    tracker.disable();

    assert!(tracker.rollback_to(checkpoint));
    assert_eq!(tracker.num_steps(), 2);
    assert_eq!(tracker.scope_stack.len(), 1);
    assert!(tracker.is_enabled());
    assert_eq!(tracker.theory_name, "LIA");
    assert!(!tracker
        .proof
        .named_steps
        .contains_key("discarded_assumption"));
    assert_internal_id_invariants(&tracker);
    assert_outer_entries_dedup(&mut tracker, outer_assumption, outer_lemma);
    assert_eq!(
        tracker
            .add_assumption(TermId(2), Some("replacement".to_string()))
            .expect("tracking is enabled"),
        ProofId(2)
    );
    assert!(tracker.pop());
    assert_eq!(tracker.num_steps(), 0);
    assert!(!tracker.pop());
}

#[test]
fn checkpoint_rollback_rejects_replacement_ledger_id_aliases() {
    let mut tracker = ProofTracker::new();
    tracker.enable();
    tracker.set_theory("LIA");
    tracker
        .add_assumption(TermId(1), Some("entry".to_string()))
        .expect("tracking is enabled");
    let checkpoint = tracker.rollback_checkpoint().expect("small ledger fits");

    let moved = tracker.take_proof();
    assert_eq!(moved.steps.len(), 1);
    tracker
        .add_assumption(TermId(2), Some("replacement_ledger".to_string()))
        .expect("tracking is enabled");
    tracker.set_theory("BV");
    tracker.disable();

    assert!(!tracker.rollback_to(checkpoint));
    assert_eq!(tracker.num_steps(), 0);
    assert!(tracker.is_enabled());
    assert_eq!(tracker.theory_name, "LIA");
    assert!(tracker.assumption_map.is_empty());
    assert!(tracker.lemma_map.is_empty());
    assert!(tracker.proof.named_steps.is_empty());
    assert_internal_id_invariants(&tracker);
}

#[test]
fn checkpoint_rollback_can_repeat_without_proof_id_aliasing() {
    let mut tracker = ProofTracker::new();
    tracker.enable();
    tracker
        .add_assumption(TermId(1), Some("entry".to_string()))
        .expect("tracking is enabled");
    let checkpoint = tracker.rollback_checkpoint().expect("small ledger fits");
    tracker
        .add_assumption(TermId(2), Some("discarded".to_string()))
        .expect("tracking is enabled");

    assert!(tracker.rollback_to(checkpoint));
    let second = tracker.rollback_checkpoint().expect("small ledger fits");
    assert_eq!(
        tracker
            .add_assumption(TermId(3), Some("reused_id".to_string()))
            .expect("tracking is enabled"),
        ProofId(1)
    );
    assert!(tracker.rollback_to(second));
    assert_eq!(tracker.num_steps(), 1);
    assert!(tracker.proof.named_steps.contains_key("entry"));
    assert!(!tracker.proof.named_steps.contains_key("reused_id"));
    assert_internal_id_invariants(&tracker);
}

#[test]
fn checkpoint_rollback_removes_new_map_alias_to_old_step() {
    let mut tracker = ProofTracker::new();
    tracker.enable();
    tracker.set_theory("EUF");
    let term = TermId(40);
    let lemma = tracker
        .add_explicit_trust_lemma(vec![term])
        .expect("tracking is enabled");
    let checkpoint = tracker.rollback_checkpoint().expect("small ledger fits");

    let alias = tracker
        .add_assumption(term, Some("post_checkpoint_alias".to_string()))
        .expect("certified singleton is reusable");
    assert_eq!(alias, lemma);
    assert_eq!(tracker.num_steps(), 1);
    assert!(tracker.assumption_map.contains_key(&term));

    assert!(tracker.rollback_to(checkpoint));
    assert_eq!(tracker.num_steps(), 1);
    assert!(!tracker.assumption_map.contains_key(&term));
    assert_internal_id_invariants(&tracker);
}
