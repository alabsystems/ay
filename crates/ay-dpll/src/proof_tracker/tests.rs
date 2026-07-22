// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::incremental_state::IncrementalSubsystem;
use crate::theory_inference::{
    record_theory_conflict_unsat, record_theory_conflict_unsat_with_farkas,
};
use ay_core::TheoryLit;
use ay_core::{ProofStep, Sort, TermStore, TheoryConflict};
use num_bigint::BigInt;

fn assert_internal_id_invariants(tracker: &ProofTracker) {
    let len = u32::try_from(tracker.proof.steps.len())
        .expect("proof step count should fit in u32 for tests");
    assert!(
        tracker.assumption_map.values().all(|id| id.0 < len),
        "assumption_map contains id outside proof.steps"
    );
    assert!(
        tracker.lemma_map.values().all(|id| id.0 < len),
        "lemma_map contains id outside proof.steps"
    );
    assert!(
        tracker.proof.named_steps.values().all(|id| id.0 < len),
        "named_steps contains id outside proof.steps"
    );
}

fn add_outer_entries(tracker: &mut ProofTracker) -> (ProofId, ProofId) {
    let outer_assumption = tracker
        .add_assumption(TermId(1), Some("h_outer".to_string()))
        .expect("proof tracking enabled");
    let outer_lemma = tracker
        .add_theory_lemma(vec![TermId(10)])
        .expect("proof tracking enabled");
    (outer_assumption, outer_lemma)
}

fn add_inner_entries(
    tracker: &mut ProofTracker,
    assumption_name: &str,
    kind_clause: &[TermId],
    farkas_clause: &[TermId],
) -> (ProofId, ProofId, ProofId) {
    let inner_assumption = tracker
        .add_assumption(TermId(2), Some(assumption_name.to_string()))
        .expect("proof tracking enabled");
    let inner_kind_lemma = tracker
        .add_theory_lemma_with_farkas_and_kind(
            kind_clause.to_vec(),
            FarkasAnnotation::from_ints(&[1, 1]),
            TheoryLemmaKind::LiaGeneric,
        )
        .expect("proof tracking enabled");
    let inner_farkas_lemma = tracker
        .add_theory_lemma_with_farkas_and_kind(
            farkas_clause.to_vec(),
            FarkasAnnotation::from_ints(&[1]),
            TheoryLemmaKind::LraFarkas,
        )
        .expect("proof tracking enabled");
    (inner_assumption, inner_kind_lemma, inner_farkas_lemma)
}

fn assert_triple_ids(
    actual: (ProofId, ProofId, ProofId),
    expected0: ProofId,
    expected1: ProofId,
    expected2: ProofId,
) {
    let (id0, id1, id2) = actual;
    assert_eq!(id0, expected0);
    assert_eq!(id1, expected1);
    assert_eq!(id2, expected2);
}

fn assert_outer_entries_dedup(
    tracker: &mut ProofTracker,
    expected_assumption: ProofId,
    expected_lemma: ProofId,
) {
    let outer_assumption_again = tracker
        .add_assumption(TermId(1), Some("h_outer_again".to_string()))
        .expect("proof tracking enabled");
    assert_eq!(outer_assumption_again, expected_assumption);

    let outer_lemma_again = tracker
        .add_theory_lemma(vec![TermId(10)])
        .expect("proof tracking enabled");
    assert_eq!(outer_lemma_again, expected_lemma);
}

fn assert_inner_entries_dedup(
    tracker: &mut ProofTracker,
    kind_clause: &[TermId],
    farkas_clause: &[TermId],
    expected_kind_lemma: ProofId,
    expected_farkas_lemma: ProofId,
) {
    let fresh_inner_kind_again = tracker
        .add_theory_lemma_with_farkas_and_kind(
            kind_clause.to_vec(),
            FarkasAnnotation::from_ints(&[1, 1]),
            TheoryLemmaKind::LiaGeneric,
        )
        .expect("proof tracking enabled");
    assert_eq!(fresh_inner_kind_again, expected_kind_lemma);

    let fresh_inner_farkas_again = tracker
        .add_theory_lemma_with_farkas_and_kind(
            farkas_clause.to_vec(),
            FarkasAnnotation::from_ints(&[1]),
            TheoryLemmaKind::LraFarkas,
        )
        .expect("proof tracking enabled");
    assert_eq!(fresh_inner_farkas_again, expected_farkas_lemma);
}

#[test]
fn test_tracker_disabled_by_default() {
    let tracker = ProofTracker::new();
    assert!(!tracker.is_enabled());
}

#[test]
fn test_enable_disable() {
    let mut tracker = ProofTracker::new();
    tracker.enable();
    assert!(tracker.is_enabled());
    tracker.disable();
    assert!(!tracker.is_enabled());
}

#[test]
fn test_assumption_when_disabled() {
    let mut tracker = ProofTracker::new();
    let result = tracker.add_assumption(TermId(1), None);
    assert!(result.is_none());
}

#[test]
fn test_assumption_when_enabled() {
    let mut tracker = ProofTracker::new();
    tracker.enable();

    let id = tracker.add_assumption(TermId(1), Some("h1".to_string()));
    assert!(id.is_some());
    assert_eq!(tracker.num_steps(), 1);

    // Adding same assumption returns same ID
    let id2 = tracker.add_assumption(TermId(1), None);
    assert_eq!(id, id2);
    assert_eq!(tracker.num_steps(), 1);
}

#[test]
fn test_theory_lemma() {
    let mut tracker = ProofTracker::new();
    tracker.enable();
    tracker.set_theory("EUF");

    let clause = vec![TermId(1), TermId(2)];
    let id = tracker.add_theory_lemma(clause.clone());
    assert!(id.is_some());
    assert_eq!(tracker.num_steps(), 1);

    // Adding same lemma returns same ID
    let id2 = tracker.add_theory_lemma(clause);
    assert_eq!(id, id2);
    assert_eq!(tracker.num_steps(), 1);

    // A different ordering is treated as distinct (order is significant for Alethe rules)
    let clause2 = vec![TermId(2), TermId(1)];
    let id3 = tracker.add_theory_lemma(clause2);
    assert_ne!(id, id3);
    assert_eq!(tracker.num_steps(), 2);
}

#[test]
fn test_uncertified_arithmetic_kind_records_generic_8866() {
    let mut tracker = ProofTracker::new();
    tracker.enable();
    tracker.set_theory("LIA");

    let clause = vec![TermId(1), TermId(2)];
    let id = tracker
        .add_theory_lemma_with_kind(clause.clone(), TheoryLemmaKind::LiaGeneric)
        .expect("proof tracking enabled");
    assert_eq!(tracker.num_steps(), 1);

    let proof = tracker.take_proof();
    match proof.get_step(id) {
        Some(ProofStep::TheoryLemma { kind, farkas, .. }) => {
            assert_eq!(
                *kind,
                TheoryLemmaKind::Generic,
                "LiaGeneric without Farkas/LIA evidence must stay trusted"
            );
            assert!(farkas.is_none());
        }
        other => panic!("expected TheoryLemma step, got {other:?}"),
    }
}

#[test]
fn test_uncertified_lra_farkas_kind_records_generic_8866() {
    let mut tracker = ProofTracker::new();
    tracker.enable();
    tracker.set_theory("LRA");

    let clause = vec![TermId(3), TermId(4)];
    let id = tracker
        .add_theory_lemma_with_kind(clause, TheoryLemmaKind::LraFarkas)
        .expect("proof tracking enabled");

    let proof = tracker.take_proof();
    match proof.get_step(id) {
        Some(ProofStep::TheoryLemma { kind, farkas, .. }) => {
            assert_eq!(
                *kind,
                TheoryLemmaKind::Generic,
                "LraFarkas without Farkas evidence must stay trusted"
            );
            assert!(farkas.is_none());
        }
        other => panic!("expected TheoryLemma step, got {other:?}"),
    }
}

#[test]
fn test_reset() {
    let mut tracker = ProofTracker::new();
    tracker.enable();
    tracker.add_assumption(TermId(1), None);
    assert_eq!(tracker.num_steps(), 1);

    tracker.reset();
    assert_eq!(tracker.num_steps(), 0);
    assert!(tracker.is_enabled()); // Enabled state preserved
}

#[test]
fn test_take_proof() {
    let mut tracker = ProofTracker::new();
    tracker.enable();
    tracker.add_assumption(TermId(1), None);

    let proof = tracker.take_proof();
    assert_eq!(proof.len(), 1);
    assert_eq!(tracker.num_steps(), 0);
}

// -- Push/pop scoping tests (#4534) --

#[test]
fn test_push_pop_removes_scoped_assumptions() {
    let mut tracker = ProofTracker::new();
    tracker.enable();

    tracker.add_assumption(TermId(1), Some("h0".to_string()));
    assert_eq!(tracker.num_steps(), 1);

    tracker.push();
    tracker.add_assumption(TermId(2), Some("h1".to_string()));
    assert_eq!(tracker.num_steps(), 2);

    tracker.pop();
    assert_eq!(
        tracker.num_steps(),
        1,
        "scoped assumption should be removed"
    );

    // Re-adding TermId(2) after pop should get a new ProofId
    let id = tracker.add_assumption(TermId(2), Some("h1_fresh".to_string()));
    assert!(id.is_some());
    assert_eq!(tracker.num_steps(), 2);
}

#[test]
fn test_push_pop_discards_scoped_steps() {
    let mut tracker = ProofTracker::new();
    tracker.enable();
    tracker.set_theory("EUF");

    // Global scope: add assumption A
    tracker.add_assumption(TermId(1), Some("h0".to_string()));
    assert_eq!(tracker.num_steps(), 1);

    // Push scope
    tracker.push();

    // Scoped: add assumption B and a theory lemma
    tracker.add_assumption(TermId(2), Some("h1".to_string()));
    tracker.add_theory_lemma(vec![TermId(3), TermId(4)]);
    assert_eq!(tracker.num_steps(), 3);

    // Pop: scoped steps discarded
    tracker.pop();
    assert_eq!(tracker.num_steps(), 1);

    // Global assumption A still present and dedup-cached
    let id_again = tracker.add_assumption(TermId(1), None);
    assert!(id_again.is_some());
    assert_eq!(tracker.num_steps(), 1); // No new step added

    // Scoped assumption B is gone -- re-adding creates a new step
    let id_b = tracker.add_assumption(TermId(2), None);
    assert!(id_b.is_some());
    assert_eq!(tracker.num_steps(), 2);
}

#[test]
fn test_push_pop_removes_scoped_lemmas() {
    let mut tracker = ProofTracker::new();
    tracker.enable();
    tracker.set_theory("LRA");

    let outer_clause = vec![TermId(10), TermId(11)];
    tracker.add_theory_lemma(outer_clause.clone());
    assert_eq!(tracker.num_steps(), 1);

    tracker.push();
    let inner_clause = vec![TermId(20), TermId(21)];
    tracker.add_theory_lemma(inner_clause.clone());
    assert_eq!(tracker.num_steps(), 2);

    tracker.pop();
    assert_eq!(tracker.num_steps(), 1, "scoped lemma should be removed");

    // The outer lemma still deduplicates (its ProofId is below the watermark)
    let outer_id2 = tracker.add_theory_lemma(outer_clause);
    assert!(outer_id2.is_some());
    assert_eq!(tracker.num_steps(), 1, "outer lemma should deduplicate");

    // The inner lemma is fresh after pop (its dedup entry was removed)
    let inner_id2 = tracker.add_theory_lemma(inner_clause);
    assert!(inner_id2.is_some());
    assert_eq!(tracker.num_steps(), 2, "inner lemma should be re-added");
}

#[test]
fn test_push_pop_cleans_ids_for_all_insertion_paths() {
    let mut tracker = ProofTracker::new();
    tracker.enable();
    tracker.set_theory("LIA");

    let kind_clause = [TermId(20), TermId(21)];
    let farkas_clause = [TermId(30)];
    let (outer_assumption, outer_lemma) = add_outer_entries(&mut tracker);
    assert_eq!(outer_assumption, ProofId(0));
    assert_eq!(outer_lemma, ProofId(1));

    tracker.push();
    assert_triple_ids(
        add_inner_entries(&mut tracker, "h_inner", &kind_clause, &farkas_clause),
        ProofId(2),
        ProofId(3),
        ProofId(4),
    );

    assert_internal_id_invariants(&tracker);

    tracker.pop();

    // Scoped named assumption and lemma entries should be removed.
    assert_eq!(tracker.num_steps(), 2);
    assert!(
        !tracker.proof.named_steps.contains_key("h_inner"),
        "named step from popped scope must be removed"
    );
    assert_internal_id_invariants(&tracker);

    let fresh_ids = add_inner_entries(&mut tracker, "h_inner_fresh", &kind_clause, &farkas_clause);
    assert_triple_ids(fresh_ids, ProofId(2), ProofId(3), ProofId(4));
    assert_outer_entries_dedup(&mut tracker, outer_assumption, outer_lemma);
    assert_inner_entries_dedup(
        &mut tracker,
        &kind_clause,
        &farkas_clause,
        ProofId(3),
        ProofId(4),
    );

    assert_eq!(tracker.num_steps(), 5);
    assert_internal_id_invariants(&tracker);
}

#[test]
fn test_push_pop_nested_scopes() {
    let mut tracker = ProofTracker::new();
    tracker.enable();
    tracker.set_theory("LRA");

    tracker.add_assumption(TermId(10), None); // step 0 (global)
    assert_eq!(tracker.num_steps(), 1);

    tracker.push(); // scope 1
    tracker.add_theory_lemma(vec![TermId(20)]); // step 1
    assert_eq!(tracker.num_steps(), 2);

    tracker.push(); // scope 2
    tracker.add_theory_lemma(vec![TermId(30)]); // step 2
    assert_eq!(tracker.num_steps(), 3);

    tracker.pop(); // pop scope 2
    assert_eq!(tracker.num_steps(), 2);

    tracker.pop(); // pop scope 1
    assert_eq!(tracker.num_steps(), 1);
}

#[test]
fn test_nested_push_pop() {
    let mut tracker = ProofTracker::new();
    tracker.enable();

    tracker.add_assumption(TermId(1), None);
    assert_eq!(tracker.num_steps(), 1);

    tracker.push(); // scope 1
    tracker.add_assumption(TermId(2), None);
    assert_eq!(tracker.num_steps(), 2);

    tracker.push(); // scope 2
    tracker.add_assumption(TermId(3), None);
    assert_eq!(tracker.num_steps(), 3);

    tracker.pop(); // exit scope 2
    assert_eq!(tracker.num_steps(), 2);

    tracker.pop(); // exit scope 1
    assert_eq!(tracker.num_steps(), 1);
}

#[test]
fn test_pop_without_push_is_noop() {
    let mut tracker = ProofTracker::new();
    tracker.enable();
    tracker.add_assumption(TermId(1), None);
    assert_eq!(tracker.num_steps(), 1);

    tracker.pop(); // no matching push
    assert_eq!(tracker.num_steps(), 1, "pop without push should be a no-op");
}

#[test]
fn test_reset_clears_scope_stack() {
    let mut tracker = ProofTracker::new();
    tracker.enable();
    tracker.push();
    tracker.add_assumption(TermId(1), None);
    tracker.push();
    tracker.add_assumption(TermId(2), None);

    tracker.reset();
    assert_eq!(tracker.num_steps(), 0);

    // Pop should be a no-op after reset (scope stack was cleared)
    tracker.pop();
    assert_eq!(tracker.num_steps(), 0);
}

#[test]
fn test_reset_session_preserves_scope_stack() {
    let mut tracker = ProofTracker::new();
    tracker.enable();
    tracker.set_theory("LRA");

    // Push two scopes, add content at each level
    tracker.push(); // scope 1
    tracker.add_assumption(TermId(1), Some("h1".to_string()));
    assert_eq!(tracker.num_steps(), 1);

    tracker.push(); // scope 2
    tracker.add_theory_lemma(vec![TermId(10), TermId(11)]);
    assert_eq!(tracker.num_steps(), 2);

    // reset_session clears proof content but preserves scope stack
    tracker.reset_session();
    assert_eq!(tracker.num_steps(), 0, "proof content should be cleared");

    // Pop should succeed (scope stack preserved, returns true)
    let ok = tracker.pop(); // pop scope 2
    assert!(
        ok,
        "pop after reset_session should succeed (scope preserved)"
    );

    let ok = tracker.pop(); // pop scope 1
    assert!(ok, "second pop after reset_session should succeed");

    // No more scopes — pop should return false
    let ok = tracker.pop();
    assert!(!ok, "pop with empty scope stack should return false");
}

#[test]
fn test_reset_session_watermarks_zeroed() {
    let mut tracker = ProofTracker::new();
    tracker.enable();

    tracker.push(); // scope 1
    tracker.add_assumption(TermId(1), None);
    tracker.add_assumption(TermId(2), None);
    assert_eq!(tracker.num_steps(), 2);

    // After reset_session, watermarks are 0 so the next pop removes
    // everything added in the new session
    tracker.reset_session();
    assert_eq!(tracker.num_steps(), 0);

    // Add new content in scope 1
    tracker.add_assumption(TermId(10), None);
    tracker.add_theory_lemma(vec![TermId(20)]);
    assert_eq!(tracker.num_steps(), 2);

    // Pop scope 1: watermark was zeroed, so all new content is removed
    let ok = tracker.pop();
    assert!(ok);
    assert_eq!(
        tracker.num_steps(),
        0,
        "zeroed watermark should remove all content added after reset_session"
    );
}

#[test]
fn test_push_pop_proof_isolation() {
    // Simulates: push, assert A, check-sat -> UNSAT, pop, assert B, check-sat -> UNSAT
    // Second proof must not reference A's theory lemmas.
    let mut tracker = ProofTracker::new();
    tracker.enable();
    tracker.set_theory("LRA");

    // --- Scope 1: assert A ---
    tracker.push();

    let a_assumption = tracker.add_assumption(TermId(100), Some("hA".to_string()));
    assert!(a_assumption.is_some());
    let a_lemma = tracker.add_theory_lemma(vec![TermId(100), TermId(101)]);
    assert!(a_lemma.is_some());
    assert_eq!(tracker.num_steps(), 2); // assume + lemma

    // Simulate check-sat producing a proof and taking it
    let proof_1 = tracker.take_proof();
    assert_eq!(proof_1.len(), 2);
    // After take_proof, the tracker's proof is empty but maps have entries

    // --- Pop scope 1 ---
    tracker.pop();
    // After pop, the stale map entries from scope 1 are removed

    // --- Scope 2: assert B (no push needed if this is the outer scope) ---
    // Reset for the new check-sat (as the executor does)
    tracker.reset();

    let b_assumption = tracker.add_assumption(TermId(200), Some("hB".to_string()));
    assert!(b_assumption.is_some());
    let b_lemma = tracker.add_theory_lemma(vec![TermId(200), TermId(201)]);
    assert!(b_lemma.is_some());
    assert_eq!(tracker.num_steps(), 2);

    let proof_2 = tracker.take_proof();
    assert_eq!(proof_2.len(), 2);

    // Verify proof_2 does NOT contain A's terms
    for step in &proof_2.steps {
        match step {
            ProofStep::Assume(term) => {
                assert_ne!(
                    *term,
                    TermId(100),
                    "second proof must not reference A's assumption"
                );
            }
            ProofStep::TheoryLemma { clause, .. } => {
                assert!(
                    !clause.contains(&TermId(101)),
                    "second proof must not reference A's theory lemma"
                );
            }
            _ => {}
        }
    }
}

#[test]
#[cfg(debug_assertions)]
fn test_farkas_coefficient_count_mismatch_panics() {
    let mut tracker = ProofTracker::new();
    tracker.enable();
    tracker.set_theory("LRA");

    // Farkas annotation has 1 coefficient but clause has 2 literals.
    let clause = vec![TermId(10), TermId(20)];
    let farkas = FarkasAnnotation::from_ints(&[1]); // 1 coeff, 2 lits

    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        tracker.add_theory_lemma_with_farkas_and_kind(clause, farkas, TheoryLemmaKind::LraFarkas);
    }));
    assert!(
        result.is_err(),
        "Farkas coefficient/clause length mismatch must be caught"
    );
}

#[test]
fn test_record_theory_conflict_unsat_basic() {
    let mut tracker = ProofTracker::new();
    tracker.enable();
    tracker.set_theory("EUF");

    let mut negations = HashMap::default();
    negations.insert(TermId(10), TermId(11));
    negations.insert(TermId(20), TermId(21));

    let conflict = vec![
        TheoryLit::new(TermId(10), true),
        TheoryLit::new(TermId(20), true),
    ];

    let id = record_theory_conflict_unsat(&mut tracker, None, &negations, &conflict);
    assert!(id.is_some(), "enabled tracker should produce a proof step");
    assert_eq!(tracker.num_steps(), 1);
}

#[test]
fn test_record_theory_conflict_unsat_disabled_returns_none() {
    let mut tracker = ProofTracker::new();
    // Tracker is disabled (default)

    let negations = HashMap::default();
    let conflict = vec![TheoryLit::new(TermId(10), true)];

    let id = record_theory_conflict_unsat(&mut tracker, None, &negations, &conflict);
    assert!(id.is_none(), "disabled tracker must return None");
    assert_eq!(tracker.num_steps(), 0);
}

#[test]
fn test_record_theory_conflict_unsat_integer_bounds_use_lra_farkas_when_unit_certificate_is_valid()
{
    let mut tracker = ProofTracker::new();
    tracker.enable();
    tracker.set_theory("LIA");

    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let one = terms.mk_int(BigInt::from(1));
    let zero = terms.mk_int(BigInt::from(0));
    let ge = terms.mk_ge(x, one);
    let le = terms.mk_le(x, zero);
    let not_ge = terms.mk_not(ge);
    let not_le = terms.mk_not(le);

    let mut negations = HashMap::default();
    negations.insert(ge, not_ge);
    negations.insert(le, not_le);

    let conflict = vec![TheoryLit::new(ge, true), TheoryLit::new(le, true)];
    let id = record_theory_conflict_unsat(&mut tracker, Some(&terms), &negations, &conflict)
        .expect("enabled tracker should record integer arithmetic conflicts");
    assert_eq!(tracker.num_steps(), 1);

    let proof = tracker.take_proof();
    match proof.get_step(id) {
        Some(ProofStep::TheoryLemma { kind, .. }) => {
            assert_eq!(
                *kind,
                TheoryLemmaKind::LraFarkas,
                "Farkas-valid integer conflicts must export la_generic/LraFarkas"
            );
        }
        other => panic!("expected TheoryLemma step, got {other:?}"),
    }
}

#[test]
fn test_record_theory_conflict_unsat_with_invalid_integer_farkas_stays_lia_generic() {
    let mut tracker = ProofTracker::new();
    tracker.enable();
    tracker.set_theory("LIA");

    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let one = terms.mk_int(BigInt::from(1));
    let zero = terms.mk_int(BigInt::from(0));
    let ge = terms.mk_ge(x, one);
    let le = terms.mk_le(x, zero);
    let not_ge = terms.mk_not(ge);
    let not_le = terms.mk_not(le);

    let mut negations = HashMap::default();
    negations.insert(ge, not_ge);
    negations.insert(le, not_le);

    let conflict = TheoryConflict::with_farkas(
        vec![TheoryLit::new(ge, true), TheoryLit::new(le, true)],
        FarkasAnnotation::from_ints(&[1, 0]),
    );
    let id =
        record_theory_conflict_unsat_with_farkas(&mut tracker, Some(&terms), &negations, &conflict)
            .expect("enabled tracker should record arithmetic conflicts with explicit annotations");

    let proof = tracker.take_proof();
    match proof.get_step(id) {
        Some(ProofStep::TheoryLemma { kind, .. }) => {
            assert_eq!(
                *kind,
                TheoryLemmaKind::LraFarkas,
                "shape-only Farkas check accepts [1, 0] as valid (zero coeff = unused constraint)",
            );
        }
        other => panic!("expected TheoryLemma step, got {other:?}"),
    }
}

#[test]
fn test_record_theory_conflict_unsat_with_strict_integer_bounds_uses_lra_farkas() {
    let mut tracker = ProofTracker::new();
    tracker.enable();
    tracker.set_theory("LIA");

    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let ten = terms.mk_int(BigInt::from(10));
    let five = terms.mk_int(BigInt::from(5));
    let gt = terms.mk_gt(x, ten);
    let lt = terms.mk_lt(x, five);
    let not_gt = terms.mk_not(gt);
    let not_lt = terms.mk_not(lt);

    let mut negations = HashMap::default();
    negations.insert(gt, not_gt);
    negations.insert(lt, not_lt);

    let conflict = vec![TheoryLit::new(gt, true), TheoryLit::new(lt, true)];
    let id = record_theory_conflict_unsat(&mut tracker, Some(&terms), &negations, &conflict)
        .expect("enabled tracker should record strict integer bound conflicts");

    let proof = tracker.take_proof();
    match proof.get_step(id) {
        Some(ProofStep::TheoryLemma { kind, .. }) => {
            assert_eq!(
                *kind,
                TheoryLemmaKind::LraFarkas,
                "strict Farkas-valid integer conflicts must export la_generic/LraFarkas"
            );
        }
        other => panic!("expected TheoryLemma step, got {other:?}"),
    }
}
