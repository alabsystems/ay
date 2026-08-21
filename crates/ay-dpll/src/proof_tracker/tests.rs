// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::incremental_state::IncrementalSubsystem;
use crate::theory_inference::{
    record_theory_conflict_unsat, record_theory_conflict_unsat_with_annotation,
    record_theory_conflict_unsat_with_farkas,
};
use ay_core::TheoryLit;
use ay_core::{ProofStep, Sort, TermStore, TheoryConflict};
use num_bigint::BigInt;
use num_rational::BigRational;

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
        .add_explicit_trust_lemma(vec![TermId(10)])
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
        .add_explicit_trust_lemma(vec![TermId(10)])
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
fn test_single_forall_skolem_ite_nnf_bridge_is_strict_context_valid() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("ite_nnf_x", Sort::Int);
    let cond = terms.mk_var("ite_nnf_cond", Sort::Bool);
    let p_x = terms.mk_app(Symbol::named("ite_nnf_p"), [x], Sort::Bool);
    let q_x = terms.mk_app(Symbol::named("ite_nnf_q"), [x], Sort::Bool);
    let r_x = terms.mk_app(Symbol::named("ite_nnf_r"), [x], Sort::Bool);
    let branch_x = terms.mk_ite_raw(cond, p_x, q_x);
    let not_r_x = terms.mk_not_raw(r_x);
    let quantified_body = terms.mk_or(vec![branch_x, not_r_x]);
    let quantified = terms.mk_forall(vec![("ite_nnf_x".to_string(), Sort::Int)], quantified_body);
    let original_not_forall = terms.mk_not_raw(quantified);

    let witness_name = "sk!ite_nnf_x_fixture";
    let witness = terms.mk_var(witness_name, Sort::Int);
    terms.mark_skolem_symbol(witness_name);
    let p_witness = terms.mk_app(Symbol::named("ite_nnf_p"), [witness], Sort::Bool);
    let q_witness = terms.mk_app(Symbol::named("ite_nnf_q"), [witness], Sort::Bool);
    let r_witness = terms.mk_app(Symbol::named("ite_nnf_r"), [witness], Sort::Bool);
    let branch_witness = terms.mk_ite_raw(cond, p_witness, q_witness);
    let not_r_witness = terms.mk_not_raw(r_witness);
    let instance = terms.mk_or(vec![branch_witness, not_r_witness]);
    let not_p_witness = terms.mk_not(p_witness);
    let not_q_witness = terms.mk_not(q_witness);
    let nnf_branch = terms.mk_ite(cond, not_p_witness, not_q_witness);
    let skolemized_body = terms.mk_and(vec![r_witness, nnf_branch]);

    let forged_branch = terms.mk_app(Symbol::named("ite_nnf_forged"), [witness], Sort::Bool);
    let forged_not_branch = terms.mk_not(forged_branch);
    let forged_nnf_branch = terms.mk_ite(cond, not_p_witness, forged_not_branch);
    let forged_body = terms.mk_and(vec![r_witness, forged_nnf_branch]);
    let mut rejecting_tracker = ProofTracker::new();
    rejecting_tracker.enable();
    assert!(
        rejecting_tracker
            .add_single_forall_skolemized_assertion(
                &mut terms,
                original_not_forall,
                quantified,
                instance,
                witness,
                forged_body,
            )
            .is_none(),
        "a changed ITE branch must not receive Skolem proof authority"
    );
    assert_eq!(
        rejecting_tracker.num_steps(),
        0,
        "shape rejection must occur before any proof step is emitted"
    );

    let mut tracker = ProofTracker::new();
    tracker.enable();
    let derived = tracker
        .add_single_forall_skolemized_assertion(
            &mut terms,
            original_not_forall,
            quantified,
            instance,
            witness,
            skolemized_body,
        )
        .expect("exact ITE NNF complement must have a checked derivation");
    let mut proof = tracker.take_proof();
    assert!(
        matches!(
            proof.get_step(derived),
            Some(ProofStep::Resolution { clause, .. })
                if clause == &[skolemized_body]
        ),
        "tracker must derive the exact solver-visible NNF conjunction"
    );

    let not_skolemized_body = terms.mk_not_raw(skolemized_body);
    let negated = proof.add_assume(not_skolemized_body, None);
    proof.add_resolution(Vec::new(), skolemized_body, derived, negated);
    let quality = ay_proof::check_proof_strict_with_context(
        &proof,
        &terms,
        None,
        None,
        Some(&[original_not_forall, not_skolemized_body]),
    )
    .expect("ITE NNF derivation must pass the independent strict checker");
    assert!(quality.is_complete());
    assert_eq!(quality.trust_count, 0);
}

include!("tests/normalized_forall.rs");

#[test]
fn exact_forall_instance_survives_ground_constant_folding() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("exact_forall_x", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let body = terms.mk_lt(zero, x);
    let forall = terms.mk_forall(vec![("exact_forall_x".to_string(), Sort::Int)], body);
    let exact = terms.mk_app(Symbol::named("<"), [zero, zero], Sort::Bool);
    let simplified = terms.mk_lt(zero, zero);
    assert_ne!(
        exact, simplified,
        "the regression requires a folded instance"
    );

    let mut tracker = ProofTracker::new();
    tracker.enable();
    tracker
        .add_forall_instantiated_assertion(&mut terms, forall, &[zero], exact)
        .expect("the exact structural instance must be derivable");
    let proof = tracker.take_proof();
    assert!(
        proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::Resolution { clause, .. } if clause.is_empty()
        )),
        "an independently false arithmetic instance must close before ground folding"
    );
    let quality =
        ay_proof::check_proof_strict_with_context(&proof, &terms, None, None, Some(&[forall]))
            .expect("exact forall_inst plus checked Farkas complement must pass strict checking");
    assert!(quality.is_complete());
    assert_eq!(quality.trust_count, 0);

    let mut rejected = ProofTracker::new();
    rejected.enable();
    assert!(
        rejected
            .add_forall_instantiated_assertion(&mut terms, forall, &[zero], simplified)
            .is_none(),
        "the simplified constant must never be emitted as forall_inst"
    );
    assert_eq!(rejected.num_steps(), 0);
}

/// Producer/checker parity for #quant-trigger-nested. E-matching can now find
/// an outer trigger below a preserved inner binder, so the exact proof producer
/// must be able to derive the corresponding nested `forall_inst` rather than
/// marking every such solve translation-incomplete. Two instantiations close a
/// concrete arithmetic contradiction, and AY's strict checker is the authority
/// for the complete chain.
#[test]
fn exact_forall_instance_under_nested_binder_strictly_checks() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("producer_outer_x", Sort::Int);
    let y = terms.mk_var("producer_inner_y", Sort::Int);
    let body = terms.mk_app(Symbol::named("<"), [y, x], Sort::Bool);
    let trigger = terms.mk_app(Symbol::named("producer_nested_f"), [x, y], Sort::Int);
    let inner = terms.mk_forall_with_triggers(
        vec![("producer_inner_y".to_string(), Sort::Int)],
        body,
        vec![vec![trigger]],
    );
    let outer = terms.mk_forall(vec![("producer_outer_x".to_string(), Sort::Int)], inner);
    let zero = terms.mk_int(BigInt::from(0));
    let outer_instance_body = terms.mk_app(Symbol::named("<"), [y, zero], Sort::Bool);
    let outer_instance_trigger =
        terms.mk_app(Symbol::named("producer_nested_f"), [zero, y], Sort::Int);
    let outer_instance = terms.mk_forall_with_triggers(
        vec![("producer_inner_y".to_string(), Sort::Int)],
        outer_instance_body,
        vec![vec![outer_instance_trigger]],
    );
    let ground_instance = terms.mk_app(Symbol::named("<"), [zero, zero], Sort::Bool);

    let mut tracker = ProofTracker::new();
    tracker.enable();
    tracker
        .add_forall_instantiated_assertion(&mut terms, outer, &[zero], outer_instance)
        .expect("outer substitution beneath the preserved inner binder must be derivable");
    tracker
        .add_forall_instantiated_assertion(&mut terms, outer_instance, &[zero], ground_instance)
        .expect("the derived inner universal must remain available as proof authority");
    let proof = tracker.take_proof();
    assert!(proof.steps.iter().any(|step| matches!(
        step,
        ProofStep::Resolution { clause, .. } if clause.is_empty()
    )));
    let quality =
        ay_proof::check_proof_strict_with_context(&proof, &terms, None, None, Some(&[outer]))
            .expect("the nested forall_inst chain must pass AY's strict checker");
    assert!(quality.is_complete());
    assert_eq!(quality.trust_count, 0);
}

/// Tamper controls for the nested producer lane: a witness carrying the inner
/// binder's free name would be captured, and duplicate source binder names make
/// positional substitution ambiguous. Both must fail before emitting a proof
/// step; the strict checker independently rejects the same shapes.
#[test]
fn exact_nested_forall_instance_rejects_capture_and_duplicate_binders() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("producer_capture_x", Sort::Int);
    let y = terms.mk_var("producer_capture_y", Sort::Int);
    let p_xy = terms.mk_app(Symbol::named("producer_capture_p"), [x, y], Sort::Bool);
    let inner = terms.mk_forall(vec![("producer_capture_y".to_string(), Sort::Int)], p_xy);
    let outer = terms.mk_forall(vec![("producer_capture_x".to_string(), Sort::Int)], inner);

    let mut captured = ProofTracker::new();
    captured.enable();
    assert!(
        captured
            .add_forall_instantiated_assertion(&mut terms, outer, &[y], inner)
            .is_none(),
        "a witness named by the inner binder must not be captured"
    );
    assert_eq!(captured.num_steps(), 0);

    let duplicate_body = terms.mk_app(Symbol::named("producer_duplicate_p"), [x], Sort::Bool);
    let duplicate = terms.mk_forall(
        vec![
            ("producer_capture_x".to_string(), Sort::Int),
            ("producer_capture_x".to_string(), Sort::Int),
        ],
        duplicate_body,
    );
    let zero = terms.mk_int(BigInt::from(0));
    let one = terms.mk_int(BigInt::from(1));
    let duplicate_instance =
        terms.mk_app(Symbol::named("producer_duplicate_p"), [zero], Sort::Bool);
    let mut ambiguous = ProofTracker::new();
    ambiguous.enable();
    assert!(
        ambiguous
            .add_forall_instantiated_assertion(
                &mut terms,
                duplicate,
                &[zero, one],
                duplicate_instance,
            )
            .is_none(),
        "duplicate binder names must not collapse into one substitution slot"
    );
    assert_eq!(ambiguous.num_steps(), 0);
}

#[test]
fn exact_forall_instance_closes_with_checked_ground_evaluate() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("exact_eval_x", Sort::Real);
    let zero = terms.mk_int(BigInt::from(0));
    let to_int_x = terms.mk_app(Symbol::named("to_int"), [x], Sort::Int);
    let body = terms.mk_app(Symbol::named("="), [to_int_x, zero], Sort::Bool);
    let forall = terms.mk_forall(vec![("exact_eval_x".to_string(), Sort::Real)], body);
    let three_halves = terms.mk_rational(BigRational::new(BigInt::from(3), BigInt::from(2)));
    let grounded_to_int = terms.mk_app(Symbol::named("to_int"), [three_halves], Sort::Int);
    let exact = terms.mk_app(Symbol::named("="), [grounded_to_int, zero], Sort::Bool);

    let mut tracker = ProofTracker::new();
    tracker.enable();
    tracker
        .add_forall_instantiated_assertion(&mut terms, forall, &[three_halves], exact)
        .expect("the exact to_int instance must be derivable");
    let proof = tracker.take_proof();
    assert!(proof.steps.iter().any(|step| matches!(
        step,
        ProofStep::Step {
            rule: AletheRule::Evaluate,
            ..
        }
    )));
    assert!(proof.steps.iter().any(|step| matches!(
        step,
        ProofStep::Resolution { clause, .. } if clause.is_empty()
    )));
    let quality =
        ay_proof::check_proof_strict_with_context(&proof, &terms, None, None, Some(&[forall]))
            .expect("forall_inst plus ground evaluate chain must pass strict checking");
    assert!(quality.is_complete());
    assert_eq!(quality.trust_count, 0);
}

#[test]
fn test_theory_lemma() {
    let mut tracker = ProofTracker::new();
    tracker.enable();
    tracker.set_theory("EUF");

    let clause = vec![TermId(1), TermId(2)];
    let id = tracker.add_explicit_trust_lemma(clause.clone());
    assert!(id.is_some());
    assert_eq!(tracker.num_steps(), 1);

    // Adding same lemma returns same ID
    let id2 = tracker.add_explicit_trust_lemma(clause);
    assert_eq!(id, id2);
    assert_eq!(tracker.num_steps(), 1);

    // A different ordering is treated as distinct (order is significant for Alethe rules)
    let clause2 = vec![TermId(2), TermId(1)];
    let id3 = tracker.add_explicit_trust_lemma(clause2);
    assert_ne!(id, id3);
    assert_eq!(tracker.num_steps(), 2);
}

#[test]
fn certified_singleton_theory_lemma_is_reused_as_solver_assumption() {
    let mut tracker = ProofTracker::new();
    tracker.enable();
    tracker.set_theory("arrays");
    let packed_row = TermId(17);

    let lemma = tracker
        .add_theory_lemma_with_kind(
            vec![packed_row],
            TheoryLemmaKind::ArraySelectStore { index_eq: false },
        )
        .expect("proof tracking enabled");
    let registered = tracker
        .add_assumption(packed_row, None)
        .expect("proof tracking enabled");

    assert_eq!(registered, lemma);
    assert_eq!(tracker.num_steps(), 1);
    assert!(matches!(
        tracker.proof.get_step(lemma),
        Some(ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::ArraySelectStore { index_eq: false },
            ..
        })
    ));
}

#[test]
fn scoped_singleton_alias_preserves_outer_generic_lemma() {
    let mut tracker = ProofTracker::new();
    tracker.enable();
    tracker.set_theory("arrays");
    let packed_axiom = TermId(18);

    let outer = tracker
        .add_explicit_trust_lemma(vec![packed_axiom])
        .expect("proof tracking enabled");
    tracker.push();
    let inner = tracker
        .add_theory_lemma_with_kind(
            vec![packed_axiom],
            TheoryLemmaKind::ArraySelectStore { index_eq: true },
        )
        .expect("proof tracking enabled");
    assert_ne!(inner, outer);
    assert!(tracker.pop());

    let registered = tracker
        .add_assumption(packed_axiom, None)
        .expect("proof tracking enabled");
    assert_eq!(registered, outer);
    assert_eq!(tracker.num_steps(), 1);
    assert_internal_id_invariants(&tracker);
    assert!(matches!(
        tracker.proof.get_step(outer),
        Some(ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::Generic,
            ..
        })
    ));
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
    let first_id = tracker.add_assumption(TermId(1), None);

    let proof = tracker.take_proof();
    assert_eq!(proof.len(), 1);
    assert_eq!(tracker.num_steps(), 0);

    let second_id = tracker.add_assumption(TermId(1), None);
    assert_eq!(second_id, first_id);
    assert_eq!(
        tracker.num_steps(),
        1,
        "a term from the taken proof must be recorded in the new ledger"
    );
    assert!(matches!(
        tracker.take_proof().steps.as_slice(),
        [ProofStep::Assume(TermId(1))]
    ));
}

#[test]
fn test_take_proof_clears_singleton_lemma_dedup() {
    let mut tracker = ProofTracker::new();
    tracker.enable();
    tracker.set_theory("arrays");
    let packed_row = TermId(19);

    let first_id = tracker
        .add_theory_lemma_with_kind(
            vec![packed_row],
            TheoryLemmaKind::ArraySelectStore { index_eq: false },
        )
        .expect("proof tracking enabled");
    let first = tracker.take_proof();
    assert!(matches!(
        first.get_step(first_id),
        Some(ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::ArraySelectStore { index_eq: false },
            ..
        })
    ));

    let second_id = tracker
        .add_theory_lemma_with_kind(
            vec![packed_row],
            TheoryLemmaKind::ArraySelectStore { index_eq: false },
        )
        .expect("the new ledger must record the singleton again");
    assert_eq!(second_id, ProofId(0));
    assert_eq!(tracker.num_steps(), 1);
    assert_eq!(
        tracker.add_assumption(packed_row, None),
        Some(second_id),
        "solver registration must reuse the new ledger's real lemma step"
    );
    assert_eq!(tracker.num_steps(), 1);
    assert_internal_id_invariants(&tracker);
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
    tracker.add_explicit_trust_lemma(vec![TermId(3), TermId(4)]);
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
    tracker.add_explicit_trust_lemma(outer_clause.clone());
    assert_eq!(tracker.num_steps(), 1);

    tracker.push();
    let inner_clause = vec![TermId(20), TermId(21)];
    tracker.add_explicit_trust_lemma(inner_clause.clone());
    assert_eq!(tracker.num_steps(), 2);

    tracker.pop();
    assert_eq!(tracker.num_steps(), 1, "scoped lemma should be removed");

    // The outer lemma still deduplicates (its ProofId is below the watermark)
    let outer_id2 = tracker.add_explicit_trust_lemma(outer_clause);
    assert!(outer_id2.is_some());
    assert_eq!(tracker.num_steps(), 1, "outer lemma should deduplicate");

    // The inner lemma is fresh after pop (its dedup entry was removed)
    let inner_id2 = tracker.add_explicit_trust_lemma(inner_clause);
    assert!(inner_id2.is_some());
    assert_eq!(tracker.num_steps(), 2, "inner lemma should be re-added");
}

#[test]
fn test_push_pop_rollback_cleans_ids_for_all_insertion_paths() {
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
fn test_checkpoint_rollback_restores_entire_proof_ledger() {
    let mut tracker = ProofTracker::new();
    tracker.enable();
    tracker.set_theory("LIA");

    tracker.push();
    let (outer_assumption, outer_lemma) = add_outer_entries(&mut tracker);
    let checkpoint = tracker
        .rollback_checkpoint()
        .expect("small test ledger fits checkpoint budget");

    tracker
        .add_assumption(TermId(2), Some("discarded_assumption".to_string()))
        .expect("proof tracking enabled");
    tracker.push();
    tracker
        .add_explicit_trust_lemma(vec![TermId(20), TermId(21)])
        .expect("proof tracking enabled");
    tracker.set_theory("BV");
    tracker.disable();
    assert_eq!(tracker.scope_stack.len(), 2);
    assert_eq!(tracker.num_steps(), 4);

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

    let replacement = tracker
        .add_assumption(TermId(2), Some("replacement".to_string()))
        .expect("proof tracking enabled");
    assert_eq!(replacement, ProofId(2));

    assert!(
        tracker.pop(),
        "the scope present at checkpoint must survive"
    );
    assert_eq!(tracker.num_steps(), 0);
    assert!(!tracker.pop(), "speculative nested scope must be discarded");
    assert_internal_id_invariants(&tracker);
}

#[test]
fn test_checkpoint_rollback_rejects_replacement_ledger_id_aliases() {
    let mut tracker = ProofTracker::new();
    tracker.enable();
    tracker.set_theory("LIA");
    tracker
        .add_assumption(TermId(1), Some("entry".to_string()))
        .expect("proof tracking enabled");
    let checkpoint = tracker
        .rollback_checkpoint()
        .expect("small test ledger fits checkpoint budget");

    let moved = tracker.take_proof();
    assert_eq!(moved.steps.len(), 1);
    tracker
        .add_assumption(TermId(2), Some("replacement_ledger".to_string()))
        .expect("proof tracking enabled");
    tracker.set_theory("BV");
    tracker.disable();
    assert_eq!(tracker.num_steps(), 1, "ProofId(0) was reused");

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
fn test_checkpoint_rollback_can_repeat_without_proof_id_aliasing() {
    let mut tracker = ProofTracker::new();
    tracker.enable();
    tracker
        .add_assumption(TermId(1), Some("entry".to_string()))
        .expect("proof tracking enabled");
    let checkpoint = tracker
        .rollback_checkpoint()
        .expect("small test ledger fits checkpoint budget");
    tracker
        .add_assumption(TermId(2), Some("discarded".to_string()))
        .expect("proof tracking enabled");

    assert!(tracker.rollback_to(checkpoint));
    let checkpoint = tracker
        .rollback_checkpoint()
        .expect("restored small test ledger fits checkpoint budget");
    let reused = tracker
        .add_assumption(TermId(3), Some("reused_id".to_string()))
        .expect("proof tracking enabled");
    assert_eq!(reused, ProofId(1));

    assert!(tracker.rollback_to(checkpoint));
    assert_eq!(tracker.num_steps(), 1);
    assert!(tracker.proof.named_steps.contains_key("entry"));
    assert!(!tracker.proof.named_steps.contains_key("reused_id"));
    assert_internal_id_invariants(&tracker);
}

#[test]
fn test_checkpoint_rollback_removes_new_map_alias_to_old_step() {
    let mut tracker = ProofTracker::new();
    tracker.enable();
    tracker.set_theory("EUF");
    let term = TermId(40);
    let lemma = tracker
        .add_explicit_trust_lemma(vec![term])
        .expect("proof tracking enabled");
    let checkpoint = tracker
        .rollback_checkpoint()
        .expect("small test ledger fits checkpoint budget");

    let alias = tracker
        .add_assumption(term, Some("post_checkpoint_alias".to_string()))
        .expect("certified singleton is reusable");
    assert_eq!(alias, lemma);
    assert_eq!(tracker.num_steps(), 1, "alias adds no proof step");
    assert!(tracker.assumption_map.contains_key(&term));

    assert!(tracker.rollback_to(checkpoint));
    assert_eq!(tracker.num_steps(), 1);
    assert!(!tracker.assumption_map.contains_key(&term));
    assert_internal_id_invariants(&tracker);
}

#[test]
fn test_scope_rollback_pop_removes_new_map_alias_to_old_step() {
    let mut tracker = ProofTracker::new();
    tracker.enable();
    tracker.set_theory("EUF");
    let term = TermId(41);
    tracker
        .add_explicit_trust_lemma(vec![term])
        .expect("proof tracking enabled");
    tracker.push();

    tracker
        .add_assumption(term, Some("scoped_alias".to_string()))
        .expect("certified singleton is reusable");
    assert!(tracker.assumption_map.contains_key(&term));
    assert_eq!(tracker.num_steps(), 1);

    assert!(tracker.pop());
    assert_eq!(tracker.num_steps(), 1);
    assert!(!tracker.assumption_map.contains_key(&term));
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
    tracker.add_explicit_trust_lemma(vec![TermId(20)]); // step 1
    assert_eq!(tracker.num_steps(), 2);

    tracker.push(); // scope 2
    tracker.add_explicit_trust_lemma(vec![TermId(30)]); // step 2
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
    tracker.add_explicit_trust_lemma(vec![TermId(10), TermId(11)]);
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
    tracker.add_explicit_trust_lemma(vec![TermId(20)]);
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
    let a_lemma = tracker.add_explicit_trust_lemma(vec![TermId(100), TermId(101)]);
    assert!(a_lemma.is_some());
    assert_eq!(tracker.num_steps(), 2); // assume + lemma

    // Simulate check-sat producing a proof and taking it
    let proof_1 = tracker.take_proof();
    assert_eq!(proof_1.len(), 2);
    // After take_proof, the tracker starts a coherent empty ledger.

    // --- Pop scope 1 ---
    tracker.pop();
    // Pop remains balanced even though take_proof zeroed the scope watermark.

    // --- Scope 2: assert B (no push needed if this is the outer scope) ---
    // Reset for the new check-sat (as the executor does)
    tracker.reset();

    let b_assumption = tracker.add_assumption(TermId(200), Some("hB".to_string()));
    assert!(b_assumption.is_some());
    let b_lemma = tracker.add_explicit_trust_lemma(vec![TermId(200), TermId(201)]);
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
fn conflict_trace_annotation_matches_recorded_unit_farkas_authority() {
    let mut tracker = ProofTracker::new();
    tracker.enable();
    tracker.set_theory("LIA");

    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let one = terms.mk_int(BigInt::from(1));
    let zero = terms.mk_int(BigInt::from(0));
    let ge = terms.mk_ge(x, one);
    let le = terms.mk_le(x, zero);
    let mut negations = HashMap::default();
    negations.insert(ge, terms.mk_not(ge));
    negations.insert(le, terms.mk_not(le));
    let conflict = vec![TheoryLit::new(ge, true), TheoryLit::new(le, true)];

    let (id, annotation) = record_theory_conflict_unsat_with_annotation(
        &mut tracker,
        Some(&terms),
        &negations,
        &conflict,
    );
    let id = id.expect("recorded conflict");
    let annotation = annotation.expect("materialized conflict annotation");
    let proof = tracker.take_proof();
    let Some(ProofStep::TheoryLemma {
        clause,
        kind,
        farkas,
        lia,
        ..
    }) = proof.get_step(id)
    else {
        panic!("expected theory lemma");
    };
    assert_eq!(annotation.clause, *clause);
    assert_eq!(annotation.kind, *kind);
    assert_eq!(annotation.farkas, *farkas);
    assert_eq!(annotation.lia, *lia);
    assert!(annotation.farkas.is_some());
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
                TheoryLemmaKind::LiaGeneric,
                "an annotation that does not derive contradiction must not gain Farkas authority",
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
