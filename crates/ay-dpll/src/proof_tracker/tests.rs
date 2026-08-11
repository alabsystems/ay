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

#[test]
fn test_normalized_forall_instance_uses_strict_farkas_rewrites() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("normalized_forall_x", Sort::Int);
    let k = terms.mk_var("normalized_forall_k", Sort::Int);
    let n = terms.mk_var("normalized_forall_n", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let cond = terms.mk_var("normalized_forall_cond", Sort::Bool);
    let p_x = terms.mk_app(Symbol::named("normalized_forall_p"), [x], Sort::Bool);
    let q_x = terms.mk_app(Symbol::named("normalized_forall_q"), [x], Sort::Bool);
    let ite_x = terms.mk_ite_raw(cond, p_x, q_x);
    let nonnegative_x = terms.mk_le(zero, x);
    let in_upper_bound_x = terms.mk_lt(x, n);
    let not_nonnegative_x = terms.mk_not_raw(nonnegative_x);
    let not_in_upper_bound_x = terms.mk_not_raw(in_upper_bound_x);
    let authored_body = terms.mk_or(vec![ite_x, not_nonnegative_x, not_in_upper_bound_x]);
    let authored = terms.mk_forall(
        vec![("normalized_forall_x".to_string(), Sort::Int)],
        authored_body,
    );

    let below_zero_x = terms.mk_lt(x, zero);
    let at_or_above_n_x = terms.mk_le(n, x);
    let normalized_body = terms.mk_or(vec![ite_x, below_zero_x, at_or_above_n_x]);
    let normalized = terms.mk_forall(
        vec![("normalized_forall_x".to_string(), Sort::Int)],
        normalized_body,
    );

    let p_k = terms.mk_app(Symbol::named("normalized_forall_p"), [k], Sort::Bool);
    let q_k = terms.mk_app(Symbol::named("normalized_forall_q"), [k], Sort::Bool);
    let ite_k = terms.mk_ite_raw(cond, p_k, q_k);
    let below_zero_k = terms.mk_lt(k, zero);
    let at_or_above_n_k = terms.mk_le(n, k);
    let target = terms.mk_or(vec![ite_k, below_zero_k, at_or_above_n_k]);

    let mut tracker = ProofTracker::new();
    tracker.enable();
    let derived = tracker
        .add_normalized_forall_instantiated_assertion(
            &mut terms,
            authored,
            normalized,
            &[k],
            target,
        )
        .expect("exact NNF arithmetic normalization must have a checked derivation");
    let mut proof = tracker.take_proof();
    assert!(
        matches!(
            proof.get_step(derived),
            Some(ProofStep::Resolution { clause, .. }) if clause == &[target]
        ),
        "tracker must derive the exact E-matching target"
    );
    let not_target = terms.mk_not_raw(target);
    let negated = proof.add_assume(not_target, None);
    proof.add_resolution(Vec::new(), target, derived, negated);
    let quality = ay_proof::check_proof_strict_with_context(
        &proof,
        &terms,
        None,
        None,
        Some(&[authored, not_target]),
    )
    .expect("normalized forall derivation must pass the independent strict checker");
    assert!(quality.is_complete());
    assert_eq!(quality.trust_count, 0);

    fn assert_normalized_forall_rejected(
        terms: &mut TermStore,
        authored: TermId,
        normalized: TermId,
        values: &[TermId],
        target: TermId,
        reason: &str,
    ) {
        let mut tracker = ProofTracker::new();
        tracker.enable();
        assert!(
            tracker
                .add_normalized_forall_instantiated_assertion(
                    terms, authored, normalized, values, target,
                )
                .is_none(),
            "{reason}"
        );
        assert_eq!(
            tracker.num_steps(),
            0,
            "{reason}: rejection must precede proof emission"
        );
    }

    let minus_one = terms.mk_int(BigInt::from(-1));
    let forged_below_minus_one_x = terms.mk_lt(x, minus_one);
    let forged_normalized_body =
        terms.mk_or(vec![ite_x, forged_below_minus_one_x, at_or_above_n_x]);
    let forged_normalized = terms.mk_forall(
        vec![("normalized_forall_x".to_string(), Sort::Int)],
        forged_normalized_body,
    );
    let forged_below_minus_one = terms.mk_lt(k, minus_one);
    let forged_bound = terms.mk_or(vec![ite_k, forged_below_minus_one, at_or_above_n_k]);
    assert_normalized_forall_rejected(
        &mut terms,
        authored,
        forged_normalized,
        &[k],
        forged_bound,
        "a changed arithmetic bound must fail the Farkas gate",
    );

    let forged_eq_zero_x = terms.mk_eq(x, zero);
    let forged_operator_body = terms.mk_or(vec![ite_x, forged_eq_zero_x, at_or_above_n_x]);
    let forged_operator_quantified = terms.mk_forall(
        vec![("normalized_forall_x".to_string(), Sort::Int)],
        forged_operator_body,
    );
    let forged_eq_zero_k = terms.mk_eq(k, zero);
    let forged_operator_target = terms.mk_or(vec![ite_k, forged_eq_zero_k, at_or_above_n_k]);
    assert_normalized_forall_rejected(
        &mut terms,
        authored,
        forged_operator_quantified,
        &[k],
        forged_operator_target,
        "a changed comparison operator must fail the Farkas gate",
    );

    let forged_p_x = terms.mk_app(Symbol::named("normalized_forall_forged_p"), [x], Sort::Bool);
    let forged_ite_x = terms.mk_ite_raw(cond, forged_p_x, q_x);
    let forged_branch_body = terms.mk_or(vec![forged_ite_x, below_zero_x, at_or_above_n_x]);
    let forged_branch_quantified = terms.mk_forall(
        vec![("normalized_forall_x".to_string(), Sort::Int)],
        forged_branch_body,
    );
    let forged_p_k = terms.mk_app(Symbol::named("normalized_forall_forged_p"), [k], Sort::Bool);
    let forged_ite_k = terms.mk_ite_raw(cond, forged_p_k, q_k);
    let forged_branch_target = terms.mk_or(vec![forged_ite_k, below_zero_k, at_or_above_n_k]);
    assert_normalized_forall_rejected(
        &mut terms,
        authored,
        forged_branch_quantified,
        &[k],
        forged_branch_target,
        "a changed Boolean branch must not be admitted as arithmetic normalization",
    );

    assert_normalized_forall_rejected(
        &mut terms,
        authored,
        normalized,
        &[cond],
        target,
        "a wrong-sort positional binding must fail closed",
    );

    let other_p_x = terms.mk_app(
        Symbol::named("normalized_forall_other_source"),
        [x],
        Sort::Bool,
    );
    let other_ite_x = terms.mk_ite_raw(cond, other_p_x, q_x);
    let other_authored_body =
        terms.mk_or(vec![other_ite_x, not_nonnegative_x, not_in_upper_bound_x]);
    let other_authored = terms.mk_forall(
        vec![("normalized_forall_x".to_string(), Sort::Int)],
        other_authored_body,
    );
    assert_normalized_forall_rejected(
        &mut terms,
        other_authored,
        normalized,
        &[k],
        target,
        "a forged authored source mapping must fail exact/Farkas validation",
    );

    let triggered_authored = terms.mk_forall_with_triggers(
        vec![("normalized_forall_x".to_string(), Sort::Int)],
        authored_body,
        vec![vec![p_x]],
    );
    assert_normalized_forall_rejected(
        &mut terms,
        triggered_authored,
        normalized,
        &[k],
        target,
        "source and normalized trigger groups must agree exactly",
    );

    let z = terms.mk_var("normalized_forall_z", Sort::Int);
    let pair_x_z = terms.mk_app(Symbol::named("normalized_forall_pair"), [x, z], Sort::Bool);
    let ordered_authored_body = terms.mk_or(vec![pair_x_z, not_nonnegative_x]);
    let ordered_authored = terms.mk_forall(
        vec![
            ("normalized_forall_x".to_string(), Sort::Int),
            ("normalized_forall_z".to_string(), Sort::Int),
        ],
        ordered_authored_body,
    );
    let ordered_normalized_body = terms.mk_or(vec![pair_x_z, below_zero_x]);
    let ordered_normalized = terms.mk_forall(
        vec![
            ("normalized_forall_x".to_string(), Sort::Int),
            ("normalized_forall_z".to_string(), Sort::Int),
        ],
        ordered_normalized_body,
    );
    let pair_k_n = terms.mk_app(Symbol::named("normalized_forall_pair"), [k, n], Sort::Bool);
    let ordered_target = terms.mk_or(vec![pair_k_n, below_zero_k]);
    assert_normalized_forall_rejected(
        &mut terms,
        ordered_authored,
        ordered_normalized,
        &[n, k],
        ordered_target,
        "same-sort binding values in the wrong positional order must fail closed",
    );

    let short_normalized_body = terms.mk_or(vec![ite_x, below_zero_x]);
    let short_normalized = terms.mk_forall(
        vec![("normalized_forall_x".to_string(), Sort::Int)],
        short_normalized_body,
    );
    let short_target = terms.mk_or(vec![ite_k, below_zero_k]);
    assert_normalized_forall_rejected(
        &mut terms,
        authored,
        short_normalized,
        &[k],
        short_target,
        "a normalized target with changed disjunct arity must fail closed",
    );

    let nonflat_normalized =
        terms.mk_forall(vec![("normalized_forall_x".to_string(), Sort::Int)], p_x);
    assert_normalized_forall_rejected(
        &mut terms,
        authored,
        nonflat_normalized,
        &[k],
        p_k,
        "a non-disjunctive normalized target must fail closed",
    );

    let y = terms.mk_var("normalized_forall_y", Sort::Int);
    let nested_p_y = terms.mk_app(Symbol::named("normalized_forall_nested"), [y], Sort::Bool);
    let nested = terms.mk_forall(
        vec![("normalized_forall_y".to_string(), Sort::Int)],
        nested_p_y,
    );
    let nested_authored_body = terms.mk_or(vec![nested, not_nonnegative_x]);
    let nested_authored = terms.mk_forall(
        vec![("normalized_forall_x".to_string(), Sort::Int)],
        nested_authored_body,
    );
    let nested_normalized_body = terms.mk_or(vec![nested, below_zero_x]);
    let nested_normalized = terms.mk_forall(
        vec![("normalized_forall_x".to_string(), Sort::Int)],
        nested_normalized_body,
    );
    let nested_target = terms.mk_or(vec![nested, below_zero_k]);
    assert_normalized_forall_rejected(
        &mut terms,
        nested_authored,
        nested_normalized,
        &[k],
        nested_target,
        "a nested binder in the authored body must fail closed",
    );
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
        .add_theory_lemma(vec![packed_axiom])
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
    // After take_proof, the tracker starts a coherent empty ledger.

    // --- Pop scope 1 ---
    tracker.pop();
    // Pop remains balanced even though take_proof zeroed the scope watermark.

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
