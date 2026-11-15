// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::incremental_state::IncrementalSubsystem;
use crate::proof_tracker::ProofTracker;
use ay_core::{ProofStep, TheoryLemmaKind};

#[test]
fn packed_separation_has_a_strict_proof_without_generated_assumptions() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let clause = separation_clause(&mut terms, a, b);
    assert!(ay_core::proof_validation::recognize_int_guarded_split_gap(
        &terms, &clause
    ));
    let packed = terms.mk_app(Symbol::named("or"), clause.clone(), Sort::Bool);
    let mut tracker = ProofTracker::new();
    tracker.enable();
    let unit = tracker
        .add_packed_guarded_integer_lemma(&mut terms, packed, clause.clone())
        .expect("checked packed proof");
    assert_eq!(tracker.add_assumption(packed, None), Some(unit));
    assert_eq!(
        tracker.add_packed_guarded_integer_lemma(&mut terms, packed, clause),
        Some(unit)
    );
    let mut proof = tracker.take_proof();
    assert!(!proof
        .steps
        .iter()
        .any(|step| matches!(step, ProofStep::Assume(_))));
    assert!(proof.steps.iter().any(|step| matches!(
        step,
        ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::IntGuardedSplitGap,
            ..
        }
    )));
    let negated = terms.mk_not_raw(packed);
    let premise = proof.add_assume(negated, None);
    proof.add_resolution(Vec::new(), packed, unit, premise);
    let quality =
        ay_proof::check_proof_strict_with_context(&proof, &terms, None, None, Some(&[negated]))
            .expect("strict checked refutation");
    assert_eq!(quality.trust_count, 0);
    assert_eq!(quality.hole_count, 0);
}

#[test]
fn real_and_gap_two_labels_are_rejected_without_partial_proofs() {
    for (sort, gap) in [(Sort::Real, 1_i64), (Sort::Int, 2_i64)] {
        let mut terms = TermStore::new();
        let a = terms.mk_var("a", sort.clone());
        let b = terms.mk_var("b", sort.clone());
        let equality = terms.mk_eq(a, b);
        let step = if sort == Sort::Real {
            terms.mk_rational(num_rational::BigRational::from_integer(gap.into()))
        } else {
            terms.mk_int(gap.into())
        };
        let next_a = terms.mk_add(vec![a, step]);
        let next_b = terms.mk_add(vec![b, step]);
        let forward = terms.mk_le(next_a, b);
        let reverse = terms.mk_le(next_b, a);
        let clause = vec![equality, forward, reverse];
        assert!(!ay_core::proof_validation::recognize_int_guarded_split_gap(
            &terms, &clause
        ));
        let packed = terms.mk_app(Symbol::named("or"), clause.clone(), Sort::Bool);
        let mut tracker = ProofTracker::new();
        tracker.enable();
        assert!(tracker
            .add_packed_guarded_integer_lemma(&mut terms, packed, clause)
            .is_none());
        assert!(tracker.take_proof().steps.is_empty());
    }
}

#[test]
fn current_inventory_is_bounded_ground_and_integer_only() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let c = terms.mk_var("unused", Sort::Int);
    let current = terms.mk_eq(a, b);
    let _unreachable = terms.mk_eq(a, c);
    assert_eq!(
        equality_pairs(&terms, &[current], 100, &|| false),
        Some(vec![(a, b)])
    );
    assert!(equality_pairs(&terms, &[current], 1, &|| false).is_none());
    assert!(equality_pairs(&terms, &[current], 100, &|| true).is_none());
    let real_a = terms.mk_var("real_a", Sort::Real);
    let real_b = terms.mk_var("real_b", Sort::Real);
    let real_eq = terms.mk_eq(real_a, real_b);
    assert_eq!(
        equality_pairs(&terms, &[real_eq], 100, &|| false),
        Some(Vec::new())
    );
    let quantified = terms.mk_forall(vec![("a".to_string(), Sort::Int)], current);
    assert!(equality_pairs(&terms, &[quantified], 100, &|| false).is_none());
    let zero = terms.mk_int(0.into());
    let bound = terms.mk_let(vec![("a".to_string(), zero)], current);
    assert!(equality_pairs(&terms, &[bound], 100, &|| false).is_none());
    let wide = terms.mk_app(Symbol::named("or"), vec![current; 101], Sort::Bool);
    assert!(equality_pairs(&terms, &[wide], 100, &|| false).is_none());
}

#[test]
fn outer_packed_alias_survives_nested_proof_scopes() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let c = terms.mk_var("c", Sort::Int);
    let outer_clause = separation_clause(&mut terms, a, b);
    let outer = terms.mk_app(Symbol::named("or"), outer_clause.clone(), Sort::Bool);
    let inner_clause = separation_clause(&mut terms, a, c);
    let inner = terms.mk_app(Symbol::named("or"), inner_clause.clone(), Sort::Bool);
    let mut tracker = ProofTracker::new();
    tracker.enable();
    let outer_unit = tracker
        .add_packed_guarded_integer_lemma(&mut terms, outer, outer_clause.clone())
        .expect("outer proof");
    let outer_steps = tracker.num_steps();
    tracker.push();
    tracker
        .add_packed_guarded_integer_lemma(&mut terms, inner, inner_clause.clone())
        .expect("inner proof");
    tracker.push();
    assert_eq!(
        tracker.add_packed_guarded_integer_lemma(&mut terms, outer, outer_clause),
        Some(outer_unit)
    );
    assert!(tracker.pop());
    assert!(tracker.pop());
    assert_eq!(tracker.num_steps(), outer_steps);
    assert_eq!(tracker.add_assumption(outer, None), Some(outer_unit));
    assert_eq!(tracker.num_steps(), outer_steps);
    tracker
        .add_packed_guarded_integer_lemma(&mut terms, inner, inner_clause)
        .expect("fresh inner proof");
    assert!(tracker.num_steps() > outer_steps);
}

#[test]
fn emitter_caps_and_deduplicates_without_changing_authored_roots() {
    let mut executor = Executor::new();
    executor.proof_tracker.enable();
    let a = executor.ctx.terms.mk_var("a", Sort::Int);
    let b = executor.ctx.terms.mk_var("b", Sort::Int);
    let c = executor.ctx.terms.mk_var("c", Sort::Int);
    let ab = executor.ctx.terms.mk_eq(a, b);
    let ac = executor.ctx.terms.mk_eq(a, c);
    executor.ctx.assertions = vec![ab, ac];
    let original = executor.ctx.assertions.clone();
    executor.proof_problem_assertion_provenance = Some(
        super::super::solve_harness::ProofProblemAssertionProvenance::passthrough(
            &original, &original,
        ),
    );
    assert_eq!(executor.add_ground_integer_separation(0), 0);
    assert_eq!(executor.add_ground_integer_separation(1), 1);
    assert_eq!(executor.add_ground_integer_separation(1), 0);
    assert_eq!(executor.add_ground_integer_separation(10), 1);
    assert_eq!(executor.add_ground_integer_separation(10), 0);
    assert_eq!(executor.ctx.assertions.len(), 4);
    assert_eq!(
        executor
            .proof_problem_assertion_provenance
            .as_ref()
            .expect("authored authority")
            .original_problem_assertions,
        original
    );
}

#[test]
fn absent_authority_declines_without_authorizing_the_working_window() {
    let mut executor = Executor::new();
    let a = executor.ctx.terms.mk_var("a", Sort::Int);
    let b = executor.ctx.terms.mk_var("b", Sort::Int);
    let equality = executor.ctx.terms.mk_eq(a, b);
    executor.ctx.assertions = vec![equality];
    assert!(executor.proof_problem_assertion_provenance.is_none());
    assert_eq!(executor.add_ground_integer_separation(1), 0);
    assert_eq!(executor.ctx.assertions, vec![equality]);
    assert!(executor.proof_problem_assertion_provenance.is_none());
}

#[test]
fn original_shared_ite_declines_even_after_working_terms_are_named() {
    let mut executor = Executor::new();
    let terms = &mut executor.ctx.terms;
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let condition = terms.mk_var("condition", Sort::Bool);
    let equality = terms.mk_eq(a, b);
    let ite = terms.mk_ite(condition, a, b);
    let call = terms.mk_app(Symbol::named("f"), [ite], Sort::Int);
    let shared = terms.mk_eq(call, b);
    let original = [equality, shared];
    executor.proof_problem_assertion_provenance = Some(
        super::super::solve_harness::ProofProblemAssertionProvenance::passthrough(
            &original, &original,
        ),
    );
    executor.ctx.assertions = vec![equality];
    assert_eq!(executor.add_ground_integer_separation(10), 0);
    assert_eq!(executor.ctx.assertions, vec![equality]);
}
