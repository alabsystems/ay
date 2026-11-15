// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Solver-free checks of source-projected scalar equality refutations.

use super::derive;
use crate::executor::Executor;
use ay_core::{AletheRule, Proof, ProofId, ProofStep, Sort, Symbol, TermId, TermStore};

mod fixtures;
use fixtures::{app, assert_refutation, wide, Chain};

// The same crate-local source as the public production-path regression.
const WIDE: &str = include_str!(
    "../../theories/bv/structural_preprocess/tests/native_wide_array_diamond_sat.smt2"
);

#[test]
fn original_wide_diamond_equal_fact_choices_refute_without_array_reasoning() {
    for choices in [
        ["__tree_ind_1", "__tree_ind_4"],
        ["__tree_ind_2", "__tree_ind_5"],
    ] {
        let mut executor = wide(&choices);
        let originals = executor.ctx.assertions.clone();
        let proof = derive(&mut executor.ctx.terms, &originals, &mut |_, _| true)
            .expect("equal selected scalar facts contradict the original disequality");
        assert_refutation(&executor.ctx.terms, &originals, &proof);
        assert_eq!(executor.ctx.assertions, originals);
        assert!(executor.last_result().is_none(), "no solver was invoked");
    }
}

#[test]
fn missing_and_opposite_wide_fact_choices_never_refute_satisfiable_originals() {
    for choices in [
        Vec::new(),
        vec!["__tree_ind_1"],
        vec!["__tree_ind_4"],
        vec!["__tree_ind_1", "__tree_ind_5"],
        vec!["__tree_ind_2", "__tree_ind_4"],
    ] {
        let mut executor = wide(&choices);
        let originals = executor.ctx.assertions.clone();
        assert!(derive(&mut executor.ctx.terms, &originals, &mut |_, _| true).is_none());
        assert_eq!(executor.ctx.assertions, originals);
    }
}

#[test]
fn reversed_duplicate_aliases_and_nested_conjunct_paths_retain_original_authority() {
    let mut fixture = Chain::new();
    fixture.roots.insert(0, fixture.source);
    fixture.roots.push(fixture.guard);
    let proof = derive(&mut fixture.terms, &fixture.roots, &mut |_, _| true).unwrap();
    assert_refutation(&fixture.terms, &fixture.roots, &proof);
    // The projected equalities are absent as roots: they cannot become Assumes.
    assert!(fixture
        .edges
        .iter()
        .all(|edge| !fixture.roots.contains(edge)));
}

#[test]
fn shared_body_wrong_guard_and_disjunctive_activation_do_not_license_edges() {
    let mut fixture = Chain::new();
    let negated = fixture.terms.mk_not_raw(fixture.other_guard);
    let wrong_source = app(&mut fixture.terms, "or", &[negated, fixture.body]);
    let roots = [wrong_source, fixture.guard, fixture.goal];
    assert!(derive(&mut fixture.terms, &roots, &mut |_, _| true).is_none());
    let disjunction = app(
        &mut fixture.terms,
        "or",
        &[fixture.guard, fixture.other_guard],
    );
    let roots = [fixture.source, disjunction, fixture.goal];
    assert!(derive(&mut fixture.terms, &roots, &mut |_, _| true).is_none());
    let proof = derive(&mut fixture.terms, &fixture.roots, &mut |_, _| true).unwrap();
    assert_refutation(&fixture.terms, &fixture.roots, &proof);
}

#[test]
fn missing_original_activation_and_mutated_proof_fail_independent_authentication() {
    let mut fixture = Chain::new();
    let proof = derive(&mut fixture.terms, &fixture.roots, &mut |_, _| true).unwrap();
    let missing = [fixture.source, fixture.goal];
    assert!(derive(&mut fixture.terms, &missing, &mut |_, _| true).is_none());
    let authenticate = |candidate: &Proof, roots: &[TermId]| {
        ay_proof::authenticate_premise_clauses_strict_with_context_and_progress(
            candidate,
            &fixture.terms,
            None,
            None,
            roots,
            &mut |_, _| true,
        )
        .is_ok()
    };
    assert!(!authenticate(&proof, &missing));
    let mut wrong_assume = proof.clone();
    let assumption = wrong_assume
        .steps
        .iter_mut()
        .find(|step| matches!(step, ProofStep::Assume(term) if *term == fixture.guard))
        .expect("activated projection must actually use its original guard");
    *assumption = ProofStep::Assume(fixture.other_guard);
    assert!(!authenticate(&wrong_assume, &fixture.roots));
    let mut trusted = proof;
    *trusted.steps.last_mut().unwrap() = ProofStep::Step {
        rule: AletheRule::Trust,
        clause: Vec::new(),
        premises: Vec::new(),
        args: Vec::new(),
    };
    assert!(!authenticate(&trusted, &fixture.roots));
    assert!(ay_proof::check_proof_strict(&trusted, &fixture.terms).is_err());
}

#[test]
fn array_congruence_and_malformed_bitvector_edges_are_not_scalar_graph_edges() {
    let mut terms = TermStore::new();
    let value = terms.mk_bitvec(0.into(), 129);
    let base = terms.mk_const_array(Sort::Bool, value);
    let array_sort = terms.sort(base).clone();
    let left = terms.mk_var("left array", array_sort.clone());
    let right = terms.mk_var("right array", array_sort);
    let key = terms.false_term();
    let left_read = terms.mk_app(Symbol::named("select"), [left, key], Sort::bitvec(129));
    let right_read = terms.mk_app(Symbol::named("select"), [right, key], Sort::bitvec(129));
    let equal_arrays = app(&mut terms, "=", &[left, right]);
    let equal_reads = app(&mut terms, "=", &[left_read, right_read]);
    let unequal_reads = terms.mk_not_raw(equal_reads);
    assert!(derive(&mut terms, &[equal_arrays, unequal_reads], &mut |_, _| true).is_none());

    let mut fixture = Chain::new();
    let narrow = fixture.terms.mk_var("wrong width", Sort::bitvec(128));
    let first = app(&mut fixture.terms, "=", &[fixture.vars[0], narrow]);
    let second = app(&mut fixture.terms, "=", &[narrow, fixture.vars[2]]);
    assert!(derive(
        &mut fixture.terms,
        &[first, second, fixture.goal],
        &mut |_, _| true
    )
    .is_none());
}

#[test]
fn shared_work_and_byte_boundaries_are_exact_and_fresh_attempts_recover() {
    let mut measured = Chain::new();
    let mut used = (0usize, 0usize);
    let proof = derive(&mut measured.terms, &measured.roots, &mut |work, bytes| {
        used.0 = used.0.checked_add(work).unwrap();
        used.1 = used.1.checked_add(bytes).unwrap();
        true
    })
    .unwrap();
    assert_refutation(&measured.terms, &measured.roots, &proof);
    assert!(used.0 > 0 && used.1 > 0);
    for (work_limit, byte_limit, admitted) in [
        (used.0, used.1, true),
        (used.0 - 1, used.1, false),
        (used.0, used.1 - 1, false),
        (0, used.1, false),
        (used.0, 0, false),
    ] {
        let mut fixture = Chain::new();
        let mut work_left = work_limit;
        let mut bytes_left = byte_limit;
        let proof = derive(&mut fixture.terms, &fixture.roots, &mut |work, bytes| {
            let Some(next_work) = work_left.checked_sub(work) else {
                return false;
            };
            let Some(next_bytes) = bytes_left.checked_sub(bytes) else {
                return false;
            };
            work_left = next_work;
            bytes_left = next_bytes;
            true
        });
        assert_eq!(proof.is_some(), admitted);
        if let Some(proof) = proof {
            assert_eq!((work_left, bytes_left), (0, 0));
            assert_refutation(&fixture.terms, &fixture.roots, &proof);
        }
    }
    let mut fresh = Chain::new();
    let proof = derive(&mut fresh.terms, &fresh.roots, &mut |_, _| true).unwrap();
    assert_refutation(&fresh.terms, &fresh.roots, &proof);
}

#[test]
fn final_publication_poll_can_withhold_the_entire_refutation() {
    let mut fixture = Chain::new();
    let mut calls = 0usize;
    let mut last = None;
    assert!(
        derive(&mut fixture.terms, &fixture.roots, &mut |work, bytes| {
            calls = calls.checked_add(1).unwrap();
            assert!(calls < 100_000, "the tiny fixture must stay bounded");
            last = Some((work, bytes));
            true
        })
        .is_some()
    );
    assert_eq!(last, Some((0, 0)));
    let mut retry = Chain::new();
    let mut current = 0;
    assert!(derive(&mut retry.terms, &retry.roots, &mut |_, _| {
        current += 1;
        current < calls
    })
    .is_none());
    assert_eq!(
        current, calls,
        "refusal reaches the final publication boundary"
    );
}
