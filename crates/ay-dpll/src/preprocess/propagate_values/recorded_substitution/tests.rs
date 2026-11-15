// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use std::sync::atomic::{AtomicBool, Ordering};

mod fixtures;
use fixtures::*;

#[test]
fn exact_array_substitution_records_replay_without_authoring_the_rewritten_root() {
    let mut terms = TermStore::new();
    let mut roots = array_roots(&mut terms);
    let original = roots.clone();
    let mut sources: Vec<_> = original.iter().map(|&root| vec![root]).collect();
    let (mut pass, _, propagation) = wrapper(Box::new(|_, _| true));
    assert!(pass.apply_with_sources(&mut terms, &mut roots, &mut sources));
    assert_eq!(
        sources,
        original.iter().map(|&root| vec![root]).collect::<Vec<_>>()
    );
    assert_ne!(roots[1], original[1]);
    let records = propagation
        .lock()
        .unwrap()
        .take_propagation_records()
        .unwrap();
    assert_eq!(records.entries.len(), 1);
    assert_eq!(records.entries[0].source_assertion, original[0]);
    let (proof, conclusion) = replay(&mut terms, &original, &records, roots[1]).unwrap();
    assert!(authenticated(
        &terms, &original, &proof, conclusion, roots[1]
    ));
    assert!(!proof.steps.iter().any(|step| matches!(step,
        ay_core::ProofStep::Assume(term) if *term == roots[1])));
    assert!(!authenticated(
        &terms,
        &original[1..],
        &proof,
        conclusion,
        roots[1]
    ));
}

#[test]
fn shared_stamps_preserve_every_round_across_changed_assertion_lengths() {
    let mut terms = TermStore::new();
    let y = terms.mk_var("earlier y", Sort::bitvec(8));
    let x = terms.mk_var("later x", Sort::bitvec(8));
    let z = terms.mk_var("z", Sort::bitvec(8));
    let seven = terms.mk_bitvec(7.into(), 8);
    let alias = eq(&mut terms, x, y);
    let value = eq(&mut terms, y, seven);
    let query = terms.mk_app(Symbol::named("bvult"), [x, z], Sort::Bool);
    let truth = terms.true_term();
    let nested = terms.mk_app(Symbol::named("and"), [value, truth], Sort::Bool);
    let originals = vec![alias, query, nested];
    let mut roots = originals.clone();
    let (mut pass, _, propagation) = wrapper(Box::new(|_, _| true));
    propagation.lock().unwrap().apply(&mut terms, &mut roots);
    assert!(pass.apply(&mut terms, &mut roots));
    let intermediate = roots[1];
    pass.reset();
    // A different pass legitimately changes cardinality BETWEEN snapshots.
    roots.pop();
    roots.extend([value, truth]);
    propagation.lock().unwrap().reset();
    propagation.lock().unwrap().apply(&mut terms, &mut roots);
    assert!(pass.apply(&mut terms, &mut roots));
    let target = roots[1];
    assert_ne!(intermediate, target);
    let records = propagation
        .lock()
        .unwrap()
        .take_propagation_records()
        .unwrap();
    assert!(records
        .rewrites
        .iter()
        .any(|r| r.before == query && r.after == intermediate && r.stamp == 2));
    assert!(records
        .rewrites
        .iter()
        .any(|r| r.before == intermediate && r.after == target && r.stamp == 4));
    assert!(records
        .rewrites
        .iter()
        .any(|r| r.before == value && r.after == truth && r.stamp == 4));
    let (proof, conclusion) = replay(&mut terms, &originals, &records, target).unwrap();
    assert!(authenticated(
        &terms, &originals, &proof, conclusion, target
    ));
}

#[test]
fn recording_cancellation_never_changes_the_delegate_or_publishes_partial_hints() {
    for stop in [0, 1, 3] {
        let mut terms = TermStore::new();
        let original = array_roots(&mut terms);
        let mut expected = original.clone();
        let mut plain = VariableSubstitution::new();
        let changed = plain.apply(&mut terms, &mut expected);
        let mut calls = 0;
        let (mut pass, _, propagation) = wrapper(Box::new(move |_, _| {
            calls += 1;
            calls <= stop
        }));
        let mut actual = original;
        assert_eq!(pass.apply(&mut terms, &mut actual), changed);
        assert_eq!(actual, expected);
        assert!(propagation
            .lock()
            .unwrap()
            .take_propagation_records()
            .is_none());
        pass.reset();
        assert!(propagation.lock().unwrap().records_overflowed);
    }
}

#[test]
fn relevant_unsupported_ite_license_withholds_all_but_unused_old_entry_does_not() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("unsupported x", Sort::bitvec(8));
    let condition = terms.mk_var("condition", Sort::Bool);
    let one = terms.mk_bitvec(1.into(), 8);
    let two = terms.mk_bitvec(2.into(), 8);
    let yes = eq(&mut terms, x, one);
    let no = eq(&mut terms, x, two);
    let source = terms.mk_ite_raw(condition, yes, no);
    let query = terms.mk_app(Symbol::named("bvult"), [x, two], Sort::Bool);
    let (mut pass, _, propagation) = wrapper(Box::new(|_, _| true));
    let mut active = vec![source, query];
    assert!(pass.apply(&mut terms, &mut active));
    assert!(propagation
        .lock()
        .unwrap()
        .take_propagation_records()
        .is_none());

    let (mut pass, substitution, propagation) = wrapper(Box::new(|_, _| true));
    let mut earlier = vec![source, query];
    assert!(substitution.lock().unwrap().apply(&mut terms, &mut earlier));
    pass.reset();
    let mut independent = array_roots(&mut terms);
    assert!(pass.apply(&mut terms, &mut independent));
    let records = propagation
        .lock()
        .unwrap()
        .take_propagation_records()
        .unwrap();
    assert!(records.entries.iter().all(|entry| entry.expr != x));
    assert_eq!(records.entries.len(), 1);
}

#[test]
fn per_round_length_mismatch_and_stamp_overflow_refuse_records() {
    let mut terms = TermStore::new();
    let original = array_roots(&mut terms);
    let mut after = original.clone();
    let mut substitution = VariableSubstitution::new();
    substitution.apply(&mut terms, &mut after);
    assert!(records::round(
        &terms,
        &original,
        &after[..1],
        &substitution,
        1,
        &mut |_, _| true
    )
    .is_none());
    let (mut pass, _, propagation) = wrapper(Box::new(|_, _| true));
    propagation.lock().unwrap().apply_calls = u32::MAX;
    let mut actual = original;
    assert!(pass.apply(&mut terms, &mut actual));
    assert_eq!(actual, after);
    assert!(propagation
        .lock()
        .unwrap()
        .take_propagation_records()
        .is_none());
}

#[test]
fn post_delegate_refusal_is_sticky_but_a_fresh_accumulator_can_record() {
    let mut terms = TermStore::new();
    let originals = array_roots(&mut terms);
    let cancelled = Arc::new(AtomicBool::new(false));
    let observed = Arc::clone(&cancelled);
    let (mut pass, _, propagation) =
        wrapper(Box::new(move |_, _| !observed.load(Ordering::Relaxed)));
    let mut roots = originals.clone();
    let changed = pass.apply_recorded(&mut terms, &mut roots, |pass, terms, roots| {
        let changed = pass.apply(terms, roots);
        cancelled.store(true, Ordering::Relaxed);
        changed
    });
    assert!(changed);
    cancelled.store(false, Ordering::Relaxed);
    assert!(propagation
        .lock()
        .unwrap()
        .take_propagation_records()
        .is_none());
    assert!(propagation.lock().unwrap().records_overflowed);
    let (mut fresh, _, propagation) = wrapper(Box::new(|_, _| true));
    let mut roots = originals;
    assert!(fresh.apply(&mut terms, &mut roots));
    assert!(propagation
        .lock()
        .unwrap()
        .take_propagation_records()
        .is_some());
}
