// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn actual_pass_canonicalizes_changed_and_without_rewriting_untouched_nodes() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let q = terms.mk_var("q", Sort::Bool);
    let r = terms.mk_var("r", Sort::Bool);
    let truth = terms.true_term();
    let falsity = terms.false_term();
    let license = terms.mk_eq(q, p);
    // Raw input is deliberate: substitution must both sort the survivors and
    // remove the duplicate and true, not merely preserve positional children.
    let before = terms.mk_app(Symbol::named("and"), [r, q, p, truth], Sort::Bool);
    let false_branch = terms.mk_app(Symbol::named("and"), [q, falsity], Sort::Bool);
    let untouched = terms.mk_app(Symbol::named("and"), [r, p, truth], Sort::Bool);
    let expected = terms.mk_and(vec![p, r]);
    let raw_after = terms.mk_app(Symbol::named("and"), [r, p, p, truth], Sort::Bool);
    assert_ne!(raw_after, expected);
    let mut roots = vec![license, before, false_branch, untouched];
    let mut pass = VariableSubstitution::new();

    assert!(pass.apply(&mut terms, &mut roots));
    assert_eq!(pass.substitutions().get(&q), Some(&p));
    assert_eq!(pass.substitution_sources().get(&q), Some(&license));
    assert_eq!(roots, vec![truth, expected, falsity, untouched]);
    assert!(!pass.apply(&mut terms, &mut roots));
    assert_eq!(roots[1], expected);
}

#[test]
fn actual_pass_canonicalizes_or_false_true_and_complement_survivors() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let q = terms.mk_var("q", Sort::Bool);
    let r = terms.mk_var("r", Sort::Bool);
    let truth = terms.true_term();
    let falsity = terms.false_term();
    let not_p = terms.mk_not(p);
    let license = terms.mk_eq(q, p);
    let reordered = terms.mk_app(Symbol::named("or"), [r, q, p, falsity], Sort::Bool);
    let singleton = terms.mk_app(Symbol::named("or"), [q, falsity], Sort::Bool);
    let absorbing = terms.mk_app(Symbol::named("or"), [q, truth], Sort::Bool);
    let complement = terms.mk_app(Symbol::named("or"), [q, not_p], Sort::Bool);
    let expected = terms.mk_or(vec![p, r]);
    let mut roots = vec![license, reordered, singleton, absorbing, complement];
    let mut pass = VariableSubstitution::new();

    assert!(pass.apply(&mut terms, &mut roots));
    assert_eq!(pass.substitutions().get(&q), Some(&p));
    assert_eq!(roots, vec![truth, expected, p, truth, truth]);
}

#[test]
fn actual_pass_leaves_non_bool_connectives_raw_after_substitution() {
    for name in ["and", "or"] {
        let mut terms = TermStore::new();
        let p = terms.mk_var("p", Sort::Bool);
        let q = terms.mk_var("q", Sort::Bool);
        let x = terms.mk_var("x", Sort::Int);
        let zero = terms.mk_int(0.into());
        let bool_license = terms.mk_eq(q, p);
        let int_license = terms.mk_eq(x, zero);
        // Native malformed terms are kept raw. The pass must neither invoke a
        // Bool constructor on Int children nor change a non-Bool result sort.
        let bad_operand = terms.mk_app(Symbol::named(name), [x, q], Sort::Bool);
        let bad_result = terms.mk_app(Symbol::named(name), [q, p], Sort::Int);
        let expected_operand = terms.mk_app(Symbol::named(name), [zero, p], Sort::Bool);
        let expected_result = terms.mk_app(Symbol::named(name), [p, p], Sort::Int);
        let mut roots = vec![bool_license, int_license, bad_operand, bad_result];
        let mut pass = VariableSubstitution::new();

        assert!(pass.apply(&mut terms, &mut roots));
        assert_eq!(pass.substitutions().get(&q), Some(&p));
        assert_eq!(pass.substitutions().get(&x), Some(&zero));
        assert_ne!(roots[2], bad_operand);
        assert_ne!(roots[3], bad_result);
        assert_eq!(roots[2], expected_operand);
        assert_eq!(roots[3], expected_result);
        assert_eq!(terms.sort(roots[2]), &Sort::Bool);
        assert_eq!(terms.sort(roots[3]), &Sort::Int);
    }
}

#[test]
fn recorded_canonical_image_preserves_authored_source_sets_and_license() {
    use crate::preprocess::propagate_values::{PropagateValues, RecordedVariableSubstitution};
    use std::sync::{Arc, Mutex};

    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let q = terms.mk_var("q", Sort::Bool);
    let r = terms.mk_var("r", Sort::Bool);
    let truth = terms.true_term();
    let license = terms.mk_eq(q, p);
    let before = terms.mk_app(Symbol::named("and"), [r, q, p, truth], Sort::Bool);
    let untouched = terms.mk_or(vec![p, r]);
    let expected = terms.mk_and(vec![p, r]);
    let mut roots = vec![license, before, untouched];
    // Preserve caller-owned grouping, order and duplicates, not merely a set
    // of the new roots. Recording a canonical image must not author that image.
    let original_sources = vec![
        vec![license],
        vec![before, license, before],
        vec![untouched],
    ];
    let mut sources = original_sources.clone();
    let substitution = Arc::new(Mutex::new(VariableSubstitution::new()));
    let propagation = Arc::new(Mutex::new(PropagateValues::new()));
    let mut pass = RecordedVariableSubstitution::new(
        Arc::clone(&substitution),
        Arc::clone(&propagation),
        Box::new(|_, _| true),
    );

    assert!(pass.apply_with_sources(&mut terms, &mut roots, &mut sources));
    assert_eq!(roots, vec![truth, expected, untouched]);
    assert_eq!(sources, original_sources);
    assert!(!sources.iter().flatten().any(|&source| source == expected));
    let records = propagation
        .lock()
        .unwrap()
        .take_propagation_records()
        .expect("complete actual-pass recording");
    assert_eq!(records.entries.len(), 1);
    assert_eq!(records.entries[0].expr, q);
    assert_eq!(records.entries[0].source_assertion, license);
    assert!(records
        .rewrites
        .iter()
        .any(|record| record.before == before && record.after == expected));
    let TermData::App(symbol, children) = terms.get(before) else {
        panic!("original authored AND must remain available");
    };
    assert_eq!(symbol.name(), "and");
    assert_eq!(children.as_slice(), &[r, q, p, truth]);
    assert_eq!(
        substitution.lock().unwrap().substitution_sources().get(&q),
        Some(&license)
    );
}
