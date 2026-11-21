// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn duplicate_bindings_remain_invalid_in_both_authority_lanes() {
    let mut fixture = Fixture::new();
    fixture.proof.steps.push(fixture.proof.steps[0].clone());
    assert_invalid(
        fixture.authenticate(&[], &mut |_, _| true),
        "forall source was already bound",
    );
    assert_invalid(
        validate_sko_forall_uniqueness_with_progress(
            &fixture.proof,
            &fixture.terms,
            &mut |_, _| true,
        ),
        "forall source was already bound",
    );
}

#[test]
fn declaration_namespace_collisions_are_not_accepted_as_fresh() {
    let fixture = Fixture::new();
    for role in ["a constructor", "a selector", "a derived tester"] {
        let declarations = HashMap::from_iter([("whole_w".to_string(), role)]);
        let error = authenticate_bundle_skolems_with_progress(
            &fixture.proof,
            &fixture.terms,
            &[],
            &declarations,
            &mut |_, _| true,
        )
        .expect_err("declaration-owned name");
        assert!(
            matches!(error, ProofCheckError::InvalidBooleanRule { ref reason, .. }
            if reason.contains("serialized datatype declaration-owned term namespace") && reason.contains(role) && reason.contains("whole_w"))
        );
    }
}

#[test]
fn full_arena_freshness_includes_unused_application_and_binder_names() {
    for shape in 0..4 {
        let mut fixture = Fixture::new();
        let body = fixture.terms.true_term();
        let data = match shape {
            0 => TermData::App(Symbol::named("whole_w"), vec![]),
            1 => TermData::Let(vec![("whole_w".to_string(), body)], body),
            2 => TermData::Forall(vec![("whole_w".to_string(), Sort::Int)], body, vec![]),
            _ => TermData::Exists(vec![("whole_w".to_string(), Sort::Int)], body, vec![]),
        };
        let mut entries = fixture.terms.entries_snapshot();
        entries.push((data, Sort::Bool));
        fixture.replace_entries(entries);
        assert_invalid(
            fixture.authenticate(&[], &mut |_, _| true),
            "not globally fresh",
        );
    }
}

#[test]
fn problem_assertions_and_authored_assumptions_both_forbid_witness_mentions() {
    let mut fixture = Fixture::new();
    let pinned = fixture
        .terms
        .mk_app(Symbol::named("pin_witness"), [fixture.witness], Sort::Bool);
    assert_invalid(
        fixture.authenticate(&[pinned], &mut |_, _| true),
        "claimed problem obligation or an Assume step",
    );
    fixture.proof.add_assume(pinned, None);
    assert_invalid(
        fixture.authenticate(&[], &mut |_, _| true),
        "claimed problem obligation or an Assume step",
    );
}

#[test]
fn registered_freshness_checks_the_complete_raw_original_scope() {
    let mut fixture = Fixture::new();
    let original = fixture.terms.mk_not_raw(fixture.source);
    let raw_true = fixture.terms.mk_app(
        Symbol::named("="),
        [fixture.witness, fixture.witness],
        Sort::Bool,
    );
    assert_ne!(raw_true, fixture.terms.true_term());
    let check = |roots: &[TermId], progress: &mut dyn FnMut(usize, usize) -> bool| {
        validate_registered_skolem_source_scope_with_progress(
            &fixture.proof,
            &fixture.terms,
            roots,
            progress,
        )
    };
    check(&[original], &mut |_, _| true).expect("genuinely fresh registered choice");
    for roots in [vec![original, raw_true], vec![raw_true, original, raw_true]] {
        assert_invalid(
            check(&roots, &mut |_, _| true),
            "claimed problem obligation or an Assume step",
        );
    }

    // The live full-scope wrapper shares every walk/copy debit with its
    // caller, including the entry and final fences; cancellation never grants
    // freshness for a checked prefix of the original roots.
    let mut calls = 0usize;
    check(&[original], &mut |_, _| {
        calls += 1;
        true
    })
    .unwrap();
    for stop_at in 1..=calls {
        let mut current = 0usize;
        assert_resource(check(&[original], &mut |_, _| {
            current += 1;
            current < stop_at
        }));
        assert_eq!(current, stop_at);
    }
}

#[test]
fn cyclic_choice_dependencies_remain_rejected_after_exact_substitution() {
    let mut fixture = Fixture::new();
    fixture.add_dependent(true);
    // Each step separately has a fresh witness and exact substitution; only
    // the whole-proof dependency graph detects the mutually recursive choices.
    validate_sko_forall_uniqueness_with_progress(&fixture.proof, &fixture.terms, &mut |_, _| true)
        .expect("locally exact bijection");
    assert_invalid(
        fixture.authenticate(&[], &mut |_, _| true),
        "cyclic choice dependency",
    );
}

#[test]
fn trigger_only_witness_mentions_still_violate_problem_freshness() {
    let mut fixture = Fixture::new();
    let mut entries = fixture.terms.entries_snapshot();
    let root = TermId::new(entries.len() as u32);
    entries.push((
        TermData::Forall(
            vec![("trigger_bound".to_string(), Sort::Int)],
            fixture.terms.true_term(),
            vec![vec![], vec![fixture.witness]],
        ),
        Sort::Bool,
    ));
    fixture.replace_entries(entries);
    assert_invalid(
        fixture.authenticate(&[root], &mut |_, _| true),
        "claimed problem obligation or an Assume step",
    );
}
