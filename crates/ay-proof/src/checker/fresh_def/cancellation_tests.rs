// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![cfg(test)]

use ay_core::{Sort, Symbol};

use super::*;

mod fixtures;
mod oracle;

use fixtures::Fixture;

fn summary(registry: FreshDefRegistry) -> Vec<(String, TermId, ProofId)> {
    let mut entries: Vec<_> = registry
        .bindings
        .into_iter()
        .map(|(name, binding)| (name, binding.definiens, binding.step))
        .collect();
    entries.sort_by(|left, right| left.0.cmp(&right.0));
    entries
}

fn compare(fixture: &Fixture, assertions: Option<&[TermId]>) -> Result<usize, ProofCheckError> {
    let expected = oracle::collect(&fixture.proof, &fixture.terms, assertions).map(summary);
    let actual = FreshDefRegistry::collect_with_progress(
        &fixture.proof,
        &fixture.terms,
        assertions,
        &mut |work, bytes| {
            assert_eq!(
                (work, bytes),
                (0, 0),
                "cancellation does not invent charges"
            );
            true
        },
    )
    .map(summary);
    assert_eq!(actual, expected);
    assert_eq!(
        FreshDefRegistry::collect(&fixture.proof, &fixture.terms, assertions).map(summary),
        expected,
    );
    actual.map(|entries| entries.len())
}

fn every_refusal(fixture: &Fixture) {
    let before =
        serde_json::to_vec(&(&fixture.proof.steps, fixture.terms.entries_snapshot())).unwrap();
    let mut total = 0;
    let live = FreshDefRegistry::collect_with_progress(
        &fixture.proof,
        &fixture.terms,
        Some(&fixture.assertions),
        &mut |_, _| {
            total += 1;
            true
        },
    )
    .map(summary);
    for stop in 1..=total {
        let mut calls = 0;
        let result = FreshDefRegistry::collect_with_progress(
            &fixture.proof,
            &fixture.terms,
            Some(&fixture.assertions),
            &mut |_, _| {
                calls += 1;
                calls != stop
            },
        );
        assert!(
            matches!(result, Err(ProofCheckError::ResourceLimit)),
            "{stop}"
        );
        assert_eq!(
            calls, stop,
            "false is terminal even if a later poll would return true"
        );
    }
    assert_eq!(
        FreshDefRegistry::collect(&fixture.proof, &fixture.terms, Some(&fixture.assertions))
            .map(summary),
        live,
    );
    assert_eq!(
        serde_json::to_vec(&(&fixture.proof.steps, fixture.terms.entries_snapshot())).unwrap(),
        before
    );
}

#[test]
fn live_mixed_bounds_equalities_and_repeated_definitions_preserve_first_binding() {
    let mut fixture = Fixture::new();
    fixture.add(AletheRule::FreshDefEq, fixture.d, fixture.x);
    fixture.add(AletheRule::FreshDefBound, fixture.d, fixture.x);
    let lower = fixture
        .terms
        .mk_app(Symbol::named("<="), [fixture.x, fixture.d], Sort::Bool);
    fixture.proof.add_rule_step(
        AletheRule::FreshDefBound,
        vec![lower],
        vec![],
        vec![fixture.d],
    );
    assert_eq!(compare(&fixture, None), Ok(1));
    assert_eq!(compare(&fixture, Some(&[])), Ok(1));
    let checked = FreshDefRegistry::collect(&fixture.proof, &fixture.terms, None).unwrap();
    assert_eq!(checked.bindings["cancel-definition"].step, ProofId(0));
}

#[test]
fn independent_numeric_and_boolean_definitions_remain_accepted() {
    let mut fixture = Fixture::new();
    let defined = fixture
        .terms
        .mk_var("cancel-boolean-definition", Sort::Bool);
    let source = fixture.terms.mk_var("cancel-boolean-source", Sort::Bool);
    fixture.add(AletheRule::FreshDefEq, defined, source);
    assert_eq!(compare(&fixture, Some(&[])), Ok(2));
}

#[test]
fn every_callback_in_real_binding_and_rich_name_walks_refuses_terminally() {
    let fixture = Fixture::rich();
    assert_eq!(compare(&fixture, Some(&fixture.assertions)), Ok(1));
    every_refusal(&fixture);
}

#[test]
fn every_callback_on_invalid_definitions_including_final_error_poll_refuses() {
    let mut fixture = Fixture::new();
    let other = fixture.terms.mk_var("other-definiens", Sort::Int);
    fixture.add(AletheRule::FreshDefEq, fixture.d, other);
    assert!(compare(&fixture, Some(&[])).is_err());
    every_refusal(&fixture);
}

#[test]
fn empty_registry_still_has_cancellable_entry_and_final_checkpoints() {
    let mut fixture = Fixture::new();
    fixture.proof.steps.clear();
    assert_eq!(compare(&fixture, None), Ok(0));
    every_refusal(&fixture);
}

#[test]
fn precancel_precedes_even_malformed_raw_handles() {
    let terms = TermStore::new();
    let mut proof = Proof::new();
    proof.add_rule_step(
        AletheRule::FreshDefBound,
        vec![TermId::SENTINEL],
        vec![],
        vec![TermId::SENTINEL],
    );
    let mut calls = 0;
    let result = FreshDefRegistry::collect_with_progress(&proof, &terms, None, &mut |_, _| {
        calls += 1;
        false
    });
    assert!(matches!(result, Err(ProofCheckError::ResourceLimit)));
    assert_eq!(calls, 1);
}

#[test]
fn malformed_rule_shapes_and_sort_mismatch_preserve_old_errors() {
    for alteration in 0..4 {
        let mut fixture = Fixture::new();
        let truth = fixture.terms.true_term();
        let real = fixture.terms.mk_var("real-source", Sort::Real);
        let wrong_sort = fixture
            .terms
            .mk_app(Symbol::named("<="), [fixture.d, real], Sort::Bool);
        let ProofStep::Step {
            clause,
            premises,
            args,
            ..
        } = &mut fixture.proof.steps[0]
        else {
            panic!("definition fixture")
        };
        match alteration {
            0 => premises.push(ProofId(0)),
            1 => args.clear(),
            2 => clause[0] = truth,
            3 => clause[0] = wrong_sort,
            _ => unreachable!(),
        }
        assert!(compare(&fixture, None).is_err());
    }
}

#[test]
fn duplicate_mixed_rules_with_different_definientia_are_not_independent_tables() {
    let mut fixture = Fixture::new();
    let different = fixture.terms.mk_var("different-source", Sort::Int);
    fixture.add(AletheRule::FreshDefEq, fixture.d, different);
    let error = compare(&fixture, None).unwrap_err();
    assert!(
        matches!(error, ProofCheckError::InvalidTheoryLemma { reason, .. } if reason.contains("SECOND definiens"))
    );
}

#[test]
fn even_acyclic_references_to_another_introduced_symbol_still_fail_independence() {
    let mut fixture = Fixture::new();
    let second = fixture.terms.mk_var("second-definition", Sort::Int);
    fixture.add(AletheRule::FreshDefEq, second, fixture.d);
    let error = compare(&fixture, None).unwrap_err();
    assert!(
        matches!(error, ProofCheckError::InvalidTheoryLemma { reason, .. } if reason.contains("inside a definiens"))
    );
}

#[test]
fn self_reference_and_dependency_cycle_keep_the_old_rejection() {
    for cyclic in [false, true] {
        let mut fixture = Fixture::new();
        fixture.proof.steps.clear();
        let other = if cyclic {
            fixture.terms.mk_var("cycle-definition", Sort::Int)
        } else {
            fixture.d
        };
        let expression =
            fixture
                .terms
                .mk_app(Symbol::named("source-expression"), [other], Sort::Int);
        fixture.add(AletheRule::FreshDefEq, fixture.d, expression);
        if cyclic {
            fixture.add(AletheRule::FreshDefBound, other, fixture.d);
        }
        assert!(compare(&fixture, Some(&[])).is_err());
    }
}

#[test]
fn source_and_assume_freshness_are_both_name_based_across_sorts() {
    for as_assume in [false, true] {
        let mut fixture = Fixture::new();
        let same_name = fixture.terms.mk_var("cancel-definition", Sort::Bool);
        if as_assume {
            fixture.proof.add_assume(same_name, None);
        } else {
            fixture.assertions.push(same_name);
        }
        let error = compare(&fixture, Some(&fixture.assertions)).unwrap_err();
        assert!(
            matches!(error, ProofCheckError::InvalidTheoryLemma { reason, .. } if reason.contains("NOT fresh"))
        );
    }
}

#[test]
fn application_heads_binder_names_and_triggers_still_contribute_to_freshness() {
    for location in 0..4 {
        let mut fixture = Fixture::new();
        let truth = fixture.terms.true_term();
        let root = match location {
            0 => fixture
                .terms
                .mk_app(Symbol::named("cancel-definition"), [], Sort::Bool),
            1 => fixture
                .terms
                .mk_let(vec![("cancel-definition".to_owned(), fixture.x)], truth),
            2 => fixture
                .terms
                .mk_forall(vec![("cancel-definition".to_owned(), Sort::Int)], truth),
            3 => fixture
                .terms
                .mk_exists_with_triggers(vec![], truth, vec![vec![fixture.d]]),
            _ => unreachable!(),
        };
        fixture.assertions.push(root);
        assert!(compare(&fixture, Some(&fixture.assertions)).is_err());
    }
}

#[test]
fn duplicate_fanout_adds_checkpoints_for_edges_not_only_unique_nodes() {
    let mut terms = TermStore::new();
    let leaf = terms.mk_var("repeated-leaf", Sort::Int);
    let narrow = terms.mk_app(Symbol::named("fanout"), [leaf], Sort::Int);
    let wide = terms.mk_app(Symbol::named("fanout"), vec![leaf; 65], Sort::Int);
    let usage = |root| {
        let mut count = 0;
        collect_symbol_names(
            &terms,
            root,
            &mut DetHashSet::default(),
            &mut DetHashSet::default(),
            &mut |_, _| {
                count += 1;
                true
            },
        )
        .unwrap();
        count
    };
    // Each repeated edge is pushed once and popped/checked even when visited.
    assert_eq!(usage(wide) - usage(narrow), 64 * 3);
}
