// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::{Symbol, TermData, TermId};

use super::*;

mod boundaries;
mod empty_identity;

struct Fixture {
    terms: TermStore,
    declarations: Vec<(String, Vec<String>)>,
    selectors: Vec<(String, Vec<String>)>,
    signatures: Vec<DatatypeMemberSignature>,
}

fn fixture() -> Fixture {
    let mut terms = TermStore::new();
    let carrier = Sort::Uninterpreted("MeterBox".into());
    let value = terms.mk_var("payload", Sort::Int);
    let boxed = terms.mk_app(Symbol::named("meter-mk"), [value], carrier.clone());
    let _selector_application = terms.mk_app(Symbol::named("meter-value"), [boxed], Sort::Int);
    let _recognizer_application = terms.mk_app(Symbol::named("is-meter-mk"), [boxed], Sort::Bool);
    Fixture {
        terms,
        declarations: vec![("MeterBox".into(), vec!["meter-mk".into()])],
        selectors: vec![("meter-mk".into(), vec!["meter-value".into()])],
        signatures: vec![
            DatatypeMemberSignature {
                identity: "meter-mk".into(),
                argument_sorts: vec![Sort::Int],
                result_sort: carrier.clone(),
                nullary_term: None,
            },
            DatatypeMemberSignature {
                identity: "is-meter-mk".into(),
                argument_sorts: vec![carrier.clone()],
                result_sort: Sort::Bool,
                nullary_term: None,
            },
            DatatypeMemberSignature {
                identity: "meter-value".into(),
                argument_sorts: vec![carrier],
                result_sort: Sort::Int,
                nullary_term: None,
            },
        ],
    }
}

fn check(
    fixture: &Fixture,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<(), ProofCheckError> {
    validate_datatype_signature_context_with_progress(
        &fixture.terms,
        Some(&fixture.declarations),
        Some(&fixture.selectors),
        &fixture.signatures,
        progress,
    )
}

fn usage(fixture: &Fixture) -> (usize, usize, usize) {
    let (mut work, mut bytes, mut polls) = (0, 0, 0);
    check(fixture, &mut |w, b| {
        work += w;
        bytes += b;
        polls += 1;
        true
    })
    .unwrap();
    (work, bytes, polls)
}

fn assert_invalid(result: Result<(), ProofCheckError>) {
    assert!(
        matches!(
            result,
            Err(ProofCheckError::InvalidDatatypeSignatureContext { .. })
        ),
        "{result:?}"
    );
}

#[test]
fn valid_context_matches_compatibility_and_preserves_source() {
    let fixture = fixture();
    let before = fixture.terms.entries_snapshot();
    check(&fixture, &mut |_, _| true).unwrap();
    validate_datatype_signature_context(
        &fixture.terms,
        Some(&fixture.declarations),
        Some(&fixture.selectors),
        &fixture.signatures,
    )
    .unwrap();
    assert_eq!(before, fixture.terms.entries_snapshot());
}

#[test]
fn every_callback_including_final_poll_can_refuse_without_resuming() {
    let fixture = fixture();
    let (_, _, polls) = usage(&fixture);
    assert!(polls > 20);
    for stop in 1..=polls {
        let mut calls = 0;
        let result = check(&fixture, &mut |_, _| {
            calls += 1;
            calls != stop
        });
        assert!(
            matches!(result, Err(ProofCheckError::ResourceLimit)),
            "poll {stop}: {result:?}"
        );
        assert_eq!(calls, stop);
    }
}

#[test]
fn work_and_bytes_are_exactly_cumulative_and_shared_between_calls() {
    let fixture = fixture();
    let (work, bytes, _) = usage(&fixture);
    for (max_work, max_bytes, success) in [
        (work, bytes, true),
        (work - 1, bytes, false),
        (work, bytes - 1, false),
    ] {
        let (mut spent_work, mut spent_bytes) = (0, 0);
        let mut progress = |w, b| {
            spent_work += w;
            spent_bytes += b;
            spent_work <= max_work && spent_bytes <= max_bytes
        };
        assert_eq!(check(&fixture, &mut progress).is_ok(), success);
        if success {
            assert!(matches!(
                check(&fixture, &mut progress),
                Err(ProofCheckError::ResourceLimit)
            ));
        }
    }
}

#[test]
fn duplicate_missing_and_extra_context_members_remain_invalid() {
    for mutation in 0..7 {
        let mut fixture = fixture();
        match mutation {
            0 => fixture.signatures.push(fixture.signatures[0].clone()),
            1 => {
                fixture.signatures.remove(1);
            }
            2 => fixture.signatures.push(DatatypeMemberSignature {
                identity: "unused-extra".into(),
                argument_sorts: vec![],
                result_sort: Sort::Int,
                nullary_term: None,
            }),
            3 => fixture.declarations.push(fixture.declarations[0].clone()),
            4 => fixture.selectors.push(fixture.selectors[0].clone()),
            5 => fixture.selectors.clear(),
            _ => fixture.selectors[0].1.push("meter-value".into()),
        }
        assert_invalid(check(&fixture, &mut |_, _| true));
    }
}

#[test]
fn unused_member_occurrence_is_still_authenticated() {
    let mut fixture = fixture();
    let wrong = fixture.terms.false_term();
    let _ill_typed_member_occurrence = fixture.terms.mk_app(
        Symbol::named("meter-mk"),
        [wrong],
        Sort::Uninterpreted("MeterBox".into()),
    );
    assert_invalid(check(&fixture, &mut |_, _| true));
}

#[test]
fn missing_application_argument_ids_are_typed_errors_not_indexing_panics() {
    for missing in [TermId::new(100), TermId::new(u32::MAX)] {
        let mut fixture = fixture();
        let mut entries = fixture.terms.entries_snapshot();
        entries.push((
            TermData::App(Symbol::named("meter-mk"), vec![missing]),
            Sort::Uninterpreted("MeterBox".into()),
        ));
        let (true_term, false_term) = fixture.terms.boolean_constant_ids();
        fixture.terms = TermStore::from_entries(entries, true_term, false_term, 0);
        assert_invalid(check(&fixture, &mut |_, _| true));
    }
}

#[test]
fn missing_nullary_binding_is_typed_and_both_valid_representations_survive() {
    let mut fixture = fixture();
    fixture.terms = TermStore::new();
    let carrier = Sort::Uninterpreted("MeterBox".into());
    let pinned = fixture
        .terms
        .mk_fresh_named_var("meter-mk", carrier.clone());
    let _nullary_member_application =
        fixture
            .terms
            .mk_app(Symbol::named("meter-mk"), Vec::<TermId>::new(), carrier);
    fixture.selectors[0].1.clear();
    fixture.signatures.pop();
    fixture.signatures[0].argument_sorts.clear();
    fixture.signatures[0].nullary_term = Some(pinned);
    check(&fixture, &mut |_, _| true).unwrap();
    fixture.signatures[0].nullary_term = Some(TermId::new(u32::MAX));
    assert_invalid(check(&fixture, &mut |_, _| true));
}
