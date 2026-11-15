// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

fn fixture() -> Vec<(TermData, Sort)> {
    let mut values = entries();
    values.push((
        TermData::Let(vec![("local".into(), TermId(2))], TermId(3)),
        Sort::Int,
    ));
    values.push((
        TermData::Forall(
            vec![("bound".into(), Sort::Int)],
            TermId(0),
            vec![vec![TermId(2)]],
        ),
        Sort::Bool,
    ));
    values.push((
        TermData::App(Symbol::named("="), vec![TermId(2), TermId(3)]),
        Sort::Bool,
    ));
    values.push(rational(2, 6));
    values.push(rational(3, 7));
    values
}

fn usage(values: &[(TermData, Sort)]) -> (usize, usize, usize) {
    let (mut work, mut bytes, mut polls) = (0usize, 0usize, 0usize);
    validate_term_snapshot_with_progress(values, &mut |w, b| {
        work = work.checked_add(w).unwrap();
        bytes = bytes.checked_add(b).unwrap();
        polls = polls.saturating_add(1);
        true
    })
    .unwrap();
    (work, bytes, polls)
}

#[test]
fn every_callback_refusal_including_final_poll_is_terminal_and_nonmutating() {
    let values = fixture();
    let before = serde_json::to_vec(&values).unwrap();
    let (_, _, polls) = usage(&values);
    for stop in 1..=polls {
        let mut calls = 0;
        let result = validate_term_snapshot_with_progress(&values, &mut |_, _| {
            calls += 1;
            calls != stop
        });
        assert_eq!(result, Err(ProofCheckError::ResourceLimit), "stop {stop}");
        assert_eq!(calls, stop);
    }
    assert_eq!(serde_json::to_vec(&values).unwrap(), before);
    run(&values).unwrap();
}

#[test]
fn exact_cumulative_work_and_allocation_envelopes_are_shared_across_entries() {
    let values = fixture();
    let (work, bytes, _) = usage(&values);
    assert!(work > 1 && bytes > 1);
    for (work_limit, byte_limit, expected) in [
        (work, bytes, true),
        (work - 1, bytes, false),
        (work, bytes - 1, false),
    ] {
        let (mut w, mut b) = (0usize, 0usize);
        let result = validate_term_snapshot_with_progress(&values, &mut |dw, db| {
            w = w.checked_add(dw).unwrap();
            b = b.checked_add(db).unwrap();
            w <= work_limit && b <= byte_limit
        });
        assert_eq!(result.is_ok(), expected);
        if !expected {
            assert_eq!(result, Err(ProofCheckError::ResourceLimit));
        }
    }
}

#[test]
fn duplicate_argument_edges_and_empty_trigger_groups_are_incrementally_debited() {
    let base = entries();
    let base_work = usage(&base).0;
    for extra in [
        (
            TermData::App(Symbol::named("uf"), vec![TermId(2); 4_096]),
            Sort::Int,
        ),
        (
            TermData::Forall(vec![], TermId(0), vec![vec![]; 4_096]),
            Sort::Bool,
        ),
    ] {
        let mut values = base.clone();
        values.push(extra);
        assert!(usage(&values).0 >= base_work + 4_096);
        let mut spent = 0;
        assert_eq!(
            validate_term_snapshot_with_progress(&values, &mut |w, _| {
                spent += w;
                spent <= base_work + 32
            }),
            Err(ProofCheckError::ResourceLimit)
        );
    }
}

#[test]
fn unused_large_names_cannot_enter_hashing_without_a_full_payload_charge() {
    let values = vec![(TermData::Var("v".repeat(16_384), 0), Sort::Int)];
    let mut saw_payload = false;
    assert_eq!(
        validate_term_snapshot_with_progress(&values, &mut |w, _| {
            saw_payload |= w >= 16_384;
            w < 16_384
        }),
        Err(ProofCheckError::ResourceLimit)
    );
    assert!(saw_payload);
    run(&values).unwrap();
}

#[test]
fn malformed_diagnostic_allocation_can_be_refused_before_publication() {
    let values = vec![(TermData::Not(TermId::SENTINEL), Sort::Bool)];
    assert_eq!(
        validate_term_snapshot_with_progress(&values, &mut |_, bytes| bytes == 0),
        Err(ProofCheckError::ResourceLimit)
    );
    assert!(matches!(
        run(&values),
        Err(ProofCheckError::MalformedProofBundle { .. })
    ));
}
