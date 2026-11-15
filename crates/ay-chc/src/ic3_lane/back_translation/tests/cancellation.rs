// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::cell::Cell;
use std::time::Duration;

use ay_core::time::Instant;

use super::*;

fn live_deadline() -> Instant {
    Instant::now() + Duration::from_secs(30)
}

fn fixture_clauses() -> Vec<Vec<Literal>> {
    vec![
        vec![literal(0, false), literal(1, true)],
        vec![literal(0, true), literal(1, false)],
        vec![literal(0, true)],
        vec![literal(1, true), literal(1, true), literal(0, false)],
    ]
}

#[test]
fn every_reconstruction_poll_refuses_without_reviving_or_publishing_partial_model() {
    let (params, latches) = bool_fixture();
    let clauses = fixture_clauses();
    let pred = PredicateId::new(0);
    let calls = Cell::new(0);
    let mut count = || {
        calls.set(calls.get() + 1);
        true
    };
    let control = Control::new(live_deadline(), &mut count);
    let model = back_translate_controlled(pred, &params, &latches, &clauses, &control)
        .expect("the live control must preserve the existing translation");
    assert_eq!(
        model.get(&pred).expect("complete interpretation").formula,
        translated_formula(&params, &latches, &clauses)
    );
    let total = calls.get();
    assert!(total > clauses.len() * 2 + params.len());

    for stop_at in 1..=total {
        let refused_calls = Cell::new(0);
        let mut refuse_once = || {
            let call = refused_calls.get() + 1;
            refused_calls.set(call);
            call != stop_at
        };
        let stopped = Control::new(live_deadline(), &mut refuse_once);
        assert!(
            back_translate_controlled(pred, &params, &latches, &clauses, &stopped).is_none(),
            "refusal at poll {stop_at}/{total} must discard the whole candidate"
        );
        assert!(stopped.stopped());
        assert_eq!(refused_calls.get(), stop_at);
        assert!(
            back_translate_controlled(pred, &params, &latches, &clauses, &stopped).is_none(),
            "a callback that would now return true must not revive reconstruction"
        );
        assert_eq!(refused_calls.get(), stop_at);
    }

    assert_eq!(
        translated_formula(&params, &latches, &clauses),
        model.get(&pred).expect("complete interpretation").formula,
        "a fresh call after refusal must remain usable"
    );
}

#[test]
fn expired_reconstruction_does_not_even_invoke_callback() {
    let (params, latches) = bool_fixture();
    let calls = Cell::new(0);
    let mut count = || {
        calls.set(calls.get() + 1);
        true
    };
    let control = Control::new(Instant::now(), &mut count);
    assert!(back_translate_controlled(
        PredicateId::new(0),
        &params,
        &latches,
        &fixture_clauses(),
        &control,
    )
    .is_none());
    assert!(control.stopped());
    assert_eq!(calls.get(), 0);
}

#[test]
fn every_literal_is_observed_in_a_single_long_clause() {
    let (params, latches) = bool_fixture();
    let clause = vec![literal(0, true); 257];
    let calls = Cell::new(0);
    let mut count = || {
        calls.set(calls.get() + 1);
        true
    };
    let control = Control::new(live_deadline(), &mut count);
    assert!(translate_clause(&clause, &params, &latches, &control).is_some());
    assert_eq!(calls.get(), clause.len() + 2);

    let refusal = Cell::new(0);
    let mut last_literal = || {
        refusal.set(refusal.get() + 1);
        refusal.get() != clause.len() + 1
    };
    let control = Control::new(live_deadline(), &mut last_literal);
    assert!(translate_clause(&clause, &params, &latches, &control).is_none());
    assert_eq!(refusal.get(), clause.len() + 1);
}

#[test]
fn partner_discovery_polls_even_unpaired_and_duplicate_clauses() {
    let clauses = fixture_clauses();
    let calls = Cell::new(0);
    let mut count = || {
        calls.set(calls.get() + 1);
        true
    };
    let control = Control::new(live_deadline(), &mut count);
    assert_eq!(
        exact_iff_partners(&clauses, &control),
        Some(vec![Some(1), Some(0), None, None])
    );
    assert_eq!(calls.get(), clauses.len() + 2);
}

#[test]
fn empty_cnf_and_empty_clause_keep_opposite_meanings_under_control() {
    let (params, latches) = bool_fixture();
    for (clauses, expected) in [(Vec::new(), true), (vec![Vec::new()], false)] {
        let mut keep_going = || true;
        let control = Control::new(live_deadline(), &mut keep_going);
        let model =
            back_translate_controlled(PredicateId::new(0), &params, &latches, &clauses, &control)
                .expect("empty CNF and empty clause are both representable");
        assert_eq!(
            model
                .get(&PredicateId::new(0))
                .expect("complete interpretation")
                .formula,
            ChcExpr::Bool(expected)
        );
    }
}

#[test]
fn missing_latch_is_not_recovered_as_a_partial_invariant() {
    let (params, latches) = bool_fixture();
    let mut keep_going = || true;
    let control = Control::new(live_deadline(), &mut keep_going);
    assert!(back_translate_controlled(
        PredicateId::new(0),
        &params,
        &latches,
        &[vec![literal(0, true)], vec![literal(9, true)]],
        &control,
    )
    .is_none());
}

#[test]
fn deadline_expiry_in_final_true_callback_discards_completed_model() {
    let (params, latches) = bool_fixture();
    let clauses = fixture_clauses();
    let start = Instant::now();
    let deadline = start + Duration::from_secs(30);
    let now = Cell::new(start);
    let clock = || now.get();
    let calls = Cell::new(0);
    let mut count = || {
        calls.set(calls.get() + 1);
        true
    };
    let control = Control::with_clock(deadline, &mut count, &clock);
    assert!(
        back_translate_controlled(PredicateId::new(0), &params, &latches, &clauses, &control,)
            .is_some()
    );
    let final_poll = calls.get();
    let late_calls = Cell::new(0);
    let mut expire_at_publication = || {
        let call = late_calls.get() + 1;
        late_calls.set(call);
        if call == final_poll {
            now.set(deadline);
        }
        true
    };
    let control = Control::with_clock(deadline, &mut expire_at_publication, &clock);
    assert!(
        back_translate_controlled(PredicateId::new(0), &params, &latches, &clauses, &control,)
            .is_none()
    );
    assert!(control.stopped());
    assert_eq!(late_calls.get(), final_poll);
}
