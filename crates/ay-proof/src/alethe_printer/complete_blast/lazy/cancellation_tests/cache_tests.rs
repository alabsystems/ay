// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::panic::{catch_unwind, AssertUnwindSafe};

fn old_value() -> DetHashSet<String> {
    ["retained-before-render".to_string()].into_iter().collect()
}

#[test]
fn every_key_and_retained_choice_copy_poll_observes_the_owner() {
    let f = Fixture::new();
    for key_only in [true, false] {
        let operation = |printer: &AlethePrinter<'_>| {
            if key_only {
                settled_key(printer, &[f.identity], None).map(|_| ())
            } else {
                settled::retained_opaque(
                    printer,
                    [f.quotient].into_iter().collect(),
                    &[printer.format_term(f.quotient)].into_iter().collect(),
                )
                .map(|_| ())
            }
        };
        let mut polls = 0;
        let mut callback = || {
            polls += 1;
            true
        };
        let printer = AlethePrinter::new(&f.terms).with_emission_progress(&mut callback);
        operation(&printer).expect("accepting copy");
        drop(printer);
        assert!(polls > 0);
        for stop in 1..=polls {
            let mut observed = 0;
            let mut callback = || {
                observed += 1;
                observed != stop
            };
            let printer = AlethePrinter::new(&f.terms).with_emission_progress(&mut callback);
            assert!(operation(&printer).is_none());
            assert!(operation(&printer).is_none());
            drop(printer);
            assert_eq!(observed, stop);
        }
    }
}

#[test]
fn cache_hit_copy_refusal_does_not_erase_existing_work() {
    settled::reset();
    settled::remember_settled("old".into(), old_value());
    let terms = TermStore::new();
    let mut polls = 0;
    let mut callback = || {
        polls += 1;
        polls != 3
    };
    let printer = AlethePrinter::new(&terms).with_emission_progress(&mut callback);
    assert!(settled_opaque(&printer, "old").is_none());
    assert!(settled_opaque(&printer, "old").is_none());
    drop(printer);
    assert_eq!(polls, 3);
    assert_eq!(settled::raw_lookup("old"), Some(old_value()));
}

#[test]
fn post_publication_refusal_rolls_back_a_replaced_entry() {
    settled::reset();
    settled::remember_settled("old".into(), old_value());
    let terms = TermStore::new();
    let calls = Cell::new(0usize);
    let armed = Cell::new(false);
    let mut callback = || {
        calls.set(calls.get() + 1);
        !armed.get() || calls.get() != 5
    };
    let printer = AlethePrinter::new(&terms).with_emission_progress(&mut callback);
    let candidate =
        Candidate::new(&printer, "old".into(), &DetHashSet::default()).expect("candidate");
    calls.set(0);
    armed.set(true);
    assert!(candidate.commit(&printer).is_none());
    assert_eq!(calls.get(), 5);
    assert_eq!(settled::raw_lookup("old"), Some(old_value()));
}

#[test]
fn post_publication_refusal_restores_an_evicted_table() {
    settled::reset();
    for index in 0..256 {
        settled::remember_settled(format!("old-{index}"), old_value());
    }
    let terms = TermStore::new();
    let calls = Cell::new(0usize);
    let armed = Cell::new(false);
    let mut callback = || {
        calls.set(calls.get() + 1);
        !armed.get() || calls.get() != 5
    };
    let printer = AlethePrinter::new(&terms).with_emission_progress(&mut callback);
    let candidate =
        Candidate::new(&printer, "new".into(), &DetHashSet::default()).expect("candidate");
    calls.set(0);
    armed.set(true);
    assert!(candidate.commit(&printer).is_none());
    assert_eq!(settled::raw_lookup("new"), None);
    for index in 0..256 {
        assert_eq!(
            settled::raw_lookup(&format!("old-{index}")),
            Some(old_value())
        );
    }
}

#[test]
fn an_observer_unwind_restores_the_old_entry_and_leaves_the_owner_stopped() {
    settled::reset();
    settled::remember_settled("old".into(), old_value());
    let terms = TermStore::new();
    let calls = Cell::new(0usize);
    let armed = Cell::new(false);
    let mut callback = || {
        calls.set(calls.get() + 1);
        assert!(
            !armed.get() || calls.get() != 5,
            "callback unwind after tentative retention"
        );
        true
    };
    let printer = AlethePrinter::new(&terms).with_emission_progress(&mut callback);
    let candidate =
        Candidate::new(&printer, "old".into(), &DetHashSet::default()).expect("candidate");
    calls.set(0);
    armed.set(true);
    assert!(catch_unwind(AssertUnwindSafe(|| candidate.commit(&printer))).is_err());
    assert_eq!(settled::raw_lookup("old"), Some(old_value()));
    assert!(printer.check_emission_progress(0).is_err());
    assert_eq!(calls.get(), 5);
}

#[test]
fn a_reentrant_other_owner_cannot_publish_into_the_pending_transaction() {
    settled::reset();
    let terms = TermStore::new();
    let other = AlethePrinter::new(&terms);
    let calls = Cell::new(0usize);
    let armed = Cell::new(false);
    let mut callback = || {
        calls.set(calls.get() + 1);
        if armed.get() && calls.get() == 5 {
            assert_eq!(settled::raw_lookup("pending"), None);
            Candidate::new(&other, "nested".into(), &DetHashSet::default())
                .expect("independent owner candidate")
                .commit(&other)
                .expect("skipped optional retention");
            false
        } else {
            true
        }
    };
    let printer = AlethePrinter::new(&terms).with_emission_progress(&mut callback);
    let candidate =
        Candidate::new(&printer, "pending".into(), &DetHashSet::default()).expect("candidate");
    calls.set(0);
    armed.set(true);
    assert!(candidate.commit(&printer).is_none());
    assert_eq!(settled::raw_lookup("pending"), None);
    assert_eq!(settled::raw_lookup("nested"), None);
    Candidate::new(&other, "later".into(), &DetHashSet::default())
        .expect("new transaction")
        .commit(&other)
        .expect("retained after rollback");
    assert_eq!(settled::raw_lookup("later"), Some(DetHashSet::default()));
}
