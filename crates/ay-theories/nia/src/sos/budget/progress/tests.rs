// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::cell::Cell;

use super::SosProgress;
use crate::sos::lp::lp_phase1_feasible_with_progress;
use crate::sos::{search_with_progress, MultiConstraint, MultiPoly, Rel};
use ay_core::term::TermId;
use num_bigint::BigInt;
use num_rational::BigRational;

fn rational(numerator: i64, denominator: i64) -> BigRational {
    BigRational::new(BigInt::from(numerator), BigInt::from(denominator))
}

fn feasible(control: &SosProgress<'_>) -> Option<Vec<BigRational>> {
    lp_phase1_feasible_with_progress(
        vec![
            vec![rational(2, 1), rational(1, 1)],
            vec![rational(1, 1), rational(3, 1)],
        ],
        vec![rational(1, 1), rational(1, 1)],
        2,
        control,
    )
}

#[test]
fn lp_cancellation_at_entry_inside_work_and_final_poll_is_sticky() {
    let calls = Cell::new(0usize);
    let count = || {
        calls.set(calls.get() + 1);
        true
    };
    assert_eq!(
        feasible(&SosProgress::new(&count)),
        Some(vec![rational(2, 5), rational(1, 5)])
    );
    let total = calls.get();
    assert!(total > 4);
    for stop_at in [1, 3, total / 2, total] {
        let seen = Cell::new(0usize);
        // A one-shot stop deliberately permits future polls. The attempt's
        // local latch must still refuse every later phase and reuse.
        let once = || {
            seen.set(seen.get() + 1);
            seen.get() != stop_at
        };
        let control = SosProgress::new(&once);
        assert!(feasible(&control).is_none());
        assert_eq!(seen.get(), stop_at);
        assert!(feasible(&control).is_none());
        assert_eq!(seen.get(), stop_at);
    }
    assert!(feasible(&SosProgress::new(&|| true)).is_some());
}

#[test]
fn zero_row_lp_obeys_entry_and_publication_stop() {
    for stop_at in [1, 2] {
        let calls = Cell::new(0);
        let stop = || {
            calls.set(calls.get() + 1);
            calls.get() != stop_at
        };
        assert!(
            lp_phase1_feasible_with_progress(vec![], vec![], 3, &SosProgress::new(&stop)).is_none()
        );
    }
    assert_eq!(
        lp_phase1_feasible_with_progress(vec![], vec![], 3, &SosProgress::new(&|| true)),
        Some(vec![rational(0, 1); 3])
    );
}

fn strict_refutation() -> (Vec<MultiConstraint>, Vec<TermId>) {
    let x = TermId(1);
    let y = TermId(2);
    (
        vec![MultiConstraint {
            poly: MultiPoly {
                terms: vec![(vec![x, x], rational(1, 1)), (vec![y, y], rational(1, 1))],
            },
            rel: Rel::Lt,
        }],
        vec![x, y],
    )
}

#[test]
fn search_never_returns_a_certificate_after_observing_stop() {
    let (constraints, vars) = strict_refutation();
    let calls = Cell::new(0usize);
    let count = || {
        calls.set(calls.get() + 1);
        true
    };
    let cert = search_with_progress(&constraints, &vars, &SosProgress::new(&count))
        .expect("unstopped strict template has a certificate");
    assert_eq!(cert.verify(&constraints), Ok(()));
    let total = calls.get();
    assert!(total > 10);
    for stop_at in [1, total / 4, total / 2, total - 1, total] {
        let seen = Cell::new(0usize);
        let once = || {
            seen.set(seen.get() + 1);
            seen.get() != stop_at
        };
        let control = SosProgress::new(&once);
        assert!(search_with_progress(&constraints, &vars, &control).is_none());
        assert_eq!(seen.get(), stop_at);
        assert!(search_with_progress(&constraints, &vars, &control).is_none());
        assert_eq!(
            seen.get(),
            stop_at,
            "a stopped template cannot start another phase"
        );
    }
    assert!(search_with_progress(&constraints, &vars, &SosProgress::new(&|| true)).is_some());
}
