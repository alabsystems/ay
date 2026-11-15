// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Cooperative cancellation cannot turn a partial search/recheck into evidence.
use super::*;
use ay_core::resource::{self, ChildSpec, Guard, NodeLabel};
use std::cell::Cell;

fn contradiction() -> Vec<MultiConstraint> {
    vec![con(
        poly(&[(&[v(1), v(1)], 1), (&[v(2), v(2)], 1)]),
        Rel::Lt,
    )]
}

#[test]
fn caller_polls_preserve_the_complete_checked_certificate() {
    let constraints = contradiction();
    let expected = search(&constraints, &[v(1), v(2)]).expect("checked refutation");
    let polls = Cell::new(0);
    let allow = || {
        polls.set(polls.get() + 1);
        true
    };
    let found = search_with_progress(&constraints, &[v(1), v(2)], &SosProgress::new(&allow))
        .expect("uninterrupted checked refutation");
    assert!(
        polls.get() > 100,
        "control reaches construction, LP and replay"
    );
    assert_eq!(found.verify(&constraints), Ok(()));
    let render = |cert: &SosCertificate| cert.render_alethe("same", |id| format!("v{}", id.0));
    assert_eq!(render(&found), render(&expected));
}

#[test]
fn search_refusal_is_sticky_through_later_templates_and_final_recheck() {
    let constraints = contradiction();
    let total = Cell::new(0);
    let allow = || {
        total.set(total.get() + 1);
        true
    };
    assert!(search_with_progress(&constraints, &[v(1), v(2)], &SosProgress::new(&allow)).is_some());
    for stop_at in [2, total.get() / 3, 2 * total.get() / 3, total.get()] {
        let polls = Cell::new(0);
        // A later callback would allow work again. The shared sticky state must
        // not invoke it or let another template resume a refused attempt.
        let allow = || {
            polls.set(polls.get() + 1);
            polls.get() != stop_at
        };
        let progress = SosProgress::new(&allow);
        assert!(search_with_progress(&constraints, &[v(1), v(2)], &progress).is_none());
        assert_eq!(polls.get(), stop_at);
        assert!(!progress.poll());
        assert_eq!(polls.get(), stop_at);
    }
}

#[test]
fn phase_one_stops_inside_an_otherwise_feasible_lp() {
    let a = vec![vec![r(1), r(1), r(1)], vec![r(1), r(-1), r(0)]];
    let b = vec![r(2), r(0)];
    let total = Cell::new(0);
    let allow = || {
        total.set(total.get() + 1);
        true
    };
    let expected =
        lp_phase1_feasible_with_progress(a.clone(), b.clone(), 3, &SosProgress::new(&allow))
            .expect("feasible");
    assert_eq!(Some(expected), lp_phase1_feasible(a.clone(), b.clone(), 3));
    let stop_at = total.get() / 2;
    assert!(
        stop_at > a.len() * a[0].len() + b.len(),
        "past input validation"
    );
    let guard = Guard::root_child(ChildSpec::new(NodeLabel::Check));
    let _scope = guard.enter();
    let polls = Cell::new(0);
    let allow = || {
        polls.set(polls.get() + 1);
        if polls.get() == stop_at {
            guard.cancel();
        }
        !resource::check_stop_requested()
    };
    let progress = SosProgress::new(&allow);
    assert!(lp_phase1_feasible_with_progress(a, b, 3, &progress).is_none());
    assert!(resource::check_stop_requested());
    assert_eq!(polls.get(), stop_at);
    assert!(!progress.poll());
}

#[test]
fn independent_recheck_refuses_in_progress_and_before_success() {
    let constraints = contradiction();
    let cert = search(&constraints, &[v(1), v(2)]).expect("valid certificate");
    let total = Cell::new(0);
    let allow = || {
        total.set(total.get() + 1);
        true
    };
    assert_eq!(
        cert.verify_with_progress(&constraints, &SosProgress::new(&allow)),
        Ok(())
    );
    for stop_at in [total.get() / 2, total.get()] {
        assert!(stop_at > 1);
        let polls = Cell::new(0);
        let allow = || {
            polls.set(polls.get() + 1);
            polls.get() != stop_at
        };
        assert_eq!(
            cert.verify_with_progress(&constraints, &SosProgress::new(&allow)),
            Err(SosError::ResourceLimit)
        );
        assert_eq!(polls.get(), stop_at);
    }
}
