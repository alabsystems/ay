// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn every_projection_poll_refuses_before_any_candidate_is_published() {
    let original = source();
    let before = format!("{original:?}");
    let mut count = 0;
    assert!(Projection::new(&original, &mut || {
        count += 1;
        true
    })
    .is_some());
    assert!(count > original.clauses().len());
    for stop in 1..=count {
        let mut calls = 0;
        let mut stopped = false;
        let result = Projection::new(&original, &mut || {
            calls += 1;
            stopped |= calls == stop;
            !stopped
        });
        assert!(result.is_none(), "projection checkpoint {stop}/{count}");
        assert!(stopped);
        assert_eq!(calls, stop, "refusal must not run a later transform phase");
        assert_eq!(format!("{original:?}"), before);
    }
}

#[test]
fn every_lift_poll_refuses_without_partial_model_or_source_mutation() {
    let original = source();
    let projection = project(&original);
    let candidate = model(projection.reduced());
    let before = format!("{candidate:?}");
    let reduced_before = format!("{:?}", projection.reduced());
    let mut count = 0;
    assert!(projection
        .lift(&candidate, &mut || {
            count += 1;
            true
        })
        .is_some());
    assert!(count > candidate.len());
    for stop in 1..=count {
        let mut calls = 0;
        let result = projection.lift(&candidate, &mut || {
            calls += 1;
            calls < stop
        });
        assert!(result.is_none(), "lift checkpoint {stop}/{count}");
        assert_eq!(calls, stop);
        assert_eq!(format!("{candidate:?}"), before);
        assert_eq!(format!("{:?}", projection.reduced()), reduced_before);
    }
}

#[test]
fn a_shared_stopped_callback_does_not_gain_a_new_grant_between_projection_and_lift() {
    let original = source();
    let mut projection_calls = 0;
    let baseline = Projection::new(&original, &mut || {
        projection_calls += 1;
        true
    })
    .unwrap();
    let candidate = model(baseline.reduced());
    let mut remaining = projection_calls;
    let mut stopped = false;
    let mut poll = || {
        if remaining == 0 {
            stopped = true;
        }
        if stopped {
            return false;
        }
        remaining -= 1;
        true
    };
    let projection = Projection::new(&original, &mut poll).unwrap();
    assert!(projection.lift(&candidate, &mut poll).is_none());
    assert!(projection.lift(&candidate, &mut poll).is_none());
    drop(poll);
    assert!(stopped);
    assert_eq!(remaining, 0);
    // Caller-owned sticky state is the boundary; a genuinely fresh invocation
    // may proceed. This helper has no persistent proof or Unsafe authority.
    assert!(projection.lift(&candidate, &mut || true).is_some());
}

#[test]
fn panics_at_projection_and_lift_callbacks_never_modify_borrowed_sources() {
    let original = source();
    let before = format!("{original:?}");
    let refused = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        Projection::new(&original, &mut || -> bool { panic!("caller stop") })
    }));
    assert!(refused.is_err());
    assert_eq!(format!("{original:?}"), before);
    let projection = project(&original);
    let candidate = model(projection.reduced());
    let before = format!("{candidate:?}");
    let refused = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        projection.lift(&candidate, &mut || -> bool { panic!("caller stop") })
    }));
    assert!(refused.is_err());
    assert_eq!(format!("{candidate:?}"), before);
}
