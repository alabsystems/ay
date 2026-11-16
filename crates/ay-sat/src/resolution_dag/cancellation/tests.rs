// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

#![cfg(test)]

use super::*;
use std::panic::{catch_unwind, AssertUnwindSafe};

#[test]
fn fn_adapter_latches_refusal_without_reinvoking_a_changing_callback() {
    let mut calls = 0;
    let mut progress = || {
        calls += 1;
        calls != 2
    };
    let control = ProofControl::new(&mut progress);
    let predicate = || control.poll().is_err();
    fn call_fn(predicate: &dyn Fn() -> bool) -> bool {
        predicate()
    }
    assert!(!call_fn(&predicate));
    assert!(call_fn(&predicate));
    assert!(call_fn(&predicate));
    assert_eq!(calls, 2);
}

#[test]
fn caught_callback_panic_cannot_resurrect_progress() {
    let mut calls = 0;
    let mut progress = || {
        calls += 1;
        panic!("injected cancellation callback panic")
    };
    let control = ProofControl::new(&mut progress);
    assert!(catch_unwind(AssertUnwindSafe(|| control.poll())).is_err());
    assert_eq!(control.poll(), Err(ResolutionProofError::Cancelled));
    assert_eq!(calls, 1);
}

#[test]
fn final_refusal_happens_after_private_scratch_destruction() {
    struct Scratch<'a>(&'a Cell<bool>);
    impl Drop for Scratch<'_> {
        fn drop(&mut self) {
            self.0.set(true);
        }
    }
    let dropped = Cell::new(false);
    let mut calls = 0;
    let mut progress = || {
        calls += 1;
        if calls == 2 {
            assert!(dropped.get());
            false
        } else {
            true
        }
    };
    let control = ProofControl::new(&mut progress);
    let result = control.run(|_| {
        let _scratch = Scratch(&dropped);
        Ok(7)
    });
    assert_eq!(result, Err(ResolutionProofError::Cancelled));
    assert_eq!(calls, 2);
}

#[test]
fn live_control_preserves_original_errors_and_absolute_deadline() {
    let mut progress = || true;
    let control = ProofControl::new(&mut progress);
    assert_eq!(
        control.run::<()>(|_| Err(ResolutionProofError::NoEmptyClause)),
        Err(ResolutionProofError::NoEmptyClause)
    );
    assert_eq!(
        control.check(Some(Instant::now()), ResolutionProofPhase::Parse),
        Err(ResolutionProofError::DeadlineExceeded {
            phase: ResolutionProofPhase::Parse
        }),
    );
    // A clock refusal is not a caller cancellation and does not poison it.
    assert_eq!(control.check(None, ResolutionProofPhase::Parse), Ok(()));
}

#[test]
fn ordinary_error_has_no_new_callback_but_prior_refusal_still_wins() {
    for caught_refusal in [false, true] {
        let mut calls = 0;
        let mut progress = || {
            calls += 1;
            calls == 1
        };
        let control = ProofControl::new(&mut progress);
        let result = control.run::<()>(|control| {
            if caught_refusal {
                assert_eq!(control.poll(), Err(ResolutionProofError::Cancelled));
            }
            Err(ResolutionProofError::NoEmptyClause)
        });
        assert_eq!(
            result,
            Err(if caught_refusal {
                ResolutionProofError::Cancelled
            } else {
                ResolutionProofError::NoEmptyClause
            })
        );
        assert_eq!(calls, if caught_refusal { 2 } else { 1 });
    }
}
