// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

#[test]
fn exact_and_one_short_handoff_work_use_the_same_admission() {
    let originals = arena();
    let mut trace = pending(&originals);
    let mut used = 0;
    assert!(trace.finish_original_transfer(originals, 1, &mut |units| {
        used += units;
        true
    }));
    assert!(used > 0);
    for grant in [used - 1, used] {
        let originals = arena();
        let mut trace = pending(&originals);
        let mut left = grant;
        let mut stopped = false;
        let accepted = trace.finish_original_transfer(originals, 1, &mut |units| {
            if stopped || units > left {
                stopped = true;
                return false;
            }
            left -= units;
            true
        });
        assert_eq!(accepted, grant == used);
        if accepted {
            assert_eq!(left, 0);
        }
    }
}

#[test]
fn one_shot_refusal_and_caught_admission_panic_cannot_revive_capture() {
    for panic in [false, true] {
        let originals = arena();
        let mut trace = pending(&originals);
        let original = trace.original_control().unwrap();
        let mut calls = 0;
        let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            trace.finish_original_transfer(originals, 1, &mut |_| {
                calls += 1;
                if calls == 3 {
                    assert!(!panic, "injected observer unwind");
                    return false;
                }
                true
            })
        }));
        if panic {
            assert!(outcome.is_err());
        } else {
            assert!(!outcome.unwrap());
        }
        assert!(!original.open());
        assert_eq!(calls, 3, "no callback after the first refusal");
    }
}

#[test]
fn captured_callback_survives_tls_replacement_and_is_sticky() {
    let armed = Arc::new(AtomicBool::new(false));
    let observed = armed.clone();
    let original_scope = ay_core::resource::enter_check_stop(Arc::new(move || {
        observed.swap(false, Ordering::AcqRel)
    }));
    let originals = arena();
    let mut trace = pending(&originals);
    drop(original_scope);
    let _replacement = ay_core::resource::enter_check_stop(Arc::new(|| false));
    armed.store(true, Ordering::Release);
    let control = trace.original_control().unwrap();
    assert!(!trace.finish_original_transfer(originals, 1, &mut |_| true));
    assert!(!control.open());
}

#[test]
fn a_raw_original_append_cannot_bypass_the_ledger_event_prefix() {
    let originals = arena();
    let mut trace = pending(&originals);
    trace.add_clause_with_hint_slices(3, &[x()], true, &[]);
    assert!(trace.proof_work_exhausted());
    assert!(!trace.finish_original_transfer(originals, 1, &mut |_| true));
}

#[test]
fn captured_guard_is_debited_after_its_scope_ends_without_a_fresh_allowance() {
    let mut guard = ay_core::resource::Guard::new();
    guard.set_rlimit(Some(3));
    let entered = guard.enter();
    let control = OriginalControl::capture(None, None, None).unwrap();
    let mut trace = ClauseTrace::new();
    assert!(trace.begin_original_transfer(control.clone()));
    drop(entered);
    let replacement = ay_core::resource::Guard::new();
    let _replacement = replacement.enter();
    let originals = arena();
    assert!(!trace.note_ledger_original(1, originals.retained_bytes().unwrap()));
    assert_eq!(guard.ticks(), 4);
    assert!(guard.poll().is_some());
    assert_eq!(replacement.ticks(), 0);
    assert!(!control.open());
}
