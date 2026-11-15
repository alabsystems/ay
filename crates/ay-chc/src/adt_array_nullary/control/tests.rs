// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::resource::{enter_check_stop, ChildSpec, NodeLabel};

#[test]
fn zero_budget_and_exhausted_original_guard_refuse_before_naming() {
    assert!(Control::capture(Duration::ZERO).is_none());
    let guard = Guard::root_child(ChildSpec::new(NodeLabel::Check).with_rlimit(Some(0)));
    let _scope = guard.enter();
    assert!(Control::capture(Duration::from_secs(5)).is_none());
}

#[test]
fn construction_debits_the_original_guard_not_a_fresh_grant() {
    let guard = Guard::root_child(ChildSpec::new(NodeLabel::Check).with_rlimit(Some(10)));
    let _scope = guard.enter();
    let control = Control::capture(Duration::from_secs(5)).expect("open owner");
    assert!(control.admit(7, 0).is_some());
    assert_eq!(guard.ticks(), 7);
    assert!(control.admit(4, 0).is_none());
    assert!(control.poll().is_none());
}

#[test]
fn nested_one_shot_refusal_stays_terminal_after_scope_replacement() {
    let armed = Arc::new(AtomicBool::new(false));
    let original = Arc::clone(&armed);
    let _outer = enter_check_stop(Arc::new(move || original.swap(false, Ordering::AcqRel)));
    let control = Control::capture(Duration::from_secs(5)).expect("open owner");
    {
        let _nested = control.enter();
        armed.store(true, Ordering::Release);
        assert!(ay_core::resource::check_stop_requested());
        assert!(!armed.load(Ordering::Acquire));
    }
    let _replacement = enter_check_stop(Arc::new(|| false));
    assert!(control.poll().is_none());
    assert!(control.remaining().is_none());
}

#[test]
fn caught_original_callback_panic_cannot_resume_this_owner() {
    let armed = Arc::new(AtomicBool::new(false));
    let original = Arc::clone(&armed);
    let _outer = enter_check_stop(Arc::new(move || {
        assert!(!original.swap(false, Ordering::AcqRel), "caller unwind");
        false
    }));
    let control = Control::capture(Duration::from_secs(5)).expect("open owner");
    armed.store(true, Ordering::Release);
    assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| control.poll())).is_err());
    assert!(control.poll().is_none());
}

#[test]
fn callback_reentry_cannot_hide_a_refusal_by_returning_false() {
    let armed = Arc::new(AtomicBool::new(false));
    let original = Arc::clone(&armed);
    let _outer = enter_check_stop(Arc::new(move || {
        if original.swap(false, Ordering::AcqRel) {
            assert!(ay_core::resource::check_stop_requested());
        }
        false
    }));
    let control = Control::capture(Duration::from_secs(5)).expect("open owner");
    let _nested = control.enter();
    armed.store(true, Ordering::Release);
    assert!(control.poll().is_none());
}

#[test]
fn expired_tree_slice_does_not_renew_or_exhaust_the_original_owner() {
    let control = Control::capture(Duration::from_secs(5)).expect("original owner");
    let before = control.remaining().expect("initial remaining");
    {
        let _slice = crate::smt::deadline::ScopedSmtDeadline::install(Duration::ZERO);
        assert!(crate::smt::deadline::smt_deadline_remaining().is_some_and(|time| time.is_zero()));
        assert!(
            control.poll().is_some(),
            "a local slice is not original refusal"
        );
    }
    assert!(control.remaining().expect("same owner remains").le(&before));
}
