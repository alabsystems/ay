// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::resource::{enter_check_stop, ChildSpec, Guard, NodeLabel};
use std::sync::{
    atomic::{AtomicBool, Ordering},
    Arc,
};

#[test]
fn zero_original_guard_refuses_and_admission_debits_same_guard() {
    let guard = Guard::root_child(ChildSpec::new(NodeLabel::Check).with_rlimit(Some(0)));
    let scope = guard.enter();
    assert!(Owner::capture().is_err());
    drop(scope);
    let guard = Guard::root_child(ChildSpec::new(NodeLabel::Check).with_rlimit(Some(10)));
    let _scope = guard.enter();
    let mut owner = Owner::capture().expect("owner");
    assert_eq!(owner.admit(7, 0), Ok(()));
    assert_eq!(guard.ticks(), 7);
    assert_eq!(owner.admit(4, 0), Err(Error::Resource));
    assert!(owner.poll().is_err());
}

#[test]
fn complete_replay_accepts_adequate_owner_and_refuses_short_owner() {
    let (problem, derivation) = evidence(32);
    let guard = Guard::root_child(ChildSpec::new(NodeLabel::Check).with_rlimit(Some(500_000)));
    let scope = guard.enter();
    assert_eq!(check(&problem, &derivation), Ok(()));
    let used = guard.ticks();
    assert!(used > 1);
    drop(scope);
    let short = Guard::root_child(ChildSpec::new(NodeLabel::Check).with_rlimit(Some(used - 1)));
    let _scope = short.enter();
    assert!(matches!(
        check(&problem, &derivation),
        Err(Error::Resource | Error::Stopped)
    ));
}

#[test]
fn one_shot_nested_refusal_cannot_be_revived_by_callback_replacement() {
    let armed = Arc::new(AtomicBool::new(false));
    let original = Arc::clone(&armed);
    let _outer = enter_check_stop(Arc::new(move || original.swap(false, Ordering::AcqRel)));
    let mut owner = Owner::capture().expect("owner");
    {
        let _nested = owner.enter();
        armed.store(true, Ordering::Release);
        assert!(ay_core::resource::check_stop_requested());
    }
    let _replacement = enter_check_stop(Arc::new(|| false));
    assert_eq!(owner.poll(), Err(Error::Stopped));
    assert_eq!(owner.admit(1, 0), Err(Error::Stopped));
}

#[test]
fn caught_callback_panic_and_recursive_false_return_are_sticky() {
    for panics in [false, true] {
        let armed = Arc::new(AtomicBool::new(false));
        let original = Arc::clone(&armed);
        let _outer = enter_check_stop(Arc::new(move || {
            if original.swap(false, Ordering::AcqRel) {
                assert!(!panics, "original callback unwind");
                assert!(ay_core::resource::check_stop_requested());
            }
            false
        }));
        let mut owner = Owner::capture().expect("owner");
        armed.store(true, Ordering::Release);
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| owner.poll()));
        assert!(if panics {
            result.is_err()
        } else {
            matches!(result, Ok(Err(Error::Stopped)))
        });
        assert_eq!(owner.poll(), Err(Error::Stopped));
    }
}

#[test]
fn memory_and_original_deadline_are_not_renewed() {
    let (problem, derivation) = evidence(10);
    {
        let _memory = crate::smt::SmtContext::scoped_thread_term_memory_budget(Some(128));
        let mut owner = Owner::capture().expect("nonzero owner");
        assert_eq!(
            validate(&problem, &derivation, &mut owner),
            Err(Error::Resource)
        );
        assert_eq!(owner.poll(), Err(Error::Resource));
    }
    let _deadline = crate::smt::deadline::ScopedSmtDeadline::install(std::time::Duration::ZERO);
    assert!(Owner::capture().is_err());
}

#[test]
fn owner_without_deadline_does_not_invent_one_or_capture_inner_slice() {
    let mut owner = Owner::capture().expect("owner");
    assert_eq!(owner.remaining(), None);
    {
        let _slice = crate::smt::deadline::ScopedSmtDeadline::install(std::time::Duration::ZERO);
        assert_eq!(owner.poll(), Ok(()));
    }
    assert_eq!(owner.poll(), Ok(()));
}
