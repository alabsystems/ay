// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::resource::{enter_check_stop, ChildSpec, Guard, NodeLabel};
use std::sync::atomic::{AtomicBool, Ordering};

#[test]
fn captured_callback_survives_replacement_and_a_transient_stop_is_terminal() {
    let flag = Arc::new(AtomicBool::new(false));
    let observed = Arc::clone(&flag);
    let entered = enter_check_stop(Arc::new(move || observed.load(Ordering::SeqCst)));
    let mut scope = Scope::new(Limits::default(), &|| true);
    scope.work(1).expect("original caller is open");
    drop(entered);
    let _replacement = enter_check_stop(Arc::new(|| false));
    flag.store(true, Ordering::SeqCst);
    assert_eq!(scope.poll(), Err(Failure::Stopped));
    flag.store(false, Ordering::SeqCst);
    assert_eq!(scope.work(0), Err(Failure::Stopped));
}

#[test]
fn a_caught_original_callback_panic_never_reopens_projection() {
    let once = Arc::new(AtomicBool::new(true));
    let observed = Arc::clone(&once);
    let _entered = enter_check_stop(Arc::new(move || {
        assert!(!observed.swap(false, Ordering::SeqCst), "owner panic");
        false
    }));
    let mut scope = Scope::new(Limits::default(), &|| true);
    assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| scope.poll())).is_err());
    assert_eq!(scope.poll(), Err(Failure::Stopped));
}

#[test]
fn every_work_debit_still_reaches_the_original_tree_after_scope_replacement() {
    let owner = Guard::root_child(ChildSpec::new(NodeLabel::Check).with_rlimit(Some(10)));
    let entered = owner.enter();
    let mut scope = Scope::new(Limits::default(), &|| true);
    scope.work(4).expect("first original debit");
    drop(entered);
    let other = Guard::new();
    let _replacement = other.enter();
    scope.work(4).expect("second original debit");
    assert_eq!(scope.work(4), Err(Failure::Stopped));
    assert!(owner.poll().is_some(), "the original allowance was spent");
    assert!(other.poll().is_none(), "no replacement allowance was spent");
    assert_eq!(scope.work(0), Err(Failure::Stopped));
}

#[test]
fn original_tree_cancellation_cannot_be_hidden_by_replacement() {
    let flag = Arc::new(AtomicBool::new(false));
    let owner = Guard::root_child(ChildSpec::new(NodeLabel::Check).with_external(flag.clone()));
    let entered = owner.enter();
    let mut scope = Scope::new(Limits::default(), &|| true);
    scope.poll().expect("open original tree");
    drop(entered);
    let replacement = Guard::new();
    let _entered = replacement.enter();
    flag.store(true, Ordering::SeqCst);
    assert_eq!(scope.poll(), Err(Failure::Stopped));
    flag.store(false, Ordering::SeqCst);
    assert_eq!(scope.poll(), Err(Failure::Stopped));
}

#[test]
fn actual_projection_observes_the_explicit_caller_and_original_work_budget() {
    let formula = ChcExpr::Bool(true);
    {
        let _entered = enter_check_stop(Arc::new(|| true));
        assert!(matches!(project(&formula, &[]), Projection::Stopped));
    }
    {
        let owner = Guard::root_child(ChildSpec::new(NodeLabel::Check).with_rlimit(Some(1)));
        let _entered = owner.enter();
        assert!(matches!(project(&formula, &[]), Projection::Stopped));
    }
    assert!(matches!(
        project(&formula, &[]),
        Projection::Closed(ChcExpr::Bool(true))
    ));
}

#[test]
fn restoring_deadline_tls_during_a_callback_cannot_renew_projection() {
    use crate::smt::ScopedSmtDeadline;
    use std::sync::Mutex;
    use std::time::Duration;

    let deadline = ScopedSmtDeadline::install(Duration::ZERO);
    let original = Arc::new(Mutex::new(Some(deadline)));
    let observed = Arc::clone(&original);
    let callback = enter_check_stop(Arc::new(move || {
        // Remove the expired TLS scope before the projector's ambient poll.
        // Its independently captured entry deadline must still be binding.
        drop(observed.lock().expect("deadline lock").take());
        false
    }));
    assert!(matches!(
        project(&ChcExpr::Bool(true), &[]),
        Projection::Stopped
    ));
    assert!(original.lock().expect("deadline lock").is_none());
    drop(callback);
    assert!(matches!(
        project(&ChcExpr::Bool(true), &[]),
        Projection::Closed(ChcExpr::Bool(true))
    ));
}
