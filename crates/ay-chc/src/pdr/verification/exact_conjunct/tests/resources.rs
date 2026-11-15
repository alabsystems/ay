// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::resource::{enter_check_stop, ChildSpec, Guard, NodeLabel};
use std::sync::atomic::{AtomicBool, Ordering};

#[test]
fn original_guard_is_debited_and_short_refusal_cannot_restart() {
    let body = ChcExpr::eq(variable("x", ChcSort::Int), ChcExpr::Int(1));
    let generous = Guard::root_child(ChildSpec::new(NodeLabel::Check).with_rlimit(Some(100_000)));
    let scope = generous.enter();
    assert_eq!(prove(&body, &body), Ok(true));
    let used = generous.ticks();
    assert!(used > 1);
    drop(scope);
    let exact = Guard::root_child(ChildSpec::new(NodeLabel::Check).with_rlimit(Some(used + 1)));
    let scope = exact.enter();
    assert_eq!(prove(&body, &body), Ok(true));
    assert_eq!(exact.ticks(), used);
    drop(scope);
    let short = Guard::root_child(ChildSpec::new(NodeLabel::Check).with_rlimit(Some(used - 1)));
    let scope = short.enter();
    let mut owner = Owner::capture().unwrap();
    assert_eq!(entails(&body, &body, &mut owner), Err(Error::Resource));
    drop(scope);
    let replacement =
        Guard::root_child(ChildSpec::new(NodeLabel::Check).with_rlimit(Some(100_000)));
    let _replacement = replacement.enter();
    assert_eq!(entails(&body, &body, &mut owner), Err(Error::Resource));
    assert_eq!(replacement.ticks(), 0);
}

#[test]
fn captured_callback_cancellation_remains_stopped_after_replacement() {
    let armed = Arc::new(AtomicBool::new(false));
    let original = Arc::clone(&armed);
    let _callback = enter_check_stop(Arc::new(move || original.swap(false, Ordering::AcqRel)));
    let mut owner = Owner::capture().unwrap();
    armed.store(true, Ordering::Release);
    let _replacement = enter_check_stop(Arc::new(|| false));
    assert_eq!(
        entails(&ChcExpr::Bool(true), &ChcExpr::Bool(true), &mut owner),
        Err(Error::Stopped)
    );
    assert_eq!(
        entails(&ChcExpr::Bool(true), &ChcExpr::Bool(true), &mut owner),
        Err(Error::Stopped)
    );
}

#[test]
fn zero_guard_expired_deadline_and_captured_lane_refuse() {
    let zero = Guard::root_child(ChildSpec::new(NodeLabel::Check).with_rlimit(Some(0)));
    let scope = zero.enter();
    assert!(Owner::capture().is_err());
    drop(scope);
    let deadline = crate::smt::deadline::ScopedSmtDeadline::install(std::time::Duration::ZERO);
    assert!(Owner::capture().is_err());
    drop(deadline);
    let token = crate::CancellationToken::new();
    let _lane = crate::smt::deadline::ScopedLaneCancellation::install(token.clone(), None);
    let mut owner = Owner::capture().unwrap();
    token.cancel();
    let _replacement = crate::smt::deadline::ScopedLaneCancellation::install(
        crate::CancellationToken::new(),
        None,
    );
    assert_eq!(
        entails(&ChcExpr::Bool(true), &ChcExpr::Bool(true), &mut owner),
        Err(Error::Stopped)
    );
}

#[test]
fn storage_depth_and_long_names_are_bounded_terminal_refusals() {
    let memory = crate::smt::SmtContext::scoped_thread_term_memory_budget(Some(128));
    let mut owner = Owner::capture().unwrap();
    assert_eq!(
        entails(&ChcExpr::Bool(true), &ChcExpr::Bool(true), &mut owner),
        Err(Error::Resource)
    );
    drop(memory);
    assert_eq!(owner.poll(), Err(Error::Resource));
    let mut deep = ChcExpr::Bool(true);
    for _ in 0..types::MAX_DEPTH {
        deep = op(ChcOp::Not, vec![deep]);
    }
    assert_eq!(prove(&deep, &deep), Err(Error::Resource));
    let long = variable(
        &"x".repeat(crate::expr::MAX_PREPROCESSING_NODES),
        ChcSort::Bool,
    );
    assert_eq!(prove(&long, &long), Err(Error::Resource));
}

#[test]
fn repeated_checks_share_one_original_cumulative_allowance() {
    let guard = Guard::root_child(ChildSpec::new(NodeLabel::Check).with_rlimit(Some(250)));
    let _scope = guard.enter();
    let mut owner = Owner::capture().unwrap();
    let body = ChcExpr::eq(variable("x", ChcSort::Int), ChcExpr::Int(1));
    assert_eq!(entails(&body, &body, &mut owner), Ok(true));
    let mut stopped = false;
    for _ in 0..250 {
        if entails(&body, &body, &mut owner) == Err(Error::Resource) {
            stopped = true;
            break;
        }
    }
    assert!(stopped);
    assert_eq!(owner.poll(), Err(Error::Resource));
}
