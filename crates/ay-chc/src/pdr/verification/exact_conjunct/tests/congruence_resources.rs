// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::resource::{enter_check_stop, ChildSpec, Guard, NodeLabel};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

fn implication() -> (ChcExpr, ChcExpr) {
    let x = variable("x", ChcSort::BitVec(2));
    let y = variable("y", ChcSort::BitVec(2));
    let body = ChcExpr::eq(x.clone(), y.clone());
    let one = op(
        ChcOp::Ite,
        vec![
            op(
                ChcOp::Ne,
                vec![ChcExpr::BitVec(3, 2), ChcExpr::BitVec(0, 2)],
            ),
            op(
                ChcOp::BvMul,
                vec![ChcExpr::BitVec(3, 2), ChcExpr::BitVec(3, 2)],
            ),
            ChcExpr::BitVec(0, 2),
        ],
    );
    let head = ChcExpr::eq(
        op(ChcOp::BvConcat, vec![x, ChcExpr::BitVec(1, 2)]),
        op(ChcOp::BvConcat, vec![y, one]),
    );
    (body, head)
}

#[test]
fn congruence_exact_credit_is_deterministic_and_short_credit_is_terminal() {
    let (body, head) = implication();
    let generous = Guard::root_child(ChildSpec::new(NodeLabel::Check).with_rlimit(Some(100_000)));
    let scope = generous.enter();
    assert_eq!(prove(&body, &head), Ok(true));
    let used = generous.ticks();
    assert!(used > 1);
    drop(scope);
    for _ in 0..3 {
        let exact = Guard::root_child(ChildSpec::new(NodeLabel::Check).with_rlimit(Some(used + 1)));
        let scope = exact.enter();
        assert_eq!(prove(&body, &head), Ok(true));
        assert_eq!(exact.ticks(), used);
        drop(scope);
    }
    let short = Guard::root_child(ChildSpec::new(NodeLabel::Check).with_rlimit(Some(used - 1)));
    let scope = short.enter();
    let mut owner = Owner::capture().unwrap();
    assert_eq!(entails(&body, &head, &mut owner), Err(Error::Resource));
    drop(scope);
    assert_eq!(entails(&body, &head, &mut owner), Err(Error::Resource));
}

#[test]
fn every_new_congruence_poll_can_cancel_without_reviving_the_original_owner() {
    let (body, head) = implication();
    let count = Arc::new(AtomicUsize::new(0));
    let observed = Arc::clone(&count);
    let callback = enter_check_stop(Arc::new(move || {
        observed.fetch_add(1, Ordering::Relaxed);
        false
    }));
    assert_eq!(prove(&body, &head), Ok(true));
    let polls = count.load(Ordering::Relaxed);
    drop(callback);
    assert!(polls > 10);
    for stop_at in 2..=polls {
        let count = Arc::new(AtomicUsize::new(0));
        let observed = Arc::clone(&count);
        let callback = enter_check_stop(Arc::new(move || {
            observed.fetch_add(1, Ordering::Relaxed) + 1 == stop_at
        }));
        // Capture itself may reach stop_at; no replacement owner is allowed.
        if let Ok(mut owner) = Owner::capture() {
            assert_eq!(
                entails(&body, &head, &mut owner),
                Err(Error::Stopped),
                "poll {stop_at}"
            );
            let _replacement = enter_check_stop(Arc::new(|| false));
            assert_eq!(entails(&body, &head, &mut owner), Err(Error::Stopped));
        }
        drop(callback);
    }
}

#[test]
fn closure_growth_admission_uses_the_same_typed_input_owner() {
    let (body, head) = implication();
    let mut owner = Owner::capture().unwrap();
    let mut arena = Arena::new();
    let body = arena.read(&body, 0, &mut owner).unwrap();
    let head = arena.read(&head, 0, &mut owner).unwrap();
    let assumptions = [body].into_iter().collect();
    // Tighten only after the complete typing phase: closure must still admit
    // its own union/find and signature storage against this same owner.
    let memory = crate::smt::SmtContext::scoped_thread_term_memory_budget(Some(1));
    assert_eq!(
        super::super::congruence::entails(&mut arena, head, &assumptions, &mut owner),
        Err(Error::Resource)
    );
    drop(memory);
    assert_eq!(owner.poll(), Err(Error::Resource));
}

#[test]
fn original_callback_is_retained_through_equivalence_rebuilds() {
    let (body, head) = implication();
    let armed = Arc::new(AtomicBool::new(false));
    let original = Arc::clone(&armed);
    let _original = enter_check_stop(Arc::new(move || original.swap(false, Ordering::AcqRel)));
    let mut owner = Owner::capture().unwrap();
    let _replacement = enter_check_stop(Arc::new(|| false));
    armed.store(true, Ordering::Release);
    assert_eq!(entails(&body, &head, &mut owner), Err(Error::Stopped));
    assert_eq!(entails(&body, &head, &mut owner), Err(Error::Stopped));
}
