// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::resource::{enter_check_stop, ChildSpec, Guard, NodeLabel};
use std::sync::atomic::{AtomicUsize, Ordering};

fn bv(value: u128) -> ChcExpr {
    ChcExpr::BitVec(value, 2)
}

fn facts_and_head() -> (ChcExpr, ChcExpr) {
    let x = variable("x", ChcSort::BitVec(2));
    let y = variable("y", ChcSort::BitVec(2));
    let z = variable("z", ChcSort::BitVec(2));
    (
        op(
            ChcOp::And,
            vec![ChcExpr::eq(x.clone(), y.clone()), ChcExpr::eq(y, z.clone())],
        ),
        ChcExpr::eq(z, x),
    )
}

fn application_head() -> (ChcExpr, ChcExpr) {
    let x = variable("x", ChcSort::BitVec(2));
    let y = variable("y", ChcSort::BitVec(2));
    let body = ChcExpr::eq(x.clone(), y.clone());
    let head = ChcExpr::eq(
        op(ChcOp::BvAdd, vec![x, bv(1)]),
        op(ChcOp::BvAdd, vec![y, bv(1)]),
    );
    (body, head)
}

#[test]
fn original_fact_unions_prove_reversed_transitive_equalities() {
    let (body, head) = facts_and_head();
    assert_eq!(prove(&body, &head), Ok(true));
    assert_eq!(prove(&body, &ChcExpr::not(head)), Ok(false));
}

#[test]
fn a_completed_signature_pass_proves_the_requested_application_equality() {
    let (body, head) = application_head();
    assert_eq!(prove(&body, &head), Ok(true));
    let x = variable("x", ChcSort::BitVec(2));
    let y = variable("y", ChcSort::BitVec(2));
    let different = ChcExpr::eq(
        op(ChcOp::BvAdd, vec![x, bv(1)]),
        op(ChcOp::BvSub, vec![y, bv(1)]),
    );
    assert_eq!(prove(&body, &different), Ok(false));
}

#[test]
fn an_unproved_intermediate_head_continues_to_later_rule_passes() {
    let (body, equality) = application_head();
    // Signature merging establishes the inner equality. A subsequent rule
    // pass must still propagate its truth through both negations.
    let head = op(ChcOp::Not, vec![op(ChcOp::Not, vec![equality])]);
    assert_eq!(prove(&body, &head), Ok(true));
    assert_eq!(prove(&body, &ChcExpr::not(head)), Ok(false));
}

#[test]
fn an_early_provable_head_still_requires_all_source_typing() {
    let (body, head) = facts_and_head();
    let invalid = op(
        ChcOp::BvAdd,
        vec![ChcExpr::BitVec(0, 2), ChcExpr::BitVec(0, 3)],
    );
    let hidden = ChcExpr::eq(invalid.clone(), invalid);
    let complete_body = op(ChcOp::And, vec![body, hidden]);
    assert_eq!(prove(&complete_body, &head), Ok(false));
}

#[test]
fn early_positive_completion_retains_every_original_cancellation_cut() {
    let (body, head) = facts_and_head();
    let polls = Arc::new(AtomicUsize::new(0));
    let observed = polls.clone();
    let callback = enter_check_stop(Arc::new(move || {
        observed.fetch_add(1, Ordering::Relaxed);
        false
    }));
    assert_eq!(prove(&body, &head), Ok(true));
    let total = polls.load(Ordering::Relaxed);
    drop(callback);
    assert!(total > 1);
    for stop_at in 2..=total {
        let polls = Arc::new(AtomicUsize::new(0));
        let observed = polls.clone();
        let _callback = enter_check_stop(Arc::new(move || {
            observed.fetch_add(1, Ordering::Relaxed) + 1 == stop_at
        }));
        if let Ok(mut owner) = Owner::capture() {
            assert_eq!(entails(&body, &head, &mut owner), Err(Error::Stopped));
            let _replacement = enter_check_stop(Arc::new(|| false));
            assert_eq!(entails(&body, &head, &mut owner), Err(Error::Stopped));
        }
    }
}

#[test]
fn a_short_work_owner_cannot_publish_an_early_positive_result() {
    let (body, head) = facts_and_head();
    let generous = Guard::root_child(ChildSpec::new(NodeLabel::Check).with_rlimit(Some(100_000)));
    let entered = generous.enter();
    assert_eq!(prove(&body, &head), Ok(true));
    let used = generous.ticks();
    assert!(used > 1);
    drop(entered);

    let short = Guard::root_child(ChildSpec::new(NodeLabel::Check).with_rlimit(Some(used - 1)));
    let _entered = short.enter();
    let mut owner = Owner::capture().unwrap();
    assert_eq!(entails(&body, &head, &mut owner), Err(Error::Resource));
    assert_eq!(entails(&body, &head, &mut owner), Err(Error::Resource));
}
