// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::original_query::StopReason;
use crate::resource::{ChildSpec, DeadlineSource, Exhausted, Guard, LiveDeadline, NodeLabel};

#[test]
fn genuine_expired_end_refuses_before_observing_and_never_renews() {
    let end = Instant::now();
    let calls = Arc::new(AtomicUsize::new(0));
    let observed = Arc::clone(&calls);
    let owner = CountedAdmission::new(
        FiniteAdmissionGrant::new(10, 10),
        Some(end),
        Arc::new(move || {
            observed.fetch_add(1, Ordering::SeqCst);
            false
        }),
    )
    .unwrap();
    let expected = CountedAdmissionError::Original(OriginalAdmissionError::Query(
        QueryError::Interrupted(StopReason::Deadline),
    ));
    assert_eq!(owner.deadline(), Some(end));
    assert_eq!(owner.admit(1, 1), Err(expected));
    assert_eq!(owner.clone().check(), Err(expected));
    assert_eq!(calls.load(Ordering::SeqCst), 0);
}

#[test]
fn original_guard_deadline_only_tightens_and_cannot_be_extended() {
    let original_end = end();
    let cell = LiveDeadline::new(Some(original_end));
    let guard = Guard::root_child(
        ChildSpec::new(NodeLabel::Check).with_deadline(DeadlineSource::Live(cell.clone())),
    );
    let scope = guard.enter();
    let owner = CountedAdmission::new(
        FiniteAdmissionGrant::new(10, 10),
        Some(original_end + Duration::from_secs(20)),
        Arc::new(|| false),
    )
    .unwrap();
    assert_eq!(owner.deadline(), Some(original_end));
    cell.set(Some(original_end + Duration::from_secs(60)));
    assert_eq!(owner.deadline(), Some(original_end));
    owner.admit(1, 1).unwrap();
    cell.set(Some(Instant::now()));
    drop(scope);
    assert_eq!(
        owner.check(),
        Err(CountedAdmissionError::Guard(Exhausted::Deadline))
    );
    cell.set(None);
    assert_eq!(
        owner.clone().check(),
        Err(CountedAdmissionError::Guard(Exhausted::Deadline))
    );
}

#[test]
fn current_expired_guard_is_seen_before_a_callback_can_erase_its_scope() {
    let calls = Arc::new(AtomicUsize::new(0));
    let observed = Arc::clone(&calls);
    let owner = CountedAdmission::new(
        FiniteAdmissionGrant::new(2, 2),
        None,
        Arc::new(move || {
            observed.fetch_add(1, Ordering::SeqCst);
            false
        }),
    )
    .unwrap();
    let guard = Guard::root_child(
        ChildSpec::new(NodeLabel::Check).with_deadline(DeadlineSource::Fixed(Instant::now())),
    );
    let scope = guard.enter();
    assert_eq!(
        owner.admit(1, 1),
        Err(CountedAdmissionError::Guard(Exhausted::Deadline))
    );
    drop(scope);
    assert_eq!(calls.load(Ordering::SeqCst), 0);
    assert_eq!(
        owner.check(),
        Err(CountedAdmissionError::Guard(Exhausted::Deadline))
    );
}
