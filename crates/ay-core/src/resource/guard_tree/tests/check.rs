// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! M1 for step S2: what the executor's Check and Certify nodes read, the
//! reads that latch nothing, and the work caps (`read.rs`, `cap.rs`).

use super::*;
use crate::resource::{
    enter_work_ceiling, enter_work_grant, work, work_ceiling_reached, work_grant_spent,
};

#[test]
fn a_poll_latches_nothing_and_reads_a_moved_deadline_again() {
    let cell = LiveDeadline::new(Some(Instant::now()));
    let check = Guard::root_child(
        ChildSpec::new(NodeLabel::Check).with_deadline(DeadlineSource::Live(cell.clone())),
    );
    assert_eq!(check.poll(), Some(Exhausted::Deadline));
    cell.set(Some(Instant::now() + HOUR));
    assert_eq!(check.poll(), None, "the restore is read");
    assert_eq!(check.stopped(), None);
    cell.set(Some(Instant::now()));
    assert_eq!(check.exhausted(), Some(Exhausted::Deadline), "this latches");
    cell.set(Some(Instant::now() + HOUR));
    assert_eq!(
        check.poll(),
        Some(Exhausted::Deadline),
        "a latch is reported"
    );
}

#[test]
fn the_cancel_chain_reads_flags_and_no_clock() {
    let interrupt = Arc::new(AtomicBool::new(false));
    let check = Guard::root_child(
        ChildSpec::new(NodeLabel::Check)
            .with_external(Arc::clone(&interrupt))
            .with_deadline(DeadlineSource::Fixed(Instant::now())),
    );
    let certify = check.child(
        ChildSpec::new(NodeLabel::Certify)
            .cancel_only()
            .with_deadline(DeadlineSource::Fixed(Instant::now())),
    );
    assert_eq!(certify.cancelled(), None, "neither deadline is a cancel");
    assert_eq!(
        certify.poll(),
        Some(Exhausted::Deadline),
        "its own is a stop"
    );
    interrupt.store(true, Ordering::Relaxed);
    assert_eq!(certify.cancelled(), Some(Exhausted::Cancelled));
    assert_eq!(certify.stopped(), None, "and nothing was latched");
}

#[test]
fn a_lane_share_is_the_polling_threads() {
    const MIB: usize = 1 << 20;
    let check = Guard::root_child(ChildSpec::new(NodeLabel::Check).with_lane_share());
    let certify = check.child(ChildSpec::new(NodeLabel::Certify).cancel_only());
    let lane = ay_sys::MemoryGroup::named("lane", MIB, 64 * MIB, Arc::new(AtomicBool::new(false)));
    let seen = std::thread::spawn(move || {
        let _lane = ay_sys::enter_memory_group(lane);
        let before = (check.poll(), certify.cancelled());
        ay_sys::charge_current_for_testing(2 * MIB);
        (before, check.poll(), certify.cancelled())
    })
    .join()
    .expect("the lane ran");
    assert_eq!(seen.0, (None, None));
    assert_eq!(seen.1, Some(Exhausted::Memory));
    assert_eq!(
        seen.2,
        Some(Exhausted::Memory),
        "Certify sees the trip (DR-39)"
    );
}

#[test]
fn the_nearest_check_and_a_handle_that_does_not_keep_it_open() {
    let check = Guard::root_child(ChildSpec::new(NodeLabel::Check).with_rlimit(Some(80)));
    let share = check.child(ChildSpec::new(NodeLabel::Share));
    let found = share.nearest(NodeLabel::Check).expect("the check is above");
    assert!(same(&found, &check));
    assert_eq!(found.allotment(), Some(80));
    assert!(share.nearest(NodeLabel::Certify).is_none());
    assert!(share.is_within(&check) && share.is_within(&share));
    assert!(!check.is_within(&share), "a parent is not within its child");
    let weak = share.downgrade();
    assert!(weak.upgrade().is_some_and(|open| same(&open, &share)));
    drop(share);
    assert!(weak.upgrade().is_none(), "a weak handle keeps nothing open");
    assert!(WeakGuard::default().upgrade().is_none());
}

#[test]
fn a_work_cap_reaches_through_cancel_only_and_counts_what_runs_below_it() {
    let check = Guard::root_child(ChildSpec::new(NodeLabel::Check));
    let _inside = check.enter();
    let ceiling = enter_work_ceiling(Some(4));
    let certify = current_guard()
        .expect("the ceiling is entered")
        .child(ChildSpec::new(NodeLabel::Certify).cancel_only());
    {
        let _certify = certify.enter();
        let nested = certify.child(ChildSpec::new(NodeLabel::Check));
        let _nested = nested.enter();
        work().add_sat_work(3, 0);
        assert!(!work_ceiling_reached());
        work().note_round_trip();
        assert!(work_ceiling_reached(), "a ceiling bounds certification");
        assert_eq!(nested.poll(), Some(Exhausted::Rlimit));
    }
    assert!(ceiling.spent(), "and counts it (cap.rs)");
    assert_eq!(check.poll(), None, "a cap reaches down, never up");
    assert_eq!(check.ledger().sat_conflicts, 3);
    drop(ceiling);
    assert!(!work_ceiling_reached());
    let grant = enter_work_grant(0);
    assert!(!work_grant_spent());
    work().note_round_trip();
    assert!(work_grant_spent());
    assert!(!work_ceiling_reached(), "a grant is not a ceiling");
    drop(grant);
    assert!(!work_grant_spent());
}

#[test]
fn a_share_of_an_owners_deadline_keeps_a_live_cell_of_its_own() {
    let wall = Instant::now() + HOUR;
    let passed = Instant::now();
    let check = Guard::root_child(
        ChildSpec::new(NodeLabel::Check).with_deadline(DeadlineSource::Fixed(passed)),
    );
    let share = Guard::share_of(Some(&check), Portion::Half, Some(wall))
        .expect("the owner's deadline divides");
    let cell = share.live_deadline().expect("a share's deadline is a cell");
    let half = cell.get().expect("half of the owner's hour");
    assert!(half < wall && half > Instant::now() + HOUR / 3, "{half:?}");
    cell.set(Some(wall));
    assert_eq!(share.deadline(), Some(wall), "its owner moves the share");
    assert_eq!(check.deadline(), Some(passed), "never the parent");
    drop(share);
    assert_eq!(check.ledger().deadline_shares, 1);
    assert_eq!(check.ledger().deadline_shares_spent, 0);

    let lone = Guard::share_of(None, Portion::Half, Some(wall)).expect("below the root");
    assert!(lone.live_deadline().is_some());
    assert!(Guard::share_of(None, Portion::Half, None).is_none());
}

#[test]
fn a_share_closes_spent_when_a_ceiling_over_it_is_reached() {
    let check = Guard::root_child(
        ChildSpec::new(NodeLabel::Check)
            .with_deadline(DeadlineSource::Fixed(Instant::now() + HOUR)),
    );
    let _inside = check.enter();
    let ceiling = enter_work_ceiling(Some(1));
    let in_retry = current_guard()
        .expect("the ceiling is entered")
        .share(Portion::Half)
        .expect("the check's deadline divides");
    work().note_round_trip();
    drop(in_retry);
    assert!(ceiling.spent());
    assert_eq!(check.ledger().deadline_shares, 1);
    assert_eq!(
        check.ledger().deadline_shares_spent,
        1,
        "the executor's deadline polls read a reached ceiling as a passed deadline"
    );
}
