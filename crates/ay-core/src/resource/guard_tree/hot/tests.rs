// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::time::Duration;

use super::*;
use crate::resource::{
    current_guard, enter_work_ceiling, work, ChildSpec, DeadlineSource, LiveDeadline, MemoryShare,
    NodeLabel,
};
use crate::time::Instant;

const HOUR: Duration = Duration::from_secs(3600);

/// The executor's shape: a Check node whose external flag is the interrupt
/// and whose deadline is a live cell, a Search child, and a `CancelOnly`
/// Certify grandchild that shares the interrupt.
fn chain(interrupt: &Arc<AtomicBool>, cell: &LiveDeadline) -> (Guard, Guard, Guard) {
    let check = Guard::root_child(
        ChildSpec::new(NodeLabel::Check)
            .with_external(Arc::clone(interrupt))
            .with_deadline(DeadlineSource::Live(cell.clone())),
    );
    let search = check.child(ChildSpec::new(NodeLabel::Search));
    let certify = search.child(
        ChildSpec::new(NodeLabel::Certify)
            .cancel_only()
            .with_external(Arc::clone(interrupt)),
    );
    (check, search, certify)
}

/// Poll through the exact phase and the first strided whole read after it,
/// asserting at every poll that the hot poll answers as `Guard::poll`: the
/// next poll reads whole only if the watch is disturbed.
fn warm(poll: &GuardPoll) {
    for at in 0..=HotStride::EXACT {
        assert_eq!(poll.poll(), poll.guard().poll(), "exact poll {at}");
    }
    assert!(!poll.stride.exact());
}

/// Past the exact phase, the next poll answers as `Guard::poll`, a stop.
fn read_at_once(poll: &GuardPoll, what: &str) -> Exhausted {
    let whole = poll.guard().poll();
    assert!(whole.is_some(), "{what}: the fixture stops the node");
    assert_eq!(poll.poll(), whole, "{what}: read at the next poll");
    assert_eq!(poll.poll(), whole, "{what}: and at the one after");
    whole.unwrap_or(Exhausted::Cancelled)
}

#[test]
fn every_watched_change_is_read_at_the_next_poll_with_guard_polls_reason() {
    type Raise = fn(&Guard, &Guard, &Guard, &Arc<AtomicBool>);
    // The event, and the first node of the chain (0: Check) whose poll it
    // stops: every node below it, the polled ones included, sees it.
    let events: [(&str, Raise, usize); 4] = [
        ("Check cancelled", |check, _, _, _| check.cancel(), 0),
        ("Search cancelled", |_, search, _, _| search.cancel(), 1),
        ("Certify cancelled", |_, _, certify, _| certify.cancel(), 2),
        (
            "interrupt raised",
            |_, _, _, interrupt| interrupt.store(true, Ordering::Relaxed),
            0,
        ),
    ];
    for (what, raise, from) in events {
        for polled in from..3 {
            let interrupt = Arc::new(AtomicBool::new(false));
            let cell = LiveDeadline::new(Some(Instant::now() + HOUR));
            let nodes = chain(&interrupt, &cell);
            let poll = [&nodes.0, &nodes.1, &nodes.2][polled].hot_poll();
            warm(&poll);
            raise(&nodes.0, &nodes.1, &nodes.2, &interrupt);
            assert_eq!(read_at_once(&poll, what), Exhausted::Cancelled);
        }
    }
}

/// A stop an ancestor latched on a flag that is lowered again reaches a
/// `CancelOnly` node through the latch alone: the watch reads latches.
#[test]
fn an_ancestor_latch_outliving_its_flag_is_read_at_the_next_poll() {
    let interrupt = Arc::new(AtomicBool::new(false));
    let cell = LiveDeadline::new(Some(Instant::now() + HOUR));
    let (check, _search, certify) = chain(&interrupt, &cell);
    let poll = certify.hot_poll();
    warm(&poll);
    interrupt.store(true, Ordering::Relaxed);
    assert_eq!(check.exhausted(), Some(Exhausted::Cancelled), "latches");
    interrupt.store(false, Ordering::Relaxed);
    assert_eq!(
        read_at_once(&poll, "latched ancestor"),
        Exhausted::Cancelled
    );
}

/// A moved live deadline is read at the next poll by the nodes that obey
/// it, and is no stop for the `CancelOnly` node that does not.
#[test]
fn a_moved_live_deadline_is_read_at_the_next_poll_where_it_is_obeyed() {
    let interrupt = Arc::new(AtomicBool::new(false));
    let cell = LiveDeadline::new(Some(Instant::now() + HOUR));
    let (check, search, certify) = chain(&interrupt, &cell);
    let polls = [check.hot_poll(), search.hot_poll(), certify.hot_poll()];
    for poll in &polls {
        warm(poll);
    }
    cell.set(Some(Instant::now()));
    for poll in &polls[..2] {
        assert_eq!(read_at_once(poll, "moved deadline"), Exhausted::Deadline);
    }
    assert_eq!(polls[2].poll(), None);
    assert_eq!(certify.poll(), None, "Certify keeps its own envelope");
    cell.set(Some(Instant::now() + HOUR));
    for poll in &polls {
        assert_eq!(poll.poll(), None, "an extension is read at once too");
        assert_eq!(poll.poll(), poll.guard().poll());
    }
}

/// Counts that latch nothing (an allotment spent by `record_ticks`, a work
/// cap reached through a `CancelOnly` node) are read at every poll: a
/// budget is never overrun by a stride.
#[test]
fn counts_are_read_at_every_poll() {
    let budget = Guard::root_child(ChildSpec::new(NodeLabel::Check).with_rlimit(Some(10)));
    let poll = budget.hot_poll();
    warm(&poll);
    budget.record_ticks(9);
    for _ in 0..HotStride::STRIDE * 2 {
        assert_eq!(poll.poll(), None);
    }
    budget.record_ticks(2);
    assert_eq!(read_at_once(&poll, "allotment"), Exhausted::Rlimit);

    let _ceiling = enter_work_ceiling(Some(3));
    let ceiling = current_guard().expect("the ceiling is entered");
    let certify = ceiling.child(ChildSpec::new(NodeLabel::Certify).cancel_only());
    let poll = certify.hot_poll();
    warm(&poll);
    work().add_sat_work(2, 0);
    assert_eq!(poll.poll(), None);
    work().add_sat_work(1, 0);
    assert_eq!(read_at_once(&poll, "work cap"), Exhausted::Rlimit);
}

/// The new "no stop" answer is given only where `Guard::poll` gives it: an
/// unchanged chain stays quiet, and a latch the node does not obey disturbs
/// the watch, is read whole and answers no stop.
#[test]
fn a_quiet_answer_agrees_with_guard_poll() {
    let interrupt = Arc::new(AtomicBool::new(false));
    let cell = LiveDeadline::new(Some(Instant::now() + HOUR));
    let (check, _search, certify) = chain(&interrupt, &cell);
    let poll = certify.hot_poll();
    warm(&poll);
    for at in 0..HotStride::STRIDE * 4 {
        assert_eq!(poll.poll(), None, "quiet poll {at}");
    }
    cell.set(Some(Instant::now()));
    assert_eq!(check.exhausted(), Some(Exhausted::Deadline), "latches");
    assert!(poll.watch.disturbed(), "a new latch disturbs the watch");
    assert_eq!(poll.poll(), None, "Certify does not obey it");
    assert_eq!(certify.poll(), None);
    for _ in 0..HotStride::STRIDE * 2 {
        assert_eq!(poll.poll(), certify.poll());
    }
}

/// What only the clock reveals: read at every poll of a short walk, and
/// within one stride, never later, once the exact phase is over.
#[test]
fn a_clock_condition_is_read_at_once_early_and_within_a_stride_after() {
    let soon = Instant::now() + Duration::from_millis(20);
    let short = Guard::root_child(
        ChildSpec::new(NodeLabel::Check).with_deadline(DeadlineSource::Fixed(soon)),
    );
    let poll = short.hot_poll();
    let early = poll.poll();
    while Instant::now() < soon {
        std::thread::sleep(Duration::from_millis(1));
    }
    if early.is_none() {
        assert_eq!(poll.poll(), Some(Exhausted::Deadline), "an exact poll");
    }

    let at = Instant::now() + Duration::from_millis(500);
    let long = Guard::root_child(
        ChildSpec::new(NodeLabel::Check).with_deadline(DeadlineSource::Fixed(at)),
    );
    let poll = long.hot_poll();
    for _ in 0..HotStride::EXACT {
        if poll.poll().is_some() {
            // A host too slow to warm in 500 ms: the exact phase read it.
            assert!(Instant::now() >= at);
            return;
        }
    }
    while Instant::now() < at {
        std::thread::sleep(Duration::from_millis(1));
    }
    let seen = (1..=HotStride::STRIDE).find(|_| poll.poll().is_some());
    assert!(seen.is_some(), "read within one stride");
    for _ in 0..3 {
        assert_eq!(poll.poll(), Some(Exhausted::Deadline), "and from then on");
    }
}

#[test]
fn a_stride_is_due_at_every_exact_poll_then_once_per_stride() {
    let stride = HotStride::new();
    for at in 0..HotStride::EXACT {
        assert!(stride.exact());
        assert!(stride.due(), "exact poll {at}");
    }
    assert!(!stride.exact());
    for round in 0..3 {
        assert!(stride.due(), "round {round}");
        for _ in 1..HotStride::STRIDE {
            assert!(!stride.due());
        }
    }
    assert!(stride.due());
    assert!(!stride.due());
    stride.again();
    assert!(stride.due(), "again: the next poll is due");
    assert!(!stride.due());
}

/// [`Guard::cancelled`]'s part of a watch, and an extra flag, read no clock:
/// each disturbs the watch at once. (That an undisturbed watch is quiet is
/// pinned through `GuardPoll`'s answers above: the stop epoch is the
/// process's, and another test may write it at any time.)
#[test]
fn a_cancelled_watch_and_an_extra_flag_are_read_at_every_poll() {
    let interrupt = Arc::new(AtomicBool::new(false));
    let cell = LiveDeadline::new(Some(Instant::now()));
    let (_check, search, certify) = chain(&interrupt, &cell);
    let extra = Arc::new(AtomicBool::new(false));
    let watch = HotWatch::new().cancelled_of(&certify).flag(&extra);
    extra.store(true, Ordering::Relaxed);
    assert!(watch.disturbed(), "the extra flag");
    extra.store(false, Ordering::Relaxed);
    interrupt.store(true, Ordering::Relaxed);
    assert!(watch.disturbed(), "the chain's external flag");
    interrupt.store(false, Ordering::Relaxed);
    watch.note();
    search.cancel();
    assert!(watch.disturbed(), "an ancestor's own flag, by the epoch");
    assert!(certify.cancelled().is_some());
}

/// Every write the stop epoch stands for bumps it: a cancel, a latch and a
/// live deadline set are each seen by a watch noted before them.
#[test]
fn every_write_the_epoch_stands_for_bumps_it() {
    let cell = LiveDeadline::new(Some(Instant::now() + HOUR));
    let node = Guard::root_child(
        ChildSpec::new(NodeLabel::Check).with_deadline(DeadlineSource::Live(cell.clone())),
    );
    let watch = HotWatch::new().poll_of(&node);
    let writes: [(&str, &dyn Fn()); 3] = [
        ("deadline set", &|| cell.set(Some(Instant::now()))),
        ("latch", &|| assert!(node.exhausted().is_some())),
        ("cancel", &|| node.cancel()),
    ];
    for (what, write) in writes {
        watch.note();
        write();
        assert!(watch.disturbed(), "{what}");
    }
}

/// A memory share's trip raises its node's own flag from ay-sys (GT8), which
/// bumps no stop epoch: the watch reads that flag itself, at the next poll,
/// on the node and on a `CancelOnly` node below it.
#[test]
fn a_memory_share_trip_is_read_at_the_next_poll() {
    const MIB: usize = 1 << 20;
    let check = Guard::root_child(ChildSpec::new(NodeLabel::Check).with_memory(MemoryShare {
        soft_bytes: MIB,
        hard_bytes: 64 * MIB,
    }));
    let certify = check.child(ChildSpec::new(NodeLabel::Certify).cancel_only());
    let polls = [check.hot_poll(), certify.hot_poll()];
    for poll in &polls {
        warm(poll);
    }
    {
        let _scope = check.enter();
        ay_sys::charge_current_for_testing(2 * MIB);
    }
    for poll in &polls {
        assert_eq!(read_at_once(poll, "memory share"), Exhausted::Memory);
    }
}

/// The polling thread's lane share trips without a flag the watch holds or
/// an epoch bump: the watch reads it itself, at the next poll.
#[test]
fn a_tripped_lane_share_is_read_at_the_next_poll() {
    const MIB: usize = 1 << 20;
    let check = Guard::root_child(ChildSpec::new(NodeLabel::Check).with_lane_share());
    let certify = check.child(ChildSpec::new(NodeLabel::Certify).cancel_only());
    let lane = ay_sys::MemoryGroup::named("lane", MIB, 64 * MIB, Arc::new(AtomicBool::new(false)));
    let seen = std::thread::spawn(move || {
        let _lane = ay_sys::enter_memory_group(lane);
        let polls = [check.hot_poll(), certify.hot_poll()];
        for poll in &polls {
            warm(poll);
        }
        ay_sys::charge_current_for_testing(2 * MIB);
        polls.map(|poll| read_at_once(&poll, "lane share"))
    })
    .join()
    .expect("the lane ran");
    assert_eq!(seen, [Exhausted::Memory; 2]);
}
