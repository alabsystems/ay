// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::time::Duration;

use super::*;

/// The hang detector for waits on something that must happen.
const HANG: Duration = Duration::from_secs(60);

fn far() -> Instant {
    Instant::now() + Duration::from_secs(3600)
}

fn past() -> Instant {
    Instant::now()
        .checked_sub(Duration::from_millis(1))
        .expect("1 millisecond must fit before the current test instant")
}

/// Poll until the poll reads an alarm.
fn arm(poll: &DeadlinePoll) {
    for _ in 0..EXACT_POLLS {
        assert!(!poll.expired());
    }
    assert!(poll.is_armed());
}

#[test]
fn the_alarm_raises_its_flag_once_the_deadline_passes() {
    let deadline = Instant::now() + Duration::from_millis(20);
    let alarm = DeadlineAlarm::arm(deadline);
    assert!(alarm.watched());
    let started = Instant::now();
    while !alarm.raised() {
        assert!(started.elapsed() < HANG, "the deadline flag never rose");
        std::thread::sleep(Duration::from_millis(1));
    }
    assert!(
        Instant::now() >= deadline,
        "the flag rose before the deadline"
    );
    assert!(
        DeadlineAlarm::arm(past()).raised(),
        "a passed deadline at once"
    );
}

#[test]
fn dropping_the_alarm_stops_its_timer() {
    let alarm = DeadlineAlarm::arm(far());
    let flag = alarm.flag();
    assert!(alarm.watched(), "a future deadline arms a timer");
    // Dropping joins the timer thread: a timer that ignored the stop would
    // hold this test for the hour.
    drop(alarm);
    assert!(!flag.load(Ordering::Relaxed));
}

#[test]
fn an_unarmed_poll_reads_the_cell_as_expired_does() {
    let cell = SolveDeadlineCell::new();
    let poll = DeadlinePoll::new(cell.clone());
    assert!(!poll.expired());
    cell.set(Some(past()));
    assert!(poll.expired());
    cell.set(Some(far()));
    assert!(!poll.expired());
    cell.set(None);
    assert!(!poll.expired());
    assert!(!poll.is_armed());
}

#[test]
fn an_armed_poll_sees_a_deadline_set_mid_walk_at_once() {
    let cell = SolveDeadlineCell::new();
    cell.set(Some(far()));
    let poll = DeadlinePoll::new(cell.clone());
    arm(&poll);
    cell.set(Some(past()));
    assert!(poll.expired(), "a moved deadline is read from the cell");
    cell.set(Some(far()));
    assert!(!poll.expired(), "and moved back, too");
    cell.set(None);
    assert!(!poll.expired());
}

#[test]
fn a_poll_armed_without_a_deadline_sees_one_installed() {
    let cell = SolveDeadlineCell::new();
    let poll = DeadlinePoll::new(cell.clone());
    arm(&poll);
    cell.set(Some(past()));
    assert!(poll.expired());
}

/// The alarm, not the walk's callback rate, bounds when an armed poll sees
/// the deadline pass. The poll arms first against a far deadline, so no
/// assertion races the clock; the deadline then moves near, and the poll
/// reads the cell again until it re-arms for it. A host that deschedules the
/// test past the deadline before that is answered by the cell, which this
/// test accepts: what it holds is that no poll answers before the deadline
/// and that one answers after it.
#[test]
fn an_armed_poll_sees_its_deadline_pass() {
    let cell = SolveDeadlineCell::new();
    cell.set(Some(far()));
    let poll = DeadlinePoll::new(cell.clone());
    arm(&poll);
    let deadline = Instant::now() + Duration::from_millis(50);
    cell.set(Some(deadline));
    let started = Instant::now();
    while !poll.expired() {
        assert!(
            started.elapsed() < HANG,
            "an armed poll never saw its deadline"
        );
        std::hint::spin_loop();
    }
    assert!(Instant::now() >= deadline, "seen before the deadline");
}
