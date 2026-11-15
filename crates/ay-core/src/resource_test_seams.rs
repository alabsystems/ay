// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Determinism seams (`ay_core::resource`): ways for a test to make the host
//! look slower without changing what the solver computes.
//!
//! A verdict is deterministic when it is a function of the query and its
//! counts alone. The way to show it is to run the same query on a "slow host"
//! and compare. Sleeping where a test happens to poll does not do that: a
//! sleep in the test's own poll never reaches the solver's clocks. The seams
//! sleep INSIDE solver work instead, at three places, so the clocks the solver
//! reads see the slowdown while every count it keeps stays the same:
//!
//! * once per DPLL(T) split-loop round trip
//!   ([`super::WorkLedger::note_round_trip`]): a clock read between rounds
//!   (deadlines, slices measured against an earlier solve) sees it;
//! * once per executor stop poll inside a SAT search ([`super::work_grant_spent`],
//!   which every executor stop closure polls, every 100 conflicts and 1000
//!   decisions): the solve deadline and other external stop controls see
//!   time spent inside the search;
//! * once per meter charge ([`super::Guard::record_ticks`]): ay-chc's CHC run
//!   charges its node at every SMT entry, DPLL(T) round, SAT solve, PDR
//!   iteration and proof obligation (the development design notes §13), so a
//!   clock ay-chc reads between two of them (a per-query slice, a frame-stall
//!   window, the solve deadline) sees the slowdown. One sleep per charge,
//!   whatever its cost, and none inside a SAT solve or an executor sub-check:
//!   a clock read only there sees no slowdown from this seam (the census's
//!   lower bound, the development design notes);
//! * per tick a node is charged on the thread ([`super::Guard::tick`] and
//!   [`super::Guard::record_ticks`]), scaled by the cost
//!   ([`delay_each_tick_picos`]): the slow host of ay-chc's CHC run under an
//!   effort (P4a slice 8), where a SAT solve's ticks cost as much more as its
//!   search did. ay-chc's own SAT stop polls ([`super::note_sat_stop_poll`])
//!   take the stop-poll delay as the executor's do, so a clock read inside
//!   one of its solves sees the slowdown too.
//!
//! [`shrink_round_slices`] divides that arm's counted slices, so a fixture of
//! a few seconds reaches a round its own slice stops.
//!
//! Compiled only for tests and under the `determinism-seams` feature; nothing
//! in a production build can reach it.

use std::cell::Cell;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant};

/// The delay per round trip, in nanoseconds; zero means none.
static ROUND_TRIP_DELAY_NANOS: AtomicU64 = AtomicU64::new(0);

/// Sleep `delay` inside every split-loop round trip from now on, on every
/// thread of the process (`Duration::ZERO` switches the seam off). Process-
/// wide on purpose: a solve's nested lanes run where it runs, and a test that
/// sets a delay owns its process (an integration-test binary of its own).
pub fn delay_each_round_trip(delay: Duration) {
    let nanos = u64::try_from(delay.as_nanos()).unwrap_or(u64::MAX);
    ROUND_TRIP_DELAY_NANOS.store(nanos, Ordering::Relaxed);
}

/// The delay currently installed by [`delay_each_round_trip`].
#[must_use]
pub fn round_trip_delay() -> Duration {
    Duration::from_nanos(ROUND_TRIP_DELAY_NANOS.load(Ordering::Relaxed))
}

/// One round trip's share of the slowdown (called by the ledger).
pub(super) fn delay_this_round_trip() {
    let nanos = ROUND_TRIP_DELAY_NANOS.load(Ordering::Relaxed);
    if nanos != 0 {
        std::thread::sleep(Duration::from_nanos(nanos));
    }
}

/// The delay per stop poll, in nanoseconds; zero means none.
static STOP_POLL_DELAY_NANOS: AtomicU64 = AtomicU64::new(0);
/// Stop polls this process has made, so a test can size a delay per poll.
static STOP_POLLS: AtomicU64 = AtomicU64::new(0);

/// Sleep `delay` inside every executor stop poll from now on, on every thread
/// of the process (`Duration::ZERO` switches the seam off). Process-wide, as
/// [`delay_each_round_trip`] is.
pub fn delay_each_stop_poll(delay: Duration) {
    let nanos = u64::try_from(delay.as_nanos()).unwrap_or(u64::MAX);
    STOP_POLL_DELAY_NANOS.store(nanos, Ordering::Relaxed);
}

/// The delay currently installed by [`delay_each_stop_poll`].
#[must_use]
pub fn stop_poll_delay() -> Duration {
    Duration::from_nanos(STOP_POLL_DELAY_NANOS.load(Ordering::Relaxed))
}

/// Stop polls made so far in this process; the difference of two readings is
/// the polls a solve made between them.
#[must_use]
pub fn stop_polls() -> u64 {
    STOP_POLLS.load(Ordering::Relaxed)
}

/// One stop poll's share of the slowdown (called by [`super::work_grant_spent`]).
pub(super) fn delay_this_stop_poll() {
    STOP_POLLS.fetch_add(1, Ordering::Relaxed);
    let nanos = STOP_POLL_DELAY_NANOS.load(Ordering::Relaxed);
    if nanos != 0 {
        std::thread::sleep(Duration::from_nanos(nanos));
    }
}

/// The delay per meter charge, in nanoseconds; zero means none.
static CHARGE_DELAY_NANOS: AtomicU64 = AtomicU64::new(0);
/// Meter charges this process has made, so a test can size a delay per charge.
static CHARGES: AtomicU64 = AtomicU64::new(0);

/// Sleep `delay` inside every meter charge ([`super::Guard::record_ticks`])
/// from now on, on every thread of the process (`Duration::ZERO` switches the
/// seam off). Process-wide, as [`delay_each_round_trip`] is.
pub fn delay_each_charge(delay: Duration) {
    let nanos = u64::try_from(delay.as_nanos()).unwrap_or(u64::MAX);
    CHARGE_DELAY_NANOS.store(nanos, Ordering::Relaxed);
}

/// The delay currently installed by [`delay_each_charge`].
#[must_use]
pub fn charge_delay() -> Duration {
    Duration::from_nanos(CHARGE_DELAY_NANOS.load(Ordering::Relaxed))
}

/// Meter charges made so far in this process; the difference of two readings
/// is the charges a run made between them.
#[must_use]
pub fn charges() -> u64 {
    CHARGES.load(Ordering::Relaxed)
}

/// One meter charge's share of the slowdown (called by [`super::Guard::record_ticks`]).
pub(super) fn delay_this_charge() {
    CHARGES.fetch_add(1, Ordering::Relaxed);
    let nanos = CHARGE_DELAY_NANOS.load(Ordering::Relaxed);
    if nanos != 0 {
        std::thread::sleep(Duration::from_nanos(nanos));
    }
}

/// Owed delay below which a thread does not sleep yet, in picoseconds: a
/// sleep of a few microseconds overshoots by more than it asks for.
const TICK_DEBT_SLEEP_PICOS: i128 = 200_000_000;
/// The longest one nap of the tick seam, so a saturating cost cannot sleep
/// for years.
const TICK_NAP_CAP: Duration = Duration::from_secs(1);

thread_local! {
    /// The delay per tick on this thread, in picoseconds; zero means none.
    static TICK_DELAY_PICOS: Cell<u64> = const { Cell::new(0) };
    /// Delay this thread's ticks owe and have not slept yet, in picoseconds
    /// (negative: a nap overshot, and later ticks pay it back first).
    static TICK_DEBT_PICOS: Cell<i128> = const { Cell::new(0) };
}

/// Sleep `picos` picoseconds for every tick a node is charged ON THIS THREAD
/// from now on (0 switches the seam off): in [`super::Guard::tick`] and
/// [`super::Guard::record_ticks`], scaled by the cost, so a SAT solve that
/// charges 10,000 ticks naps 10,000 times longer than an SMT entry that
/// charges 1. The thread naps once it owes at least 200 microseconds, for
/// what it owes (one nap at most a second), and pays any overshoot back from
/// later ticks, so the slowdown is proportional on average. ay-chc's slow host
/// under an effort (P4a slice 8): with [`delay_each_charge`]'s fixed nap a SAT
/// solve naps as long as an SMT entry, so the host it slows is not uniformly
/// slower. Per thread, unlike the other seams, because a CHC proof run is one
/// thread's work and the guard tree's own tests tick saturating costs on
/// others.
pub fn delay_each_tick_picos(picos: u64) {
    let _ = TICK_DELAY_PICOS.try_with(|delay| delay.set(picos));
    let _ = TICK_DEBT_PICOS.try_with(|debt| debt.set(0));
}

/// The delay per tick [`delay_each_tick_picos`] installed on this thread.
#[must_use]
pub fn tick_delay_picos() -> u64 {
    TICK_DELAY_PICOS.try_with(Cell::get).unwrap_or(0)
}

/// `cost` ticks' share of this thread's slowdown (called by
/// [`super::Guard::tick`] and [`super::Guard::record_ticks`]).
pub(super) fn delay_these_ticks(cost: u64) {
    let picos = tick_delay_picos();
    if picos == 0 || cost == 0 {
        return;
    }
    let _ = TICK_DEBT_PICOS.try_with(|debt| {
        let owed = debt
            .get()
            .saturating_add(i128::from(cost).saturating_mul(i128::from(picos)));
        if owed < TICK_DEBT_SLEEP_PICOS {
            debt.set(owed);
            return;
        }
        let nap =
            Duration::from_nanos(u64::try_from(owed / 1_000).unwrap_or(u64::MAX)).min(TICK_NAP_CAP);
        let started = Instant::now();
        std::thread::sleep(nap);
        let slept = i128::try_from(started.elapsed().as_nanos()).unwrap_or(i128::MAX);
        // What a capped nap left unpaid is dropped, not carried.
        let left = owed.min(i128::try_from(TICK_NAP_CAP.as_nanos()).unwrap_or(i128::MAX) * 1_000);
        debt.set(left.saturating_sub(slept.saturating_mul(1_000)));
    });
}

/// What the eager-persistent arm's counted slices are divided by; 1 is none.
static ROUND_SLICE_DIVISOR: AtomicU64 = AtomicU64::new(1);

/// Divide every counted slice of the eager-persistent split-loop arm by
/// `divisor` from now on, on every thread of the process (1 switches the seam
/// off; 0 counts as 1). The arm then stops rounds on their slices sooner, on
/// the same counts on every host: a test reaches the slice path on a fixture
/// of seconds. The search's `:rlimit` allowance is not divided.
pub fn shrink_round_slices(divisor: u64) {
    ROUND_SLICE_DIVISOR.store(divisor.max(1), Ordering::Relaxed);
}

/// [`super::round_seam::slice_divisor`] under the seam.
pub(super) fn round_slice_divisor() -> u64 {
    ROUND_SLICE_DIVISOR.load(Ordering::Relaxed).max(1)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn the_seam_sleeps_inside_a_round_trip_and_switches_off() {
        delay_each_round_trip(Duration::from_millis(5));
        assert_eq!(round_trip_delay(), Duration::from_millis(5));
        let started = std::time::Instant::now();
        crate::resource::work().note_round_trip();
        assert!(started.elapsed() >= Duration::from_millis(5));
        delay_each_round_trip(Duration::ZERO);
        assert_eq!(round_trip_delay(), Duration::ZERO);
    }

    #[test]
    fn the_stop_poll_seam_counts_and_sleeps_inside_a_poll_and_switches_off() {
        delay_each_stop_poll(Duration::from_millis(5));
        assert_eq!(stop_poll_delay(), Duration::from_millis(5));
        let before = stop_polls();
        let started = std::time::Instant::now();
        let _ = crate::resource::work_grant_spent();
        assert!(started.elapsed() >= Duration::from_millis(5));
        assert!(stop_polls() > before);
        delay_each_stop_poll(Duration::ZERO);
        assert_eq!(stop_poll_delay(), Duration::ZERO);
    }

    #[test]
    fn the_charge_seam_counts_and_sleeps_inside_a_charge_and_switches_off() {
        delay_each_charge(Duration::from_millis(5));
        assert_eq!(charge_delay(), Duration::from_millis(5));
        let before = charges();
        let started = Instant::now();
        crate::resource::Guard::new().record_ticks(1);
        assert!(started.elapsed() >= Duration::from_millis(5));
        assert!(charges() > before);
        delay_each_charge(Duration::ZERO);
        assert_eq!(charge_delay(), Duration::ZERO);
    }

    #[test]
    fn the_tick_seam_sleeps_in_proportion_to_the_ticks_and_switches_off() {
        // 50 microseconds a tick: 3 ticks owe less than the 200 microseconds a
        // thread waits to owe, so they nap with the 5 after them, 400 in all.
        delay_each_tick_picos(50_000_000);
        assert_eq!(tick_delay_picos(), 50_000_000);
        let node = crate::resource::Guard::new();
        let started = Instant::now();
        node.record_ticks(3);
        let _ = node.tick(5);
        assert!(started.elapsed() >= Duration::from_micros(400));
        delay_each_tick_picos(0);
        let started = Instant::now();
        let _ = node.tick(1_000_000);
        assert!(
            started.elapsed() < Duration::from_secs(1),
            "off: no nap, however many ticks"
        );
    }

    #[test]
    fn the_slice_divisor_is_one_unless_a_test_shrinks_the_slices() {
        use crate::resource::round_seam;
        assert_eq!(round_seam::slice_divisor(), 1);
        shrink_round_slices(16);
        assert_eq!(round_seam::slice_divisor(), 16);
        shrink_round_slices(0);
        assert_eq!(round_seam::slice_divisor(), 1, "0 counts as 1");
        shrink_round_slices(1);
    }
}
