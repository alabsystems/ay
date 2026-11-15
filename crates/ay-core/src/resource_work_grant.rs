// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A counted work grant for the work running on this thread
//! (`ay_core::resource`).
//!
//! A wall-clock budget stops a solve wherever the clock runs out. On a loaded
//! host that is an earlier round than on an idle one, and every term, lemma and
//! conflict minted after that point differs with it, so one query takes a
//! different path on every run. A grant counted in DPLL(T) split-loop round
//! trips stops at the same round on every host.
//!
//! The grant is a GuardTree node (step S2, `guard_tree/cap.rs`): a child of
//! the thread's current node, entered on the thread. Every split loop
//! reports its round trips through [`super::WorkLedger::note_round_trip`],
//! which charges them to the reporting thread's current node and its
//! ancestors, and a solve runs its loops on the thread that called it (or in
//! a node below it). Grants nest: a grant entered inside another is spent
//! when either one is, so the enclosing grant also bounds everything nested
//! inside it.
//!
//! Nothing here decides an answer. A loop whose grant is spent ends the way it
//! ends at a deadline, with "no answer".

use std::cell::Cell;

use super::guard_tree::{current_cap_reached, enter_cap, CapKind, WorkCap};
use super::{EnterScope, NodeLabel};

thread_local! {
    /// Split-loop round trips started on this thread; monotone.
    static ROUND_TRIPS: Cell<u64> = const { Cell::new(0) };
}

/// Count one split-loop round trip on this thread.
pub(super) fn note_thread_round_trip() {
    let _ = ROUND_TRIPS.try_with(|count| count.set(count.get().saturating_add(1)));
}

/// Split-loop round trips started on this thread so far; monotone. The
/// difference of two readings is the work this thread ran between them.
#[must_use]
pub fn thread_round_trips() -> u64 {
    ROUND_TRIPS.try_with(Cell::get).unwrap_or(0)
}

/// An active work grant: its node, entered on this thread. Dropping it
/// closes the grant, and the enclosing grant, if any, is the one in force
/// again. It is bound to the thread that entered it (`!Send`).
#[must_use = "the work grant ends when this scope is dropped"]
pub struct WorkGrantScope {
    scope: EnterScope,
}

impl WorkGrantScope {
    /// Round trips charged to the grant since it was entered, nested work
    /// included. One past the grant when a loop was stopped by it.
    #[must_use]
    pub fn spent_round_trips(&self) -> u64 {
        self.scope.guard().ledger().split_round_trips
    }
}

/// Grant the work this thread runs until the returned scope is dropped
/// `round_trips` split-loop round trips.
///
/// A split loop polls its stops at the top of a round, BEFORE it charges the
/// round trip, so the round trip after the last granted one still starts and
/// is charged, and [`work_grant_spent`] is true from then on: that round ends
/// at its first stop poll inside (its SAT solve, a theory check), or the next
/// loop-top poll ends the loop before it charges again. A loop stopped by its
/// grant has charged exactly `round_trips + 1`.
pub fn enter_work_grant(round_trips: u64) -> WorkGrantScope {
    WorkGrantScope {
        scope: enter_cap(NodeLabel::Grant, Some(WorkCap::RoundTrips(round_trips))),
    }
}

/// Whether a work grant over this thread's current node is spent: its own,
/// or one around it. False when no grant is active; one atomic load while no
/// grant is open in the process. Poll it only where an early end is a sound
/// "no answer", like a deadline.
#[must_use]
pub fn work_grant_spent() -> bool {
    #[cfg(any(test, feature = "determinism-seams"))]
    super::test_seams::delay_this_stop_poll();
    current_cap_reached(CapKind::RoundTrips)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn run_round_trips(count: u64) {
        for _ in 0..count {
            super::super::work().note_round_trip();
        }
    }

    #[test]
    fn a_grant_admits_exactly_its_round_trips() {
        assert!(!work_grant_spent(), "no grant, nothing spent");
        let grant = enter_work_grant(3);
        run_round_trips(3);
        assert!(
            !work_grant_spent(),
            "the third granted round trip still runs"
        );
        run_round_trips(1);
        assert!(
            work_grant_spent(),
            "the fourth round trip finds the grant spent"
        );
        assert_eq!(grant.spent_round_trips(), 4);
        drop(grant);
        assert!(!work_grant_spent(), "no stop once the grant has ended");
    }

    #[test]
    fn a_nested_grant_is_bounded_by_the_enclosing_one_and_restores_it() {
        let outer = enter_work_grant(5);
        run_round_trips(2);
        {
            let inner = enter_work_grant(10);
            run_round_trips(3);
            assert!(!work_grant_spent(), "five of the outer five");
            run_round_trips(1);
            assert!(work_grant_spent(), "the enclosing grant bounds nested work");
            assert_eq!(inner.spent_round_trips(), 4);
        }
        assert!(work_grant_spent(), "the outer grant stays spent");
        assert_eq!(outer.spent_round_trips(), 6);
        drop(outer);
        let outer = enter_work_grant(5);
        {
            let _inner = enter_work_grant(1);
            run_round_trips(2);
            assert!(
                work_grant_spent(),
                "the tighter nested grant is spent first"
            );
        }
        assert!(!work_grant_spent(), "the outer grant is restored");
        drop(outer);
    }

    #[test]
    fn grants_are_per_thread() {
        let _grant = enter_work_grant(0);
        run_round_trips(1);
        assert!(work_grant_spent());
        let other = std::thread::spawn(|| {
            run_round_trips(1);
            work_grant_spent()
        })
        .join()
        .expect("the other thread finishes");
        assert!(
            !other,
            "another thread's work neither charges nor sees this grant"
        );
    }
}
