// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A ceiling on the search work of the thread that installs it
//! (`ay_core::resource`).
//!
//! A deadline bounds a solve by the clock, so what it cuts depends on the
//! machine and its load. A work ceiling bounds it by a count of search steps
//! the solve itself makes: one unit per DPLL(T) split-loop round trip and one
//! per CDCL conflict, the same events the [`WorkLedger`](super::WorkLedger)
//! records. The ceiling is a GuardTree node (step S2, `guard_tree/cap.rs`):
//! a child of the thread's current node, entered on the thread, which counts
//! the work charged to it and to the nodes below it. A solve running on
//! another thread of the process neither spends this allowance nor is
//! stopped by it, unless it runs in a node below the ceiling, and the same
//! input stops at the same step on every run.
//!
//! Reaching the ceiling is reported through the same polls as an expired
//! deadline. The contract is the deadline's: a poll that answers "stop" ends
//! the work with a sound "no answer", never with a verdict.

use std::cell::Cell;

use super::guard_tree::{current_cap_reached, enter_cap, CapKind, WorkCap};
use super::{EnterScope, NodeLabel};

thread_local! {
    /// Work units this thread has spent since it started.
    static SPENT: Cell<u64> = const { Cell::new(0) };
}

/// Record `units` of search work on this thread.
pub(super) fn spend(units: u64) {
    let _ = SPENT.try_with(|spent| spent.set(spent.get().saturating_add(units)));
}

/// Work units this thread has spent since it started: split-loop round trips
/// plus CDCL conflicts. Monotone; a caller measures a stretch of work as the
/// difference of two readings.
#[must_use]
pub fn thread_work_units() -> u64 {
    SPENT.try_with(Cell::get).unwrap_or(0)
}

/// Whether a work ceiling over this thread's current node is reached: its
/// own, or one around it. False when none is open; one atomic load while no
/// ceiling is open in the process.
#[must_use]
#[inline]
pub fn work_ceiling_reached() -> bool {
    current_cap_reached(CapKind::Units)
}

/// Keeps a work ceiling's node entered on this thread; dropping it closes
/// the ceiling. Not `Send`: it must be dropped on the thread that entered it.
#[must_use = "the work ceiling is lifted when this scope is dropped"]
pub struct WorkCeilingScope {
    scope: EnterScope,
}

impl WorkCeilingScope {
    /// Whether the work allowed by THIS scope is spent (an enclosing, lower
    /// ceiling can stop the thread earlier without this being true).
    #[must_use]
    pub fn spent(&self) -> bool {
        self.scope.guard().own_cap_reached()
    }
}

/// Allow the work this thread runs `allowance` more work units until the
/// returned scope is dropped (`None`: no limit of its own). A ceiling can
/// only tighten the one around it: every ceiling over the thread's current
/// node applies, so the first one reached stops it.
pub fn enter_work_ceiling(allowance: Option<u64>) -> WorkCeilingScope {
    WorkCeilingScope {
        scope: enter_cap(NodeLabel::Ceiling, allowance.map(WorkCap::Units)),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::resource::{current_guard, work, ChildSpec, NodeLabel};

    /// Report `units` conflicts on this thread, as a solver does.
    fn spend(units: u64) {
        work().add_sat_work(units, 0);
    }

    #[test]
    fn a_ceiling_is_reached_by_the_work_of_its_own_thread() {
        assert!(
            !work_ceiling_reached(),
            "no ceiling is installed by default"
        );
        let before = thread_work_units();
        let scope = enter_work_ceiling(Some(3));
        spend(2);
        assert!(!work_ceiling_reached());
        assert!(!scope.spent());
        // Work on another thread spends nothing here and is not stopped here.
        std::thread::spawn(|| {
            spend(1_000);
            assert!(!work_ceiling_reached());
        })
        .join()
        .expect("the other thread ran");
        assert!(!work_ceiling_reached());
        spend(1);
        assert!(work_ceiling_reached());
        assert!(scope.spent());
        assert_eq!(thread_work_units() - before, 3);
        drop(scope);
        assert!(!work_ceiling_reached(), "the ceiling ends with its scope");
    }

    #[test]
    fn a_worker_below_the_ceiling_spends_it_and_is_stopped_by_it() {
        let scope = enter_work_ceiling(Some(3));
        let lane = current_guard()
            .expect("the ceiling is entered")
            .child(ChildSpec::new(NodeLabel::Search));
        let stopped = std::thread::spawn(move || {
            let _inside = lane.enter();
            spend(3);
            work_ceiling_reached()
        })
        .join()
        .expect("the worker ran");
        assert!(stopped, "a worker in a node below the ceiling is stopped");
        assert!(scope.spent(), "and its work spent the allowance (GT4, GT5)");
    }

    #[test]
    fn an_allowance_of_one_unit_less_is_not_spent() {
        let scope = enter_work_ceiling(Some(3));
        spend(2);
        assert!(!scope.spent());
        assert!(!work_ceiling_reached());
    }

    #[test]
    fn a_nested_ceiling_only_tightens_and_the_outer_one_is_restored() {
        let outer = enter_work_ceiling(Some(10));
        {
            // A wider inner allowance does not lift the outer ceiling.
            let wide = enter_work_ceiling(Some(1_000));
            spend(10);
            assert!(work_ceiling_reached(), "the outer ceiling still applies");
            assert!(!wide.spent(), "but the inner allowance is not spent");
        }
        assert!(outer.spent());
        drop(outer);
        let outer = enter_work_ceiling(Some(10));
        {
            let tight = enter_work_ceiling(Some(2));
            spend(2);
            assert!(work_ceiling_reached());
            assert!(tight.spent());
            assert!(!outer.spent());
        }
        assert!(
            !work_ceiling_reached(),
            "the outer ceiling is back in force"
        );
        let unlimited = enter_work_ceiling(None);
        spend(8);
        assert!(
            work_ceiling_reached(),
            "no limit of its own keeps the outer one"
        );
        assert!(!unlimited.spent());
    }

    #[test]
    fn the_ledger_spends_round_trips_and_conflicts_not_decisions() {
        let before = thread_work_units();
        let scope = enter_work_ceiling(Some(6));
        work().note_round_trip();
        work().add_sat_work(4, 900);
        assert_eq!(thread_work_units() - before, 5);
        assert!(!scope.spent());
        work().note_round_trip();
        assert!(scope.spent());
    }
}
