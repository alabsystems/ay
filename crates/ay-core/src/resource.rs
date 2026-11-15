// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Process-wide resource ledger (roadmap D5, engine design §3.9 R1).
//!
//! One owner for what a run has spent and where it is, readable from any
//! thread. Two readers need it:
//!
//! * the statistics block of a check-sat, which reports the work of EVERY lane
//!   the check ran (a lane's own `:conflicts` and `dpll.round_trips` describe
//!   the last lane only, and are overwritten by each lane in turn);
//! * the CLI watchdog that ends a run whose solve did not stop within the
//!   grace after its deadline. It runs on its own thread and cannot reach the
//!   executor, so without this ledger the run left no statistics at all.
//!
//! The counters are monotone, process-wide totals. The ledger and the
//! process cancel are the root of the GuardTree (`guard_tree`,
//! the development design notes step S1): the statics below the wrappers are
//! the root node's storage, and every node's ledger adds into the process
//! ledger. Work reported here is charged where it was done (GT5, step S2):
//! to the reporting thread's current node and each of its ancestors, the
//! root last. A node's ledger is then the work done in it, exact even in a
//! process that runs several solves at once.
//!
//! Nothing here decides anything. The ledger only records. A caller can
//! bound a stretch of search by a count instead of the clock, in two ways,
//! each a node of the tree whose cap is read off its own ledger: a work
//! grant counted in split-loop round trips ([`enter_work_grant`]), which a
//! loop honours exactly like a deadline, and a work ceiling counted in round
//! trips plus CDCL conflicts ([`enter_work_ceiling`]), which every deadline
//! poll reports. The same events are also counted per thread
//! ([`thread_work_units`], [`thread_round_trips`]), for a caller that
//! measures a stretch of its own work.

use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Mutex;

use guard_tree::{PROCESS_CANCEL, WORK};

/// Monotone work counters shared by every engine in the process.
#[derive(Debug, Default)]
pub struct WorkLedger {
    sat_conflicts: AtomicU64,
    sat_decisions: AtomicU64,
    split_round_trips: AtomicU64,
    deadline_shares: AtomicU64,
    deadline_shares_spent: AtomicU64,
    /// GuardTree ticks charged here (GT5); not part of [`WorkSnapshot`].
    ticks: AtomicU64,
}

/// A reading of the [`WorkLedger`].
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct WorkSnapshot {
    /// Conflicts of every CDCL search (`ay-sat` solvers), all lanes included.
    pub sat_conflicts: u64,
    /// Decisions of every CDCL search, all lanes included.
    pub sat_decisions: u64,
    /// Round trips of every DPLL(T) split loop: one per SAT re-solve after a
    /// theory split or refinement, all lanes included.
    pub split_round_trips: u64,
    /// Attempts that ran on a share of the remaining deadline, leaving the
    /// rest to a later attempt (a lane portfolio's time split). Every time
    /// split is a GuardTree share (`Guard::share_of`, GT6), which counts
    /// itself here, so the statistics say how often a check ran on less than
    /// its whole budget instead of the split being silent.
    pub deadline_shares: u64,
    /// Those of them that spent their whole share (counted as the share
    /// closes).
    pub deadline_shares_spent: u64,
}

impl WorkSnapshot {
    /// The work done between `earlier` and `self`.
    #[must_use]
    pub fn since(self, earlier: Self) -> Self {
        Self {
            sat_conflicts: self.sat_conflicts.saturating_sub(earlier.sat_conflicts),
            sat_decisions: self.sat_decisions.saturating_sub(earlier.sat_decisions),
            split_round_trips: self
                .split_round_trips
                .saturating_sub(earlier.split_round_trips),
            deadline_shares: self.deadline_shares.saturating_sub(earlier.deadline_shares),
            deadline_shares_spent: self
                .deadline_shares_spent
                .saturating_sub(earlier.deadline_shares_spent),
        }
    }
}

impl WorkLedger {
    /// An empty ledger.
    #[must_use]
    pub const fn new() -> Self {
        Self {
            sat_conflicts: AtomicU64::new(0),
            sat_decisions: AtomicU64::new(0),
            split_round_trips: AtomicU64::new(0),
            deadline_shares: AtomicU64::new(0),
            deadline_shares_spent: AtomicU64::new(0),
            ticks: AtomicU64::new(0),
        }
    }

    /// Add CDCL work a solver has not reported yet.
    pub fn add_sat_work(&self, conflicts: u64, decisions: u64) {
        if conflicts != 0 {
            work_ceiling::spend(conflicts);
        }
        self.report(&WorkSnapshot {
            sat_conflicts: conflicts,
            sat_decisions: decisions,
            ..WorkSnapshot::default()
        });
    }

    /// Count one split-loop round trip, here and on this thread's counters.
    pub fn note_round_trip(&self) {
        self.report(&WorkSnapshot {
            split_round_trips: 1,
            ..WorkSnapshot::default()
        });
        work_ceiling::spend(1);
        work_grant::note_thread_round_trip();
        #[cfg(any(test, feature = "determinism-seams"))]
        test_seams::delay_this_round_trip();
    }

    /// Where reported work goes (GT5). Reported on the process ledger
    /// ([`work`]), it is charged to the calling thread's current node and so
    /// to each of its ancestors, the process ledger last; on a thread in no
    /// node, to the process ledger alone. Any other ledger takes it as is.
    fn report(&self, work: &WorkSnapshot) {
        if !std::ptr::eq(self, &raw const WORK) {
            self.absorb(work);
            return;
        }
        if with_current_guard(|guard| guard.record_work(work)).is_none() {
            WORK.absorb(work);
        }
    }

    /// Read every counter.
    #[must_use]
    pub fn snapshot(&self) -> WorkSnapshot {
        WorkSnapshot {
            sat_conflicts: self.sat_conflicts.load(Ordering::Relaxed),
            sat_decisions: self.sat_decisions.load(Ordering::Relaxed),
            split_round_trips: self.split_round_trips.load(Ordering::Relaxed),
            deadline_shares: self.deadline_shares.load(Ordering::Relaxed),
            deadline_shares_spent: self.deadline_shares_spent.load(Ordering::Relaxed),
        }
    }

    /// Add `work` to the counters, and nothing else: a GuardTree ledger
    /// (GT5), whose thread-local charges are made where the work is reported.
    pub(crate) fn absorb(&self, work: &WorkSnapshot) {
        let counters = [
            (&self.sat_conflicts, work.sat_conflicts),
            (&self.sat_decisions, work.sat_decisions),
            (&self.split_round_trips, work.split_round_trips),
            (&self.deadline_shares, work.deadline_shares),
            (&self.deadline_shares_spent, work.deadline_shares_spent),
        ];
        for (counter, units) in counters {
            if units != 0 {
                counter.fetch_add(units, Ordering::Relaxed);
            }
        }
    }

    /// Add GuardTree ticks (GT5), saturating: a saturated count passed up
    /// stays saturated. Called once per clock stride and at a close.
    pub(crate) fn add_ticks(&self, ticks: u64) {
        let mut seen = self.ticks.load(Ordering::Relaxed);
        while let Err(now) = self.ticks.compare_exchange_weak(
            seen,
            seen.saturating_add(ticks),
            Ordering::Relaxed,
            Ordering::Relaxed,
        ) {
            seen = now;
        }
    }

    /// The GuardTree ticks charged here.
    pub(crate) fn ticks(&self) -> u64 {
        self.ticks.load(Ordering::Relaxed)
    }

    /// The work units a work ceiling counts: CDCL conflicts plus split-loop
    /// round trips.
    pub(crate) fn work_units(&self) -> u64 {
        self.sat_conflicts
            .load(Ordering::Relaxed)
            .saturating_add(self.split_round_trips.load(Ordering::Relaxed))
    }

    /// The split-loop round trips a work grant counts.
    pub(crate) fn round_trips(&self) -> u64 {
        self.split_round_trips.load(Ordering::Relaxed)
    }
}

/// The process-wide work ledger: the GuardTree root's.
#[must_use]
pub fn work() -> &'static WorkLedger {
    &WORK
}

/// A solver's high-water marks against the ledger, so that reporting its
/// cumulative counters any number of times adds each unit of work once.
///
/// Atomic so a solver can report through a shared reference (the DPLL(T)
/// layer reads statistics from `&Solver`).
#[derive(Debug, Default)]
pub struct WorkWatermark {
    conflicts: AtomicU64,
    decisions: AtomicU64,
}

impl WorkWatermark {
    /// A watermark for a solver whose cumulative counters start at these
    /// values, which someone else has already reported (a clone's inheritance).
    #[must_use]
    pub fn starting_at(conflicts: u64, decisions: u64) -> Self {
        Self {
            conflicts: AtomicU64::new(conflicts),
            decisions: AtomicU64::new(decisions),
        }
    }

    /// Report cumulative counters: add what grew since the last report. A
    /// counter that went down (a solver reset its totals) moves the mark
    /// without adding anything, and a report of nothing new charges no node.
    pub fn report(&self, total_conflicts: u64, total_decisions: u64) {
        let conflicts =
            total_conflicts.saturating_sub(self.conflicts.swap(total_conflicts, Ordering::Relaxed));
        let decisions =
            total_decisions.saturating_sub(self.decisions.swap(total_decisions, Ordering::Relaxed));
        if conflicts != 0 || decisions != 0 {
            WORK.add_sat_work(conflicts, decisions);
        }
    }
}

impl Clone for WorkWatermark {
    fn clone(&self) -> Self {
        Self::starting_at(
            self.conflicts.load(Ordering::Relaxed),
            self.decisions.load(Ordering::Relaxed),
        )
    }
}

/// Raise the process-wide cancel, the GuardTree root's flag: every node
/// stops. Only the owner of the process (the CLI's watchdogs) calls this; a
/// library embedder cancels a check through the cancel flag of its
/// [`ResourceGuard`] or its executor's interrupt instead.
pub fn cancel_process() {
    PROCESS_CANCEL.store(true, Ordering::SeqCst);
}

/// Whether the process-wide cancel is raised: one relaxed load, cheap enough
/// for any long loop that can end early with a sound "no answer" (a witness
/// search that finds none, a lemma pass that adds none). A loop whose early
/// end could be read as a complete answer must not poll this.
#[must_use]
pub fn process_cancelled() -> bool {
    PROCESS_CANCEL.load(Ordering::Relaxed)
}

#[path = "resource_check_stop.rs"]
mod check_stop;
pub use check_stop::{
    check_stop_requested, current_check_stop, current_check_stop_and_witness, enter_check_stop,
    enter_witnessed_check_stop, CheckStop, CheckStopCaptureError, CheckStopScope, CheckStopWitness,
};

#[path = "resource_work_ceiling.rs"]
mod work_ceiling;
pub use work_ceiling::{
    enter_work_ceiling, thread_work_units, work_ceiling_reached, WorkCeilingScope,
};

#[cfg(any(test, feature = "determinism-seams"))]
#[path = "resource_test_seams.rs"]
pub mod test_seams;

#[path = "resource_round_seam.rs"]
pub mod round_seam;

#[path = "resource_work_grant.rs"]
mod work_grant;
pub use work_grant::{enter_work_grant, thread_round_trips, work_grant_spent, WorkGrantScope};

/// A stop poll of a SAT search an embedder runs itself, outside the executor
/// (ay-chc's own solves, P4a slice 8): it does nothing in a build without the
/// `determinism-seams` feature. Under it, the slow-host seam's stop-poll delay
/// (`test_seams::delay_each_stop_poll`), which the executor's stop polls
/// reach through [`work_grant_spent`], so a clock the embedder reads inside
/// its own solve sees a slower host as the executor's clocks do.
#[inline]
pub fn note_sat_stop_poll() {
    #[cfg(any(test, feature = "determinism-seams"))]
    test_seams::delay_this_stop_poll();
}

/// Why a [`Guard`] says stop.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Exhausted {
    /// The cancel flag was raised (an interrupt, the CLI watchdog).
    Cancelled,
    /// The deadline passed.
    Deadline,
    /// The rlimit budget of ticks was spent.
    Rlimit,
    /// The node's CPU slice was spent (GuardTree §6).
    Cpu,
    /// The process passed its memory budget (`ay_sys::process_memory_exceeded`),
    /// or the node's memory share tripped (GT8).
    Memory,
}

impl Exhausted {
    /// The `:reason-unknown` spelling.
    #[must_use]
    pub fn reason(self) -> &'static str {
        match self {
            Self::Cancelled => "interrupted",
            Self::Deadline => "timeout",
            Self::Rlimit => "resourceout",
            Self::Cpu => "timeout",
            Self::Memory => "memout",
        }
    }
}

mod guard_tree;
#[cfg(test)]
use guard_tree::TICKS_PER_CLOCK_READ;
pub use guard_tree::{
    current_guard, with_current_guard, ChildSpec, DeadlineSource, EnterScope, Guard, GuardPoll,
    HotStride, HotWatch, Inherit, LiveDeadline, MemoryShare, NodeLabel, Portion, WeakGuard,
    WorkerId,
};

/// The resource owner of one check (engine design §3.9 R1), which is now a
/// node of the GuardTree (GuardTree step S0). [`ResourceGuard::new`] builds a
/// `Check` node under the root with no limits of its own, and the setters
/// give it a deadline, a cancel flag and an rlimit. Clones share the node,
/// so they draw on one budget, as before. A setter on a clone makes that
/// handle a view of the node ([`Guard::set_rlimit`]): it still draws on the
/// one budget, and its setting binds it alone, as before, except that it
/// can add a stop but not lift one the node has.
pub type ResourceGuard = Guard;

/// The phase and cost center the solve is in, mirrored for other threads.
static PHASE: Mutex<Option<(String, String)>> = Mutex::new(None);

/// Record the active solve phase (or `None` between phases). Called by the
/// executor at phase boundaries, never on a hot path.
pub fn publish_phase(phase: Option<(&str, &str)>) {
    let value = phase.map(|(p, c)| (p.to_string(), c.to_string()));
    match PHASE.lock() {
        Ok(mut slot) => *slot = value,
        Err(poisoned) => *poisoned.into_inner() = value,
    }
}

/// The last published phase and cost center. Never blocks: a reader that
/// finds the slot being written gets `None` rather than waiting, because the
/// reader may be the watchdog ending a run.
#[must_use]
pub fn phase_snapshot() -> Option<(String, String)> {
    match PHASE.try_lock() {
        Ok(slot) => slot.clone(),
        Err(std::sync::TryLockError::Poisoned(poisoned)) => poisoned.into_inner().clone(),
        Err(std::sync::TryLockError::WouldBlock) => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::time::Instant;
    use std::sync::atomic::AtomicBool;
    use std::sync::Arc;

    #[test]
    fn a_watermark_adds_each_unit_of_work_once() {
        let before = work().snapshot();
        let mark = WorkWatermark::default();
        mark.report(10, 30);
        mark.report(10, 30);
        mark.report(15, 31);
        let after = work().snapshot().since(before);
        // Other tests in this process may add work concurrently: at least ours.
        assert!(after.sat_conflicts >= 15, "{after:?}");
        assert!(after.sat_decisions >= 31, "{after:?}");
    }

    #[test]
    fn a_reset_counter_moves_the_mark_without_adding() {
        let mark = WorkWatermark::default();
        mark.report(100, 0);
        mark.report(4, 0);
        assert_eq!(mark.conflicts.load(Ordering::Relaxed), 4);
        mark.report(6, 0);
        assert_eq!(mark.conflicts.load(Ordering::Relaxed), 6);
    }

    #[test]
    fn a_clone_reports_only_its_own_new_work() {
        let inherited = WorkWatermark::starting_at(50, 70);
        inherited.report(50, 70);
        assert_eq!(inherited.conflicts.load(Ordering::Relaxed), 50);
        let twin = inherited.clone();
        assert_eq!(twin.decisions.load(Ordering::Relaxed), 70);
    }

    #[test]
    fn since_is_saturating() {
        let a = WorkSnapshot {
            sat_conflicts: 5,
            sat_decisions: 7,
            split_round_trips: 2,
            deadline_shares: 1,
            deadline_shares_spent: 0,
        };
        let b = WorkSnapshot {
            sat_conflicts: 9,
            sat_decisions: 7,
            split_round_trips: 1,
            deadline_shares: 3,
            deadline_shares_spent: 1,
        };
        assert_eq!(
            b.since(a),
            WorkSnapshot {
                sat_conflicts: 4,
                sat_decisions: 0,
                split_round_trips: 0,
                deadline_shares: 2,
                deadline_shares_spent: 1,
            }
        );
    }

    #[test]
    fn a_guard_stops_on_each_of_its_limits() {
        let open = ResourceGuard::new();
        assert_eq!(open.exhausted(), None);
        assert!(open.tick(10_000).is_ok());

        let mut past = ResourceGuard::new();
        past.set_deadline(Some(Instant::now()));
        assert_eq!(past.exhausted(), Some(Exhausted::Deadline));

        let flag = Arc::new(AtomicBool::new(false));
        let mut cancellable = ResourceGuard::new();
        cancellable.set_cancel(Some(Arc::clone(&flag)));
        assert!(cancellable.tick(1).is_ok());
        flag.store(true, Ordering::Relaxed);
        assert_eq!(cancellable.tick(1), Err(Exhausted::Cancelled));
        assert!(cancellable.should_stop());

        let mut budgeted = ResourceGuard::new();
        budgeted.set_rlimit(Some(100));
        assert!(budgeted.tick(99).is_ok());
        assert_eq!(budgeted.tick(1), Err(Exhausted::Rlimit));
        assert_eq!(budgeted.exhausted(), Some(Exhausted::Rlimit));
    }

    #[test]
    fn clones_draw_on_one_budget_and_ticks_read_the_clock() {
        let mut guard = ResourceGuard::new();
        guard.set_rlimit(Some(50));
        let twin = guard.clone();
        assert!(guard.tick(30).is_ok());
        assert_eq!(twin.tick(30), Err(Exhausted::Rlimit));
        assert_eq!(guard.ticks(), 60);

        // A deadline is seen by `tick` within one clock-read stride.
        let mut timed = ResourceGuard::new();
        timed.set_deadline(Some(Instant::now()));
        assert_eq!(timed.tick(TICKS_PER_CLOCK_READ), Err(Exhausted::Deadline));
        assert_eq!(Exhausted::Deadline.reason(), "timeout");
    }

    #[test]
    fn the_phase_mirror_round_trips() {
        publish_phase(Some(("ground-result-mapping", "ground-result-mapping")));
        let seen = phase_snapshot();
        // A concurrent test may have published since; the slot is never torn.
        assert!(seen.is_none_or(|(p, c)| !p.is_empty() && !c.is_empty()));
    }
}
