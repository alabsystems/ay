// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Test-only observations of the recursive case-split time budget.
//!
//! Both slots are THREAD-LOCAL, like the thread SMT deadline they observe
//! (`crate::smt::deadline`). libtest runs tests on parallel threads, and many
//! of them enter the case-split recursion; a process-wide slot let any of them
//! overwrite the observation between a test's own split and its read.

#![cfg(test)]

use crate::pdr::solver::PdrSolver;
use std::cell::Cell;
use std::time::Duration;

const NO_CASE_SPLIT_TIMEOUT_OBSERVED_MS: u64 = u64::MAX;

thread_local! {
    static LAST_CASE_SPLIT_TIMEOUT_MS: Cell<u64> =
        const { Cell::new(NO_CASE_SPLIT_TIMEOUT_OBSERVED_MS) };
    /// Thread SMT deadline remaining, observed at the same point as
    /// `LAST_CASE_SPLIT_TIMEOUT_MS`. The per-check timeout alone does not bound
    /// this recursion (it issues one check per LEAF), so the deadline is what
    /// bounds the whole split; see `PdrSolver::try_verification_case_split`.
    static LAST_CASE_SPLIT_DEADLINE_MS: Cell<u64> =
        const { Cell::new(NO_CASE_SPLIT_TIMEOUT_OBSERVED_MS) };
}

pub(super) fn record_case_split_timeout_for_tests(timeout: Option<Duration>) {
    let encoded = match timeout {
        Some(timeout) => u64::try_from(timeout.as_millis()).unwrap_or(u64::MAX - 1),
        None => NO_CASE_SPLIT_TIMEOUT_OBSERVED_MS,
    };
    LAST_CASE_SPLIT_TIMEOUT_MS.with(|slot| slot.set(encoded));
    let deadline = match crate::smt::deadline::smt_deadline_remaining() {
        Some(remaining) => u64::try_from(remaining.as_millis()).unwrap_or(u64::MAX - 1),
        None => NO_CASE_SPLIT_TIMEOUT_OBSERVED_MS,
    };
    LAST_CASE_SPLIT_DEADLINE_MS.with(|slot| slot.set(deadline));
}

impl PdrSolver {
    pub(in crate::pdr::solver) fn reset_case_split_timeout_observation_for_tests() {
        LAST_CASE_SPLIT_TIMEOUT_MS.with(|slot| slot.set(NO_CASE_SPLIT_TIMEOUT_OBSERVED_MS));
    }

    /// Reset this thread's thread-SMT-deadline observation recorded inside the
    /// case-split recursion.
    pub(in crate::pdr) fn reset_case_split_deadline_observation_for_tests() {
        LAST_CASE_SPLIT_DEADLINE_MS.with(|slot| slot.set(NO_CASE_SPLIT_TIMEOUT_OBSERVED_MS));
    }

    /// Thread SMT deadline remaining as seen inside this thread's most recent
    /// case-split recursion, or `None` when no deadline was armed there.
    pub(in crate::pdr) fn observed_case_split_deadline_for_tests() -> Option<Duration> {
        match LAST_CASE_SPLIT_DEADLINE_MS.with(Cell::get) {
            NO_CASE_SPLIT_TIMEOUT_OBSERVED_MS => None,
            ms => Some(Duration::from_millis(ms)),
        }
    }
}

mod thread_scope_tests {
    use super::*;
    use crate::smt::ScopedSmtDeadline;

    /// Record one case-split entry on a FRESH thread, which starts with no
    /// thread SMT deadline, optionally under `deadline`.
    fn record_on_another_thread(deadline: Option<Duration>) {
        std::thread::scope(|scope| {
            scope.spawn(|| {
                let _deadline = deadline.map(ScopedSmtDeadline::install);
                record_case_split_timeout_for_tests(None);
            });
        });
    }

    /// A test reading the observation must see ITS OWN thread's split, never a
    /// concurrently running test's.
    ///
    /// `verification_case_split_arms_the_thread_smt_deadline` resets, splits,
    /// then reads. With a process-wide slot, any case split another libtest
    /// thread entered in between overwrote it. Both directions were measured
    /// on the `ay-chc` lib at ed1a90342, `pdr::` batch, 18 threads: "none"
    /// from a split with no deadline (8 of 10 runs, the `expect` failed), and
    /// ~2 s from PDR verification under `VERIFY_INITIAL_TIMEOUT` (the 1.997 s
    /// read against 250 ms in a full-suite run). The same slot could equally
    /// have passed the test on another thread's small deadline.
    #[test]
    fn case_split_deadline_observation_is_scoped_to_the_observing_thread() {
        let own = Duration::from_millis(250);
        let _deadline = ScopedSmtDeadline::install(own);
        PdrSolver::reset_case_split_deadline_observation_for_tests();
        record_case_split_timeout_for_tests(None);

        record_on_another_thread(None);
        let observed = PdrSolver::observed_case_split_deadline_for_tests()
            .expect("another thread's undeadlined split must not erase this thread's observation");
        assert!(observed <= own, "observed {observed:?} against {own:?}");

        record_on_another_thread(Some(Duration::from_secs(2)));
        let observed = PdrSolver::observed_case_split_deadline_for_tests()
            .expect("this thread's split ran under a deadline");
        assert!(
            observed <= own,
            "another thread's 2 s deadline leaked into this thread's observation: \
             observed {observed:?} against {own:?}"
        );
    }
}
