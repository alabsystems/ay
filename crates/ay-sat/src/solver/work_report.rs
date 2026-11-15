// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! When a solver's search work reaches the process work ledger
//! (`ay_core::resource`).
//!
//! Reported work is charged to the reporting thread's current GuardTree node
//! and to each of its ancestors (GT5), and a work ceiling or grant is read off
//! its node's ledger. So a counted owner sees exactly the SAT search a solver
//! reported, on its own thread, while that thread was inside the owner.
//!
//! A solver used to report at the restarts of its main loops only (besides
//! the DPLL(T) layer's report when it collects a lane's statistics). The
//! assumption and IC3 loops restart without that report, so their solves
//! charged nothing; a solve that ended before its first restart charged
//! nothing; and every other solve's tail waited for the same solver's next
//! restart, if one ever came, charged to whatever node its thread was in by
//! then. Measured (`tests/work_ledger.rs`, 9 pigeons in 8 holes on the
//! default schedule): 1,672 conflicts, 885 charged. The strict checker runs
//! thousands of short local solves: on `rem_u32_digits` (f6555db0b, debug)
//! the residual-trust rescue's case split (`sat_sweep::split` leaves) ran for
//! about 13 s and charged no unit, while the same sweep's longer solves
//! charged 20,876. What a work ceiling saw of certification depended on where
//! restarts fell.
//!
//! A solver now reports at points its own counts place, never the clock:
//!
//! * at every caller stop poll (`Solver::solve_stop_reason`), before the
//!   caller's callback runs, so a ceiling that callback reads counts every
//!   conflict made before the poll. The loops poll on counts of their own
//!   steps (the main CDCL loops every 100 conflicts, every 1000 decisions
//!   and every 1024 iterations, the theory loop also at its theory rounds,
//!   the IC3 loop every 256 iterations);
//! * at the end of every solve call (`Solver::finish_counted_sat` and
//!   `Solver::finish_counted_assume`, which every public solve entry returns
//!   through), so each solve is charged in full, to the node it ran in,
//!   before its caller reads the answer;
//! * at every restart, as before.
//!
//! The watermark adds each conflict once however often the solver reports,
//! so the totals are the solver's own counts, the same on every host and
//! under any load. Reporting decides nothing by itself: a ceiling it reaches
//! is read by the same polls as an expired deadline and ends the search with
//! `Unknown`, never with a verdict. An IC3 query polls its caller's stop once
//! more after its search (`solve/ic3/deadline.rs`), so a query whose own
//! conflicts reach the ceiling answers `Unknown` even when its search has
//! finished, as it does when a deadline passes then.

use super::*;

impl Solver {
    /// Report the conflicts and decisions this solver has made since its last
    /// report to the process-wide work ledger ([`ay_core::resource::work`]),
    /// charged to this thread's current GuardTree node.
    ///
    /// Idempotent: the solver keeps a watermark, so calling this any number of
    /// times adds each conflict once. The solver reports at every stop poll, at
    /// the end of every solve and at every restart; the DPLL(T) layer reports
    /// when it collects a lane's statistics. That is what lets a check-sat
    /// state the work of all its lanes, a counted owner stop the solves it
    /// bounds, and the watchdog state the work of a run it has to end.
    pub fn report_work_to_ledger(&self) {
        self.cold
            .work_watermark
            .report(self.total_num_conflicts(), self.total_num_decisions());
    }
}
