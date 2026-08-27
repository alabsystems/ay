// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Sizing the SAT engine against a whole-process `--memory` budget, and
//! attributing a mid-solve peak when that budget is breached.
//!
//! Kept out of `solver/config.rs` so that file stays what its waiver says it is
//! — the switch/accessor module — and so the memory work has one place to grow.

use super::*;

/// Share of a whole-process `--memory` budget that
/// [`Solver::arm_clause_db_budget_from_process_limit`] hands to the clause
/// database.
///
/// The advisory memout gate trips at 95% of the budget on the OS footprint, so
/// the remaining 35 points cover everything the clause-DB accounting does not
/// see: per-variable arrays (measured ~209 B/var), trail and VSIDS, conflict
/// analysis buffers, the proof writer, allocator slack, and the footprint /
/// live-bytes gap (compressed and swapped pages count toward the macOS
/// `phys_footprint` the advisory reads, and do not appear in RSS at all).
pub(crate) const CLAUSE_DB_BUDGET_PERCENT: usize = 60;

/// Minimum learned-clause headroom above the loaded formula that
/// [`Solver::arm_clause_db_budget_from_process_limit`] always leaves.
///
/// Guards the degenerate case where the ORIGINAL formula alone already costs
/// more than the budget share: without a floor the byte trigger would fire on
/// every conflict with nothing reducible to show for it.
pub(crate) const CLAUSE_DB_MIN_LEARNED_HEADROOM_BYTES: usize = 64 * 1024 * 1024;

impl Solver {
    /// Derive a clause-DB byte ceiling from a whole-process memory budget and
    /// install it. Returns the ceiling actually installed, or `None` when the
    /// budget is unset (`0`).
    ///
    /// WHY THIS EXISTS. `--memory` is enforced only by observers: the advisory
    /// gate trips at 95% of the budget and the watchdog then publishes
    /// `c memout` / `s UNKNOWN`. Nothing inside the SAT engine ever *sizes its
    /// own clause database* against that budget, because `max_clause_db_bytes`
    /// defaults to `None` and the DIMACS entry points never set it — only the
    /// BV, strings and resolution-DAG paths do. So on a formula whose learned
    /// database can outgrow the budget, the reduction schedule
    /// (`next_reduce_db`, `1000*sqrt(r)` conflicts apart, deleting a permille
    /// quota of what exists) is the ONLY thing bounding growth, and when it
    /// loses that race the run does not degrade — it aborts. That is a
    /// capability failure, not a search failure: the solver never gets to try.
    ///
    /// Arming the ceiling turns the abort into backpressure. `should_reduce_db`
    /// already has the byte trigger and `reduce_db` already treats
    /// `explicit_reduce_pressure` as a mandate to sweep satisfied clauses and
    /// compact, so the whole mechanism exists; it was simply never connected to
    /// the process budget on this path.
    ///
    /// THE SHARE. The clause DB (arena + watchers + clause ids + original
    /// ledger + reconstruction stack) is what grows without bound; everything
    /// else — per-variable arrays, trail, VSIDS, conflict analysis, the proof
    /// writer's buffers, allocator slack, and the gap between the allocator's
    /// live bytes and the OS footprint that the advisory actually reads — is
    /// charged against the same budget. [`CLAUSE_DB_BUDGET_PERCENT`] is that
    /// share.
    ///
    /// THE FLOOR. The ceiling is never set below what the ORIGINAL formula
    /// already costs plus [`CLAUSE_DB_MIN_LEARNED_HEADROOM_BYTES`]: the ledger
    /// and the irredundant arena cannot be reduced away, so a ceiling under
    /// that floor would make the byte trigger fire on every single conflict and
    /// achieve nothing but the scan cost. Call this AFTER the formula is
    /// loaded so the floor reflects the real input.
    pub fn arm_clause_db_budget_from_process_limit(
        &mut self,
        process_limit_bytes: usize,
    ) -> Option<usize> {
        if process_limit_bytes == 0 {
            return None;
        }
        let share = process_limit_bytes / 100 * CLAUSE_DB_BUDGET_PERCENT;
        let floor = self
            .clause_db_memory_bytes()
            .saturating_add(CLAUSE_DB_MIN_LEARNED_HEADROOM_BYTES);
        let limit = share.max(floor);
        self.cold.max_clause_db_bytes = Some(limit);
        Some(limit)
    }

    /// `--sat-mem-probe`: attribute the CURRENT footprint to the clause
    /// database, mid-solve.
    ///
    /// The construction probe in `solver/build.rs` answers "what does a
    /// variable cost before the first clause is read" — a fixed
    /// `num_vars`-proportional tax. This answers the question a MEMOUT asks:
    /// where did the peak go, when the peak is reached in the middle of search
    /// and the per-variable tax is a small fraction of it. The terms reported
    /// here are exactly the ones [`Self::clause_db_memory_bytes`] sums, so a
    /// reader can see which of them the byte trigger is actually responding to.
    ///
    /// `phase` names the call site, so a run emits a time series (one pair of
    /// lines per reduction) rather than a single snapshot. Diagnostic only:
    /// unreachable without the CLI flag.
    pub(super) fn mem_probe_report(&self, phase: &str) {
        if !ay_core::misc_cli_flags().sat_mem_probe {
            return;
        }
        let mb = |bytes: usize| bytes as f64 / 1e6;
        let clause_ids = self.cold.clause_ids.capacity() * size_of::<u64>();
        eprintln!(
            "c mem_probe {phase} conflicts={} footprint={:.1} live={:.1} db={:.1} \
             arena={:.1} watches={:.1} ledger={:.1} clause_ids={:.1} reconstruction={:.1} \
             slack={:.1} clauses={} redundant={} db_limit={}",
            self.num_conflicts,
            mb(ay_sys::current_footprint_bytes()),
            mb(ay_sys::current_live_bytes()),
            mb(self.clause_db_memory_bytes()),
            mb(self.arena.memory_bytes()),
            mb(self.watches.heap_bytes()),
            mb(self.cold.original_ledger.heap_bytes()),
            mb(clause_ids),
            mb(self.inproc.reconstruction.memory_bytes()),
            mb(self.cold.load_slack_reclaimed_bytes),
            self.arena.num_clauses(),
            self.arena.redundant_count(),
            self.cold
                .max_clause_db_bytes
                .map_or_else(|| "none".to_string(), |limit| format!("{:.1}", mb(limit))),
        );
    }
}
