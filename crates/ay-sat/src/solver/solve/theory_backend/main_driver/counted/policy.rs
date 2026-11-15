// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

impl Policy for Counted<'_> {
    fn memory_poll(&self, s: &mut Solver) -> Result<()> {
        prepare::memory_poll(self.0)?;
        s.poll_process_memory_limit_now();
        self.0.check().map_err(counted_admission::reason)
    }
    fn iteration(&self, s: &mut Solver) -> Result<()> {
        prepare::iteration(s, self.0)
    }
    fn imports(&self, s: &mut Solver) -> Result<()> {
        self.0.admit(16, 0).map_err(counted_admission::reason)?;
        if s.decision_level == 0
            && s.cold.portfolio_clause_importer.is_some()
            && !s.cold.lrat_enabled
            && s.proof_manager.is_none()
            && s.cold.scope_selectors.is_empty()
            && !s.watches_disconnected
        {
            return Err(refusal(
                self.0,
                "selected portfolio imports are not admitted",
            ));
        }
        s.import_portfolio_shared_clauses_at_root();
        Ok(())
    }
    fn before_conflict(&self, s: &mut Solver) -> Result<()> {
        prepare::conflict(s, self.0)
    }
    fn analyze(&self, s: &mut Solver, conflict: ClauseRef) -> Result<()> {
        s.dispatch_conflict_counted(conflict).map(|_| ())
    }
    fn restart(&self, s: &mut Solver) -> Result<bool> {
        self.0.admit(64, 0).map_err(counted_admission::reason)?;
        if s.should_cold_restart() {
            return Err(refusal(self.0, "selected cold restart is not admitted"));
        }
        // Run the actual ordinary no-restart prefix, including attribution
        // clearing and EMA invariants. The later schedule can switch modes,
        // rebuild heaps, and backtrack: refuse BEFORE reaching those effects.
        if s.conflicts_since_restart != 0 && s.num_conflicts >= s.cold.restart_min_conflicts {
            return Err(refusal(
                self.0,
                "selected restart schedule continuation is not admitted",
            ));
        }
        let restarted = s.maybe_run_restart_pure();
        self.0.check().map_err(counted_admission::reason)?;
        Ok(restarted)
    }
    fn compact(&self, s: &mut Solver) -> Result<()> {
        self.0.admit(16, 0).map_err(counted_admission::reason)?;
        if s.cold.arena_compaction_pending
            && s.qhead >= s.trail.len()
            && s.pending_theory_conflicts.is_empty()
        {
            return Err(refusal(self.0, "selected arena compaction is not admitted"));
        }
        s.run_deferred_arena_compaction();
        Ok(())
    }
    fn maintenance(
        &self,
        _: &mut Solver,
        kind: Maintenance,
        _: &dyn Fn() -> bool,
        _: ProofProgress<'_>,
    ) -> Result<Option<SatResult>> {
        let why = match kind {
            Maintenance::Rephase => "selected rephase is not admitted",
            Maintenance::Reorder => "selected variable reorder is not admitted",
            Maintenance::Lookahead => "selected lookahead round is not admitted",
            Maintenance::Inprocess => "selected inprocessing round is not admitted",
        };
        Err(refusal(self.0, why))
    }
    fn decision(&self, s: &mut Solver, lit: Literal) -> Result<()> {
        self.0.admit(8, 0).map_err(counted_admission::reason)?;
        if s.cold.search_decisions == u64::MAX {
            return Err(refusal(self.0, "MAIN decision counter overflow"));
        }
        s.cold.search_decisions += 1;
        s.stats
            .record_first_search_decision(lit.variable().index() as u32);
        s.decide_counted(lit)
    }
    fn pick(&self, s: &mut Solver) -> Result<Option<Literal>> {
        s.pick_main_decision_literal_counted()
    }
    fn unsat(
        &self,
        s: &mut Solver,
        conflict: Option<ClauseRef>,
        progress: ProofProgress<'_>,
    ) -> Result<SatResult> {
        s.declare_counted_root_unsat(conflict, self.0, progress)
    }
    fn sat(&self, s: &mut Solver) -> Result<SatResult> {
        s.declare_counted_complete_assignment_sat(self.0)
    }
}
