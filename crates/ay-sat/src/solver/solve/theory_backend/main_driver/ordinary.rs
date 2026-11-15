// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

pub(super) struct Ordinary;

impl Policy for Ordinary {
    fn memory_poll(&self, s: &mut Solver) -> Result<()> {
        s.poll_process_memory_limit_now();
        Ok(())
    }
    fn iteration(&self, _: &mut Solver) -> Result<()> {
        Ok(())
    }
    fn imports(&self, s: &mut Solver) -> Result<()> {
        s.import_portfolio_shared_clauses_at_root();
        Ok(())
    }
    fn before_conflict(&self, _: &mut Solver) -> Result<()> {
        Ok(())
    }
    fn analyze(&self, s: &mut Solver, conflict: ClauseRef) -> Result<()> {
        s.analyze_and_backtrack(conflict, "main search loop", |_, _| {});
        Ok(())
    }
    fn restart(&self, s: &mut Solver) -> Result<bool> {
        Ok(s.maybe_run_restart_pure())
    }
    fn compact(&self, s: &mut Solver) -> Result<()> {
        s.run_deferred_arena_compaction();
        Ok(())
    }
    fn maintenance(
        &self,
        s: &mut Solver,
        kind: Maintenance,
        stop: &dyn Fn() -> bool,
        progress: ProofProgress<'_>,
    ) -> Result<Option<SatResult>> {
        match kind {
            Maintenance::Rephase => {
                if s.decision_level != 0 {
                    s.backtrack(0);
                }
                s.rephase();
                Ok(s.cold
                    .rephase_walk_model
                    .take()
                    .map(|model| s.declare_sat_from_model(model)))
            }
            Maintenance::Reorder => {
                if s.decision_level != 0 {
                    s.backtrack(0);
                }
                s.kissat_reorder();
                Ok(None)
            }
            Maintenance::Lookahead => {
                debug_assert_eq!(s.decision_level, 0);
                s.run_lookahead_round();
                Ok(s.has_empty_clause
                    .then(|| s.declare_unsat_with_proof_progress(progress)))
            }
            Maintenance::Inprocess => {
                if s.decision_level != 0 {
                    s.backtrack(0);
                }
                Ok(s.run_inprocessing_round_until(stop, progress))
            }
        }
    }
    fn decision(&self, s: &mut Solver, lit: Literal) -> Result<()> {
        s.cold.search_decisions += 1;
        s.stats
            .record_first_search_decision(lit.variable().index() as u32);
        s.decide(lit);
        Ok(())
    }
    fn pick(&self, s: &mut Solver) -> Result<Option<Literal>> {
        Ok(s.pick_next_decision_variable_main()
            .map(|v| s.pick_phase(v)))
    }
    fn unsat(
        &self,
        s: &mut Solver,
        conflict: Option<ClauseRef>,
        progress: ProofProgress<'_>,
    ) -> Result<SatResult> {
        if let Some(reference) = conflict {
            if s.cold.trace_ext_conflict {
                s.trace_bcp_conflict_level0(reference);
            }
            s.record_level0_conflict_chain(reference);
        }
        Ok(s.declare_unsat_with_proof_progress(progress))
    }
    fn sat(&self, s: &mut Solver) -> Result<SatResult> {
        Ok(s.declare_cdcl_complete_assignment_sat_no_tla())
    }
}
