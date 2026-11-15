// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Shared default pure CDCL orchestration. Policies admit the actual selected
//! operations, never change engine selection or turn refusal into a fixpoint.

use super::*;
pub(super) mod counted;
mod ordinary;
#[cfg(test)]
mod tests;

use ordinary::Ordinary;
type Result<T> = std::result::Result<T, SatUnknownReason>;

pub(super) fn run_ordinary(
    s: &mut Solver,
    stop: &dyn Fn() -> bool,
    progress: ProofProgress<'_>,
) -> Result<SatResult> {
    run(s, stop, progress, &Ordinary)
}

#[derive(Clone, Copy)]
enum Maintenance {
    Rephase,
    Reorder,
    Lookahead,
    Inprocess,
}

trait Policy {
    fn memory_poll(&self, s: &mut Solver) -> Result<()>;
    fn iteration(&self, s: &mut Solver) -> Result<()>;
    fn imports(&self, s: &mut Solver) -> Result<()>;
    fn before_conflict(&self, s: &mut Solver) -> Result<()>;
    fn analyze(&self, s: &mut Solver, conflict: ClauseRef) -> Result<()>;
    fn restart(&self, s: &mut Solver) -> Result<bool>;
    fn compact(&self, s: &mut Solver) -> Result<()>;
    fn maintenance(
        &self,
        s: &mut Solver,
        kind: Maintenance,
        stop: &dyn Fn() -> bool,
        progress: ProofProgress<'_>,
    ) -> Result<Option<SatResult>>;
    fn decision(&self, s: &mut Solver, lit: Literal) -> Result<()>;
    fn pick(&self, s: &mut Solver) -> Result<Option<Literal>>;
    fn unsat(
        &self,
        s: &mut Solver,
        conflict: Option<ClauseRef>,
        progress: ProofProgress<'_>,
    ) -> Result<SatResult>;
    fn sat(&self, s: &mut Solver) -> Result<SatResult>;
}

/// Exactly the original main-loop order, including conflict-free maintenance
/// priority and the separate conflict/decision/iteration stop cadences.
fn run<P: Policy>(
    s: &mut Solver,
    stop: &dyn Fn() -> bool,
    progress: ProofProgress<'_>,
    policy: &P,
) -> Result<SatResult> {
    let mut loop_iters = 0u64;
    loop {
        policy.iteration(s)?;
        if let Some(reason) = s.counted_step_stop_reason() {
            return Err(reason);
        }
        if let Some(reason) = s.active_interrupt_reason() {
            return Err(reason);
        }
        loop_iters = loop_iters.wrapping_add(1);
        if loop_iters & 1023 == 0 {
            if let Some(reason) = s.solve_stop_reason(stop) {
                return Err(reason);
            }
            policy.memory_poll(s)?;
        }
        policy.imports(s)?;
        if s.has_empty_clause {
            return policy.unsat(s, None, progress);
        }
        if let Some(conflict) = s.search_propagate_standard_counted()? {
            if s.decision_level == 0 {
                return policy.unsat(s, Some(conflict), progress);
            }
            conflict_step(s, conflict, stop, policy)?;
            continue;
        }
        policy.compact(s)?;
        let restarted =
            (!s.cold.restart_fixpoint_kissat || s.decision_level > 0) && policy.restart(s)?;
        if restarted {
            continue;
        }
        if let Some(kind) = maintenance(s) {
            if let Some(result) = policy.maintenance(s, kind, stop, progress)? {
                return Ok(result);
            }
            // The original rephase/reorder/lookahead branches all reach the
            // loop end; inprocessing explicitly continues. Both repeat BCP.
            continue;
        }
        let selected = match s.take_lookahead_decision() {
            Some(lit) => Some(lit),
            None => policy.pick(s)?,
        };
        match selected {
            Some(lit) => {
                policy.decision(s, lit)?;
                if s.num_decisions.is_multiple_of(1000) {
                    if s.decision_budget_exhausted() {
                        return Err(SatUnknownReason::ResourceBudget);
                    }
                    if let Some(reason) = s.solve_stop_reason(stop) {
                        return Err(reason);
                    }
                }
            }
            None => return policy.sat(s),
        }
    }
}

fn conflict_step<P: Policy>(
    s: &mut Solver,
    conflict: ClauseRef,
    stop: &dyn Fn() -> bool,
    policy: &P,
) -> Result<()> {
    policy.before_conflict(s)?;
    s.conflicts_since_restart += 1;
    s.num_conflicts += 1;
    s.stats.stable_conflicts += u64::from(s.stable_mode);
    if s.num_conflicts >= s.cold.stable_lock_at {
        s.decide_stable_lock();
    }
    s.on_conflict_random_decision();
    s.notify_observer_conflict();
    if s.cold.trace_ext_conflict {
        s.trace_bcp_conflict_detail(conflict);
    }
    if s.resource_budget_exhausted() {
        return Err(SatUnknownReason::ResourceBudget);
    }
    if s.num_conflicts.is_multiple_of(100) {
        if let Some(reason) = s.solve_stop_reason(stop) {
            return Err(reason);
        }
        s.maybe_emit_progress();
    }
    policy.analyze(s, conflict)?;
    if !s.cold.restart_fixpoint_kissat {
        policy.restart(s)?;
    }
    Ok(())
}

fn maintenance(s: &Solver) -> Option<Maintenance> {
    if s.should_rephase() {
        Some(Maintenance::Rephase)
    } else if s.kissat_reorder_due() && (!s.cold.reorder_weights_kissat || s.decision_level == 0) {
        Some(Maintenance::Reorder)
    } else if s.should_run_lookahead() {
        Some(Maintenance::Lookahead)
    } else if s.inprocessing_gates_pass() {
        Some(Maintenance::Inprocess)
    } else {
        None
    }
}
