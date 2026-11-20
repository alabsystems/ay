// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The `:rlimit` counts shared by the bit-blast SAT sub-solvers (BV, FP and
//! EUF enum-SAT lanes): conflicts and decisions, never a clock (P4a).

use ay_sat::{SatResult, Solver as SatSolver};

use super::Executor;

/// The ground budget's own decisions-per-conflict ratio (24M / 400k): the
/// decision allowance of a `:rlimit` that comes with the default ground budget
/// switched off and no explicit decision limit.
const DECISIONS_PER_CONFLICT: u64 =
    Executor::DEFAULT_GROUND_DECISION_ALLOWANCE / Executor::DEFAULT_GROUND_CONFLICT_ALLOWANCE;

/// What the earlier solves of one solve chain already spent. Refinement loops
/// re-solve, on a fresh solver or on the same one, so the chain total, not
/// each solve, is what an allowance bounds; one-shot lanes pass
/// [`ChainSpend::NONE`].
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(in crate::executor) struct ChainSpend {
    pub(in crate::executor) conflicts: u64,
    pub(in crate::executor) decisions: u64,
}

impl ChainSpend {
    /// Nothing spent: a one-shot solve.
    pub(in crate::executor) const NONE: Self = Self {
        conflicts: 0,
        decisions: 0,
    };

    /// Debit what the solve `solver` just finished spent. ay-sat zeroes its
    /// conflict and decision counters at the start of every solve, so they
    /// hold that solve's work alone, on a fresh solver and on a reused one
    /// alike; debit once per solve.
    pub(in crate::executor) fn debit(&mut self, solver: &SatSolver) {
        self.conflicts = self.conflicts.saturating_add(solver.num_conflicts());
        self.decisions = self.decisions.saturating_add(solver.num_decisions());
    }
}

/// The allowances one bit-blast SAT solve chain runs under. `None` is no
/// bound on that axis.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct BitblastAllowances {
    pub(crate) conflicts: Option<u64>,
    pub(crate) decisions: Option<u64>,
}

impl BitblastAllowances {
    /// The allowances for an executor's `:rlimit` (`resource_limit`), its
    /// explicit decision limit and whether its default ground budget is on.
    ///
    /// Under `:rlimit`, both counts: the conflicts are the `:rlimit` itself,
    /// and the decisions come from the helper the ground pipeline's arms use
    /// (`effective_decision_allowance`: the explicit decision limit, else the
    /// ground decision allowance), else, with the ground budget switched off,
    /// `:rlimit` conflicts at the ground budget's own ratio. A search that is
    /// decision-heavy and conflict-light therefore ends on a count too,
    /// `unknown (resourceout)`, never at the wall-clock backstop.
    ///
    /// Without `:rlimit` the conflicts stay unbounded and only an explicit
    /// decision limit applies: the DEFAULT ground allowances are deliberately
    /// not applied here, since bit-blasted instances routinely need orders of
    /// magnitude more conflicts than ground CDCL, and the ground default would
    /// flip legitimate verdicts to `unknown`.
    pub(in crate::executor) fn for_limits(
        resource_limit: Option<u64>,
        decision_limit: Option<u64>,
        ground_budget_enabled: bool,
    ) -> Self {
        let Some(conflicts) = resource_limit else {
            return Self {
                conflicts: None,
                decisions: decision_limit,
            };
        };
        let decisions = crate::pipeline_fns::effective_decision_allowance(
            decision_limit,
            ground_budget_enabled,
        )
        .unwrap_or_else(|| conflicts.saturating_mul(DECISIONS_PER_CONFLICT));
        Self {
            conflicts: Some(conflicts),
            decisions: Some(decisions),
        }
    }

    /// Whether either count is bounded.
    pub(in crate::executor) fn bounded(self) -> bool {
        self.conflicts.is_some() || self.decisions.is_some()
    }

    /// Arm `solver`'s next solve with what is left of these allowances after
    /// `spent`. Call it before EVERY solve of a chain, a re-solve of the same
    /// solver included.
    ///
    /// The target is the remainder itself: ay-sat's budget is an absolute
    /// count of `num_conflicts()` / `num_decisions()`, and the solve zeroes
    /// both when it starts (`reset_search_state`), so a target of the
    /// solver's current count plus the remainder would grant a reused
    /// solver its previous solve's work again on top of the remainder. A
    /// zero remainder is NOT "unlimited" (the `0 == unlimited` convention
    /// belongs to the user-facing `:rlimit` value, which `set_resource_limit`
    /// normalizes to `None` before it reaches the executor). `None` clears a
    /// budget a previous arming left.
    ///
    /// A bounded solve also runs ay-sat's counted schedules
    /// (`set_deterministic_inproc`): its preprocessing, inprocessing and
    /// startup probes are sized by work, not by the time left before the
    /// deadline, so the counts alone decide it and the deadline only stops
    /// it. An unbounded one goes back to the process-wide setting.
    pub(in crate::executor) fn arm(self, solver: &mut SatSolver, spent: ChainSpend) {
        let conflicts = self
            .conflicts
            .map(|allowance| allowance.saturating_sub(spent.conflicts));
        let decisions = self
            .decisions
            .map(|allowance| allowance.saturating_sub(spent.decisions));
        solver.set_conflict_budget(conflicts);
        solver.set_decision_budget(decisions);
        solver.set_deterministic_inproc(self.bounded() || ay_sat::deterministic_inproc_enabled());
    }
}

impl Executor {
    /// The bit-blast lanes' allowances for this executor's configuration
    /// (see [`BitblastAllowances::for_limits`]).
    pub(crate) fn bitblast_sat_allowances(&self) -> BitblastAllowances {
        BitblastAllowances::for_limits(
            self.resource_limit,
            self.decision_limit,
            self.ground_budget_enabled,
        )
    }

    /// Arm a bit-blast SAT (sub-)solver with the executor's `:rlimit` counts
    /// (#8749 conflicts; P4a decisions beside them): BV, FP, and EUF enum-SAT
    /// lanes.
    ///
    /// The main pipeline's CDCL solves honor `:rlimit` deterministically, but
    /// the bit-blast lanes' `SatSolver` solves once ran unbudgeted: a
    /// divergent obligation burned wall clock at 100% CPU until the deadline
    /// backstop, so its verdict was decided by machine load, exactly the
    /// nondeterminism the budget exists to kill. A conflict budget alone left
    /// that hole open for a decision-heavy, conflict-light search, so each
    /// solve carries a decision budget beside it. Each is capped at the
    /// REMAINING allowance of the solve chain (`spent`).
    ///
    /// Exhaustion surfaces as `Unknown` with `SatUnknownReason::ResourceBudget`,
    /// which `collect_sat_stats!` + `solve_and_store_model*` map to the same
    /// fail-closed `resourceout` reason as the ground pipeline: an exhausted
    /// budget is NEVER a verdict. A bounded solve runs ay-sat's counted
    /// schedules (see [`BitblastAllowances::arm`]), so the wall-clock deadline
    /// stays armed only as the outer backstop, published as `timeout` when it
    /// fires.
    pub(in crate::executor) fn arm_sat_count_budget(
        &self,
        solver: &mut SatSolver,
        spent: ChainSpend,
    ) {
        self.bitblast_sat_allowances().arm(solver, spent);
    }

    /// Solve once, armed with what is left of the chain's allowances, and
    /// debit the solve's work from the chain: a fresh solver's first solve or
    /// a re-solve of a reused one.
    pub(in crate::executor::theories) fn solve_sat_in_budget_chain(
        &mut self,
        solver: &mut SatSolver,
        spent: &mut ChainSpend,
    ) -> SatResult {
        self.arm_sat_count_budget(solver, *spent);
        let should_stop = self.make_should_stop();
        #[cfg(test)]
        let should_stop = slow_host::slow_poll(should_stop);
        let result = solver.solve_interruptible(should_stop).into_inner();
        collect_sat_stats!(self, solver);
        spent.debit(solver);
        result
    }
}

/// A slow host for the bit-blast lanes' tests: a sleep inside every stop
/// poll of the SAT search (every 100 conflicts and every 1,000 decisions, a
/// count), so every clock the solve reads (its deadline, the deadline timer)
/// sees the slowdown while every count it keeps stays the same. Per thread,
/// so a test slows only its own solve; compiled only for tests.
#[cfg(test)]
pub(in crate::executor) mod slow_host {
    use std::cell::Cell;
    use std::time::Duration;

    thread_local! {
        static DELAY: Cell<Duration> = const { Cell::new(Duration::ZERO) };
        static POLLS: Cell<u64> = const { Cell::new(0) };
    }

    /// Sleep `delay` in every SAT stop poll on this thread from now on
    /// (`Duration::ZERO` switches it off). Resets the poll count.
    pub(in crate::executor) fn delay_each_poll(delay: Duration) {
        DELAY.with(|cell| cell.set(delay));
        POLLS.with(|cell| cell.set(0));
    }

    /// Polls since the last [`delay_each_poll`], slept or not: a count of the
    /// search's trajectory, so an idle run tells a slowed one how many
    /// sleeps it will take.
    pub(in crate::executor) fn polls() -> u64 {
        POLLS.with(Cell::get)
    }

    /// `should_stop`, slowed by this thread's delay.
    pub(in crate::executor) fn slow_poll(should_stop: impl Fn() -> bool) -> impl Fn() -> bool {
        let delay = DELAY.with(Cell::get);
        move || {
            POLLS.with(|cell| cell.set(cell.get() + 1));
            if !delay.is_zero() {
                std::thread::sleep(delay);
            }
            should_stop()
        }
    }
}

#[cfg(test)]
#[path = "resource_budget/tests.rs"]
mod tests;

#[cfg(test)]
#[path = "resource_budget/host_tests.rs"]
mod host_tests;
