// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Conflict-budget plumbing shared by bit-blast SAT sub-solvers.

use ay_sat::{SatResult, Solver as SatSolver};

use super::Executor;

impl Executor {
    /// Arm a bit-blast SAT (sub-)solver with the executor's explicit
    /// `:rlimit` conflict budget (#8749: BV, FP, and EUF enum-SAT lanes).
    ///
    /// The main pipeline's CDCL solves honor `:rlimit` deterministically, but
    /// the bit-blast lanes' `SatSolver` solves ran unbudgeted: a divergent
    /// obligation burned wall clock at 100% CPU until the deadline backstop,
    /// so its verdict was decided by machine load — exactly the nondeterminism
    /// the conflict budget exists to kill. Cap each bit-blast SAT solve at the
    /// REMAINING allowance (`resource_limit - consumed_conflicts`, where
    /// `consumed_conflicts` is the conflict total already burned by earlier
    /// solves of the same solve chain: refinement loops rebuild a FRESH solver
    /// per iteration, so the chain total — not each fresh solver individually
    /// — is what the budget must bound; one-shot lanes pass 0).
    ///
    /// Exhaustion surfaces as `Unknown` with
    /// `SatUnknownReason::ResourceBudget`, which `collect_sat_stats!` +
    /// `solve_and_store_model*` already map to the same fail-closed
    /// `resourceout` reason as the ground pipeline — an exhausted budget is
    /// NEVER a verdict. A zero remaining allowance is deliberately NOT
    /// special-cased to "unlimited": the `0 == unlimited` convention applies
    /// only to the user-facing `:rlimit` value, which `set_resource_limit`
    /// already normalizes to `None` before it reaches this field.
    ///
    /// `resource_limit == None` (no explicit `:rlimit`) passes `None` through,
    /// leaving the solver unbudgeted — exactly the pre-change behavior. The
    /// DEFAULT ground conflict allowance is deliberately NOT applied here:
    /// bit-blasted instances routinely need orders of magnitude more conflicts
    /// than ground CDCL, and imposing the ground default would flip legitimate
    /// verdicts to Unknown. The wall-clock deadline stays armed as the outer
    /// liveness backstop.
    pub(in crate::executor::theories) fn arm_sat_conflict_budget(
        &self,
        solver: &mut SatSolver,
        consumed_conflicts: u64,
    ) {
        let target = self.resource_limit.map(|limit| {
            solver
                .num_conflicts()
                .saturating_add(limit.saturating_sub(consumed_conflicts))
        });
        solver.set_conflict_budget(target);
    }

    /// Solve one fresh SAT instance and debit its conflicts from a solve chain.
    pub(in crate::executor::theories) fn solve_sat_in_budget_chain(
        &mut self,
        solver: &mut SatSolver,
        consumed_conflicts: &mut u64,
    ) -> SatResult {
        self.arm_sat_conflict_budget(solver, *consumed_conflicts);
        let should_stop = self.make_should_stop();
        let result = solver.solve_interruptible(should_stop).into_inner();
        collect_sat_stats!(self, solver);
        *consumed_conflicts = consumed_conflicts.saturating_add(solver.num_conflicts());
        result
    }
}
