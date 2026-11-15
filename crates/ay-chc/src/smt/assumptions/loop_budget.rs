// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Wall-clock budget of the assumption-mode DPLL(T) loop
//! ([`SmtContext::check_sat_with_assumption_conjuncts`]).
//!
//! Every other `SmtContext` check clamps its per-check timeout to the thread's
//! deadlines — the contract of [`crate::smt::deadline`]: "a hard wall-clock
//! budget that every `SmtContext::check_sat*` call on the current thread
//! respects" — and stops for a cancelled portfolio lane. The assumption-mode
//! loop, the solver behind PDR's IUC generalization, PDKind's explanations and
//! the Farkas-history interpolation cascade, observed none of them: it called
//! the uninterruptible `solve_with_assumptions`, built each iteration's
//! `LiaSolver` with no deadline, and was bounded only by its 1,000,000-split
//! cap. A branch-and-bound that does not converge — a parity conflict such as
//! `B = 2A ∧ B = 2E - 3` over unbounded `A`, `E`, whose LP relaxation stays
//! feasible after every split — therefore kept splitting long after the owning
//! engine's deadline. Observed 2026-09-26 on `half_true_modif_m_000`
//! (`modular_hints_1362`): one interpolation query entered with 0.88 s of the
//! non-inlined PDR stage left and was still splitting (5,500 splits, 11,000
//! iterations) 100 s later, holding the adaptive worker far past its 35 s
//! budget.
//!
//! SOUNDNESS: the budget only ever turns a check into `Unknown` earlier, which
//! every caller already treats as "no conclusion".

use crate::smt::context::SmtContext;
use ay_core::time::Instant;

impl SmtContext {
    /// `check_sat`'s wall-clock budget as one absolute boundary: the per-check
    /// timeout (`check_timeout`, e.g. PDR's 5 s main-loop cap) clamped to this
    /// context's global solve deadline and the thread's effective deadline by
    /// `clamp_timeout_to_deadlines`, exactly as `check_sat_internal` clamps
    /// it, and counted from `start`. `Err(())`: a deadline already passed or
    /// the lane is cancelled. `Ok(None)`: nothing bounds the check.
    pub(in crate::smt) fn check_budget_deadline(
        &self,
        start: Instant,
    ) -> Result<Option<Instant>, ()> {
        let timeout = self.clamp_timeout_to_deadlines(self.current_timeout())?;
        Ok(timeout.and_then(|timeout| start.checked_add(timeout)))
    }
}

/// The boundaries one assumption-mode check must observe: `check_sat`'s
/// budget ([`SmtContext::check_budget_deadline`]: the per-check timeout, the
/// context's global solve deadline and the thread's effective deadline), plus
/// the owning portfolio lane's cancellation — the same set
/// `run_check_sat_theory_loop` polls. Without the per-check timeout, a
/// divergent query under PDR's 5 s main-loop cap ran until the solve deadline
/// (2026-09-26 review: a 1 s check timeout was still splitting at 12 s).
pub(super) struct AssumptionLoopBudget {
    deadline: Option<Instant>,
}

impl AssumptionLoopBudget {
    /// Capture the budget at entry. `None` when it is already spent (a
    /// deadline passed, the per-check timeout is zero or the lane was
    /// cancelled): the check must answer `Unknown` without starting, as
    /// `check_sat` refuses a spent budget.
    pub(super) fn capture(ctx: &SmtContext) -> Option<Self> {
        let deadline = ctx.check_budget_deadline(Instant::now()).ok()?;
        let budget = Self { deadline };
        (!budget.exhausted()).then_some(budget)
    }

    /// True once the deadline has passed or the lane has been cancelled.
    /// Polled at every DPLL(T) iteration and inside the SAT search.
    pub(super) fn exhausted(&self) -> bool {
        crate::smt::deadline::lane_cancelled()
            || self
                .deadline
                .is_some_and(|deadline| Instant::now() >= deadline)
    }

    /// Hand the budget to an iteration's `LiaSolver`, so its own procedures
    /// (cuts, Diophantine and finite-domain search, the IntSat probe) stop at
    /// the same boundary instead of finishing the iteration first.
    pub(super) fn arm(&self, lia: &mut ay_lia::LiaSolver<'_>) {
        if let Some(deadline) = self.deadline {
            lia.set_deadline(deadline);
        }
        lia.set_timeout_callback(crate::smt::deadline::lane_cancelled);
    }
}

#[cfg(test)]
mod tests;
