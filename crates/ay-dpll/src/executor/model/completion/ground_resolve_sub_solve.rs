// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The Phase-0 residual sub-solve of model completion, and its budget.
//!
//! `resolve_ground_constrained_absent_atoms` re-solves a small residual (the
//! ground assertions that mention absent Int/Real atoms, plus freezes of every
//! other atom they mention) on a fresh sub-`Executor`. That sub-solve used to
//! end at a 150 ms wall, and the wall decided verdicts by machine load:
//! `seq_theory_5841::test_seq_replace_decomposition_5841` and its twin in
//! `seq_soundness_5841` answered `unknown` in 56/72 and 72/72 runs of 24
//! concurrent copies (load 36-56, 2026-09-25) and `sat` alone, although the
//! sub-solve does the same 29 conflicts and 620 decisions in every run.
//!
//! How a stop inside the sub-solve used to reach the outer verdict: the
//! sub-solve ran inside the caller's evaluation-memo session, so evaluating
//! its own model left values that phase 3 read back as sequence members, and
//! a run the wall stopped before that evaluation left none. ae8cb6ed5 gave the
//! sub-solve a detached memo, which closed that channel and made those
//! verdicts a deterministic `unknown`. What remained was the wall itself: the
//! sub-solve's OWN outcome still depended on the host's speed. The counted
//! caps make its stop point a function of the problem alone (design principle
//! 4), and the sub-solve still runs in its detached memo.
//!
//! The wall clock only STOPS the sub-solve: the caller's own solve deadline
//! and interrupt when it has them, and otherwise [`SUB_SOLVE_HANG_GUARD`]. A
//! stop is never an acceptance: the sub-solve only proposes candidates, and
//! the full validation pipeline still decides every SAT answer.
//!
//! CALIBRATION (2026-09-25/26, 18-core M5 Max, test profile, instrumented
//! build never committed): every ay-dpll test target, 88 binaries and 13,010
//! tests, of which 113 reach this sub-solve in 207 calls. Run to its own end,
//! no call used more than 29 conflicts, 1,201 decisions or 1.6 s (load 40-90).
//! In 112 of the 113 tests the calls and their counters were identical across
//! six runs; the other raises an interrupt mid-solve by design. Under the old
//! wall (three runs, load 33-106), the calls that finished used at most 29
//! conflicts and 620 decisions, and 24 calls in 11 tests were cut. The caps
//! are per SAT solve and these figures are per-call totals, so each cap also
//! clears the largest single solve.

use std::time::Duration;

use ay_core::time::Instant;
use ay_core::TermId;

use crate::executor::Executor;
use crate::executor_types::{Result, SolveResult};

#[cfg(test)]
#[path = "ground_resolve_sub_solve_tests.rs"]
mod tests;

/// Per-SAT-solve conflict cap of the residual sub-solve.
///
/// In the ground lanes the decision cap binds first (no calibration call had
/// more conflicts than decisions). This cap was sized for the bit-blast lanes,
/// whose solve chain the sub-solver's `:rlimit` bounds
/// (`arm_sat_count_budget`) and which no calibration test reaches: from the
/// BV producer's release rates (`ay-proof` `producer_limits.rs`, 26k-60k
/// conflicts per second), 150 ms of test-profile bit-blasting buys a few
/// thousand conflicts, and 16,384 sits above that. It clears the most any
/// calibration call used (29) by 565x.
const SUB_SOLVE_MAX_CONFLICTS: u64 = 16_384;

/// Per-SAT-solve decision cap of the residual sub-solve.
///
/// Clears the most any calibration call used (1,201) by 6.8x and the most
/// the old wall let finish (620) by 13x. The fastest decision rate measured
/// (18.6 per ms, under load) buys about 2,800 decisions in 150 ms, so the cap
/// also covers a host twice as fast. It is also what ends a sub-solve that
/// never converges: at the slowest cost per decision measured (0.13-1.3 ms,
/// seq residuals, load 40-90), 8,192 decisions is about 1-11 s per solve,
/// inside the hang guard.
///
/// Since P4a it binds the bit-blast lanes too: they honour an explicit
/// decision limit beside their conflicts, where they once ignored it, so a
/// sub-solve that bit-blasts also ends at 8,192 decisions per solve chain
/// (often before its conflict cap: a bit-blast search can take more than one
/// decision per conflict). That is intended. The cap is the sub-solve's own
/// definition of "a small residual" on every lane, no calibration call
/// bit-blasts, and a sub-solve that stops on it only proposes nothing: the
/// caller completes the model as it would without the sub-solve.
const SUB_SOLVE_MAX_DECISIONS: u64 = 8_192;

/// Outer hang guard of the residual sub-solve. NOT a verdict budget.
///
/// The caps bound SAT work only. The slowest calibration call spends its time
/// outside the SAT solver (`regex_length_false_unsat::cvc5_issue3497_is_not_unsat`,
/// 0 conflicts and 1 decision): 0.6-1.6 s alone at load 35-80, and 1.3-1.8 s
/// under 48 concurrent copies at load 68-78. The guard sits 16x above that,
/// so it cannot end a calibration call; reaching it refuses, never accepts.
const SUB_SOLVE_HANG_GUARD: Duration = Duration::from_secs(30);

/// The envelope one residual sub-solve runs under.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct SubSolveBudget {
    max_conflicts: u64,
    max_decisions: u64,
    hang_guard: Duration,
}

impl SubSolveBudget {
    /// The production envelope.
    const DEFAULT: Self = Self {
        max_conflicts: SUB_SOLVE_MAX_CONFLICTS,
        max_decisions: SUB_SOLVE_MAX_DECISIONS,
        hang_guard: SUB_SOLVE_HANG_GUARD,
    };

    fn current() -> Self {
        #[cfg(test)]
        if let Some(budget) = SUB_SOLVE_BUDGET_TEST_OVERRIDE.with(std::cell::Cell::get) {
            return budget;
        }
        Self::DEFAULT
    }
}

#[cfg(test)]
thread_local! {
    /// Test-only envelope override, thread-scoped and uncached so one test
    /// cannot leak it into another.
    static SUB_SOLVE_BUDGET_TEST_OVERRIDE: std::cell::Cell<Option<SubSolveBudget>> =
        const { std::cell::Cell::new(None) };
}

/// Restores the previous test override on drop, including during unwinding.
#[cfg(test)]
struct SubSolveBudgetTestOverride {
    previous: Option<SubSolveBudget>,
}

#[cfg(test)]
impl Drop for SubSolveBudgetTestOverride {
    fn drop(&mut self) {
        SUB_SOLVE_BUDGET_TEST_OVERRIDE.with(|slot| slot.set(self.previous));
    }
}

/// Run this thread's residual sub-solves under `budget` until the guard drops.
#[cfg(test)]
fn override_sub_solve_budget_for_test(budget: SubSolveBudget) -> SubSolveBudgetTestOverride {
    let previous = SUB_SOLVE_BUDGET_TEST_OVERRIDE.with(|slot| slot.replace(Some(budget)));
    SubSolveBudgetTestOverride { previous }
}

impl Executor {
    /// Re-solve the residual on a fresh sub-solver under the counted envelope.
    ///
    /// Returns the sub-solver only on a definitive sub-SAT, for the caller to
    /// read candidate values from; every other outcome transfers nothing. The
    /// sub-solver never re-enters this phase (`final_lia_resolve_disabled`).
    pub(super) fn solve_ground_resolve_residual(
        &mut self,
        residual: Vec<TermId>,
        freezes: Vec<TermId>,
    ) -> Option<Executor> {
        let mut sub = Executor::new();
        sub.ctx = self.ctx.clone();
        sub.random_seed = self.random_seed;
        sub.ctx.assertions = residual;
        sub.ctx.assertions.extend(freezes);
        sub.final_lia_resolve_disabled = true;
        self.arm_ground_resolve_sub_solve(&mut sub);
        // The sub-solve and its own validation get a memo universe of their
        // own (ae8cb6ed5): nothing it evaluates may leak into the caller's
        // completion, whose model is not the sub-solve's.
        let result = super::super::eval_memo::with_detached_eval_memo(|| sub.check_sat());
        self.record_ground_resolve_sub_solve(&sub, &result);
        matches!(result, Ok(result) if result.is_sat()).then_some(sub)
    }

    /// Arm the residual sub-solver with the counted caps and the stop controls.
    ///
    /// The caps bound each of its SAT solves by conflicts and decisions, the
    /// same deterministic axes as `:rlimit` and the ground budget. The
    /// deadline is the earlier of the caller's own solve deadline and the hang
    /// guard, and the caller's interrupt flag is shared, so the sub-solve
    /// never outlives the command that asked for it.
    fn arm_ground_resolve_sub_solve(&self, sub: &mut Executor) {
        let budget = SubSolveBudget::current();
        sub.set_resource_limit(Some(budget.max_conflicts));
        sub.set_decision_limit(Some(budget.max_decisions));
        let guard = Instant::now().checked_add(budget.hang_guard);
        let deadline = match (self.solve_deadline.get(), guard) {
            (Some(caller), Some(guard)) => Some(caller.min(guard)),
            (caller, guard) => caller.or(guard),
        };
        sub.set_solve_controls(self.solve_interrupt.clone(), deadline);
    }

    /// Publish how the residual sub-solve ended, so a stop is attributable.
    ///
    /// `model_completion.ground_resolve_sub` is `sat`, `unsat`, `unknown:` plus
    /// the SMT-LIB reason (`resourceout` for a counted cap, `timeout` for the
    /// hang guard or the caller's deadline), or `error`. The counters are the
    /// sub-solve's own totals.
    fn record_ground_resolve_sub_solve(&mut self, sub: &Executor, result: &Result<SolveResult>) {
        let outcome = match result {
            Ok(result) if result.is_sat() => "sat".to_string(),
            Ok(result) if result.is_unsat() => "unsat".to_string(),
            Ok(_) => match sub.unknown_reason() {
                Some(reason) => format!("unknown:{reason}"),
                None => "unknown".to_string(),
            },
            Err(_) => "error".to_string(),
        };
        let stats = sub.statistics();
        let (conflicts, decisions) = (stats.conflicts, stats.decisions);
        self.last_statistics
            .set_string("model_completion.ground_resolve_sub", outcome);
        self.last_statistics
            .set_int("model_completion.ground_resolve_sub_conflicts", conflicts);
        self.last_statistics
            .set_int("model_completion.ground_resolve_sub_decisions", decisions);
    }
}
