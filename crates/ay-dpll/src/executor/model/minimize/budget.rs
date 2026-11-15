// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! How much the cosmetic model minimization may spend.
//!
//! Minimization shrinks the values of a model that is already valid; it can
//! never be worth a verdict. It used to be bounded only by the solve deadline,
//! polled between candidates, so on a large BV model it ran until the deadline
//! and the `sat` it was polishing was lost: with `-model` (z3 users ask for
//! the model routinely) QF_BV Sage2 `bench_12061` answered `unknown` at
//! `-T:20` and at `-T:60`, where the plain run answers `sat` in 1.3 s; 4 of 7
//! sampled sat BV files lost their verdict the same way.
//!
//! The budget is a count of candidate checks, sized by the assertion DAG each
//! check re-evaluates, so the shrunk model is the same on every machine. A
//! time guard keeps three quarters of whatever the solve deadline still allows
//! for the validation that follows, however slow one check is.

use ay_core::kani_compat::DetHashSet;
use ay_core::time::Instant;
use ay_core::TermId;

use crate::executor::Executor;

/// Assertion-DAG term visits one minimization may spend in candidate checks.
const EVALUATION_WORK: usize = 20_000_000;

/// Candidate checks allowed however large the assertions are.
const MIN_CHECKS: usize = 16;

/// The minimization's allowance of candidate checks and wall clock.
pub(super) struct MinimizationBudget {
    checks_left: usize,
    time_guard: Option<Instant>,
}

impl MinimizationBudget {
    /// The budget for minimizing `executor`'s model now.
    pub(super) fn for_executor(executor: &Executor) -> Self {
        let size = assertion_dag_size(executor).max(1);
        let checks_left = (EVALUATION_WORK / size).max(MIN_CHECKS);
        let time_guard = executor.solve_deadline.get().map(|deadline| {
            let now = Instant::now();
            now + deadline.saturating_duration_since(now) / 4
        });
        Self {
            checks_left,
            time_guard,
        }
    }

    /// This budget's time guard with no limit on candidate checks
    /// (`--minimize-model`, which asks for the work).
    pub(super) fn without_check_limit(self) -> Self {
        Self {
            checks_left: usize::MAX,
            ..self
        }
    }

    /// A budget of exactly `checks` candidate checks and no time guard.
    #[cfg(test)]
    pub(super) fn with_checks(checks: usize) -> Self {
        Self {
            checks_left: checks,
            time_guard: None,
        }
    }

    /// Whether the budget is spent (no check left, or the time guard passed).
    pub(super) fn exhausted(&self) -> bool {
        self.checks_left == 0 || self.time_guard.is_some_and(|guard| Instant::now() >= guard)
    }

    /// Spend one candidate check. False, spending nothing, once exhausted.
    pub(super) fn take_check(&mut self) -> bool {
        if self.exhausted() {
            return false;
        }
        self.checks_left -= 1;
        true
    }
}

/// Distinct terms reachable from the executor's assertions.
fn assertion_dag_size(executor: &Executor) -> usize {
    let terms = &executor.ctx.terms;
    let mut seen: DetHashSet<TermId> = DetHashSet::default();
    let mut stack: Vec<TermId> = executor.ctx.assertions.clone();
    while let Some(term) = stack.pop() {
        if seen.insert(term) {
            stack.extend(terms.children(term));
        }
    }
    seen.len()
}

#[cfg(test)]
#[path = "budget_tests.rs"]
mod tests;
