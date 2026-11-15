// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Executor-first schedule of `check_sat_with_executor_fallback` for queries
//! `prepare_check_sat_query` routes to the Executor, and the fallback
//! allowance it shares with the tail fallback.

use std::time::Duration;

use ay_core::kani_compat::DetHashMap as FxHashMap;
use ay_core::time::Instant;

use super::super::context::{SmtContext, SmtLane};
use super::super::types::SmtResult;
use super::{checksat_trace_level, preprocess, scalar_route};
use crate::ChcExpr;

/// Longest native first attempt of `check_sat_with_executor_fallback`.
const NATIVE_FIRST_ATTEMPT_CAP: Duration = Duration::from_secs(2);

/// Internal-first SLICE of `check_sat_with_executor_fallback`, and whether
/// the query is a Real one the executor takes first.
///
/// The slice caps the native DPLL(T) first attempt so the (far stronger)
/// ay-dpll Executor fallback always gets budget:
///  - Real queries (`scalar_route::ScalarArith::Real`): the executor runs
///    first; the native loop, which cannot return UNSAT on them, keeps only
///    the SAT-rescue slice after an undecided session.
///  - bit-blasted BV divide/remainder: the native loop restart-thrashes to
///    its deadline and returns Unknown while the Executor decides it in ms,
///    so a trivially-UNSAT acyclic-safety branch (e.g. `n % 3 ∉ {0,1,2}`)
///    would be reported Unknown if native ate the whole budget — cap at 2s
///    even when there is no overall budget. W1-1B: a preserved wide constant
///    modulus surviving to native runs opaque-mod (spurious-Sat risk); the
///    same cap lets the exact executor fallback decide it authoritatively.
///  - FIREFLY-class checks (#23 Stage 2.5): the native loop can't decide them
///    (the executor does in ~30ms), so give native only budget/4 ∧ 2s.
///
/// Either way the fallback runs with the remainder.
pub(super) fn native_first_slice(
    expr: &ChcExpr,
    lane: SmtLane,
    total: Option<Duration>,
) -> (Option<Duration>, bool) {
    if scalar_route::is_real_executor_first(expr, lane) {
        return (Some(scalar_route::real_rescue_slice(total)), true);
    }
    let slice = if expr.contains_bv_div_rem() || expr.contains_wide_const_mod_div() {
        Some(total.map_or(NATIVE_FIRST_ATTEMPT_CAP, |t| {
            t.min(NATIVE_FIRST_ATTEMPT_CAP)
        }))
    } else {
        total.map(|t| (t / 4).min(NATIVE_FIRST_ATTEMPT_CAP))
    };
    (slice, false)
}

#[cfg(test)]
thread_local! {
    /// Budget handed to every `SmtContext` Executor session on this thread.
    static EXECUTOR_SESSION_BUDGETS: std::cell::RefCell<Vec<Duration>> =
        const { std::cell::RefCell::new(Vec::new()) };
}

/// Test hook at the single chokepoint of `SmtContext` Executor sessions.
#[cfg(test)]
pub(in crate::smt) fn record_executor_session_for_tests(budget: Duration) {
    EXECUTOR_SESSION_BUDGETS.with(|budgets| budgets.borrow_mut().push(budget));
}

#[cfg(test)]
pub(in crate::smt) fn take_executor_session_budgets_for_tests() -> Vec<Duration> {
    EXECUTOR_SESSION_BUDGETS.with(|budgets| std::mem::take(&mut *budgets.borrow_mut()))
}

impl SmtContext {
    /// Executor-first attempt of `check_sat_with_executor_fallback`: `None`
    /// when it does not apply, otherwise the verdict of the one session it ran
    /// (`Unknown` when undecided).
    ///
    /// Executor-routed queries: `prepare_check_sat_query` hands array and
    /// datatype queries to the Executor BEFORE any native DPLL(T) work, so for
    /// them the internal-first slice capped the Executor, not the native loop
    /// it was sized for. An Executor that had decided the query but was still
    /// certifying its UNSAT when the slice expired published Unknown, and the
    /// fallback re-ran the whole solve and certification on the leftover:
    /// every executor-routed UNSAT whose certification outlived budget/4 was
    /// paid twice (measured: ~0.65s of a 2.5s nested-record certification
    /// share, after which the rerun missed its deadline on slower cores). Run
    /// the fallback FIRST with the whole budget instead: the same attempt on
    /// the same expression under the same dv-retry policy, in the order
    /// `check_sat` already uses for datatype queries (#chc25-dtbv-lane-perf).
    /// The internal attempt keeps its slice but may spend only what is left,
    /// and the tail fallback, now a pure re-run, is skipped. No attempt gains
    /// wall beyond `total`, and a verdict whose limits stopped is still never
    /// reused.
    ///
    /// Two limits, both pre-existing. With Int variables the dv-retry reserve
    /// (`executor_fallback_with_dv_retry`) still splits this one session, so
    /// "the whole budget" means the whole fallback allowance. And prepare's
    /// own session on the NORMALIZED expression now runs only on what an
    /// undecided executor-first attempt leaves (it used to run first inside
    /// the slice); both see the same query, and the original-expression
    /// session is the one whose SAT models are validated against what the
    /// caller asked.
    ///
    /// Unsliced and nonlinear queries keep the old schedule (for the latter,
    /// the QF_NIA short-circuit on `check_sat`).
    ///
    /// `real` routes a pure Real query here as well (`ScalarArith::Real`):
    /// prepare never dispatches it, but the internal loop cannot return UNSAT
    /// on it, so the executor runs first and the internal loop gets only the
    /// caller's rescue slice.
    pub(super) fn executor_first_attempt(
        &self,
        expr: &ChcExpr,
        sliced: bool,
        total: Option<Duration>,
        start: Instant,
        real: bool,
    ) -> Option<SmtResult> {
        if !sliced
            || expr.contains_nonlinear_mul()
            || !(real || preprocess::dispatches_to_executor(expr))
        {
            return None;
        }
        let timeout = self.executor_fallback_budget(total, start);
        if timeout.is_zero() {
            return None;
        }
        Some(self.executor_fallback_with_dv_retry(
            expr,
            &FxHashMap::default(),
            timeout,
            checksat_trace_level() >= 1,
        ))
    }

    /// The executor-first attempt, then the sliced internal attempt on what
    /// it leaves. `Err` carries a verdict for the caller to return as is;
    /// `Ok` carries the internal result and whether the executor-first
    /// attempt ran undecided, in which case the tail fallback would be a pure
    /// re-run and is skipped.
    pub(super) fn executor_first_then_internal(
        &mut self,
        expr: &ChcExpr,
        slice: Option<Duration>,
        total: Option<Duration>,
        start: Instant,
        real: bool,
    ) -> Result<(SmtResult, bool), SmtResult> {
        let executor_first_unknown =
            match self.executor_first_attempt(expr, slice.is_some(), total, start, real) {
                Some(SmtResult::Unknown) => true,
                Some(decided) => {
                    // A decided call never reaches `prepare_check_sat_query`;
                    // run its conversion-budget prologue so the #2472 strike
                    // streak advances exactly as when prepare decided it.
                    self.begin_conversion_budget_session();
                    if self.exact_term_memory_exceeded() {
                        return Err(SmtResult::Unknown);
                    }
                    crate::smt::note_solve_progress();
                    return Err(decided);
                }
                None => false,
            };
        let slice = if executor_first_unknown {
            slice.map(|slice| total.map_or(slice, |t| slice.min(t.saturating_sub(start.elapsed()))))
        } else {
            slice
        };
        let result = match slice {
            Some(slice) if executor_first_unknown && slice.is_zero() => {
                self.begin_conversion_budget_session();
                SmtResult::Unknown
            }
            Some(slice) => {
                let prev = self.check_timeout.replace(Some(slice));
                let r = self.check_sat_internal(expr);
                self.check_timeout.set(prev);
                r
            }
            None => self.check_sat_internal(expr),
        };
        Ok((result, executor_first_unknown))
    }

    /// The executor-fallback allowance: what is left of `total` since `start`
    /// (5s without a per-check budget), clamped to the thread SMT deadline.
    pub(super) fn executor_fallback_budget(
        &self,
        total: Option<Duration>,
        start: Instant,
    ) -> Duration {
        let timeout = match total {
            Some(t) => t.checked_sub(start.elapsed()).unwrap_or(Duration::ZERO),
            None => Duration::from_secs(5),
        };
        match self.clamp_timeout_to_deadlines(Some(timeout)) {
            Ok(Some(t)) => t,
            Ok(None) => timeout,
            Err(()) => Duration::ZERO,
        }
    }
}
