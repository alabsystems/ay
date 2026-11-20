// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Executor-first routing of scalar `check_sat` queries: the Search-lane
//! Rung 0 schedule for Bool/Int queries and the every-lane schedule for
//! queries over Real variables.

use std::time::Duration;

use super::super::context::SmtLane;
use super::query_datatypes::DatatypeUse;
use super::SEARCH_LANE_INTERNAL_PRESLICE;
use crate::ChcExpr;

/// Scalar class of a query the ay-dpll executor takes first: only
/// Bool/Int/Real variables and no array / bit-vector / datatype / UF
/// structure (nonlinear multiplication is excluded by the caller).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum ScalarArith {
    /// Bool/Int only: executor-first on the Search lane.
    IntBool,
    /// At least one Real variable: executor-first on EVERY lane. The internal
    /// DPLL(T) loop runs LiaSolver on the Real atoms and, by its #5925 guard,
    /// can never return UNSAT for them (`theory_loop.rs`); it spent 18 % of
    /// all LRA-Lin CPU (37 % on inc_cas) reaching Unknown or a SAT the
    /// executor finds anyway (PERF_vs_winners_2026-09-25, row 3). After an
    /// undecided executor session it gets only [`REAL_INTERNAL_RESCUE_SLICE`].
    Real,
}

/// Internal-loop allowance for a Real query after an undecided executor
/// session (its only possible answer is SAT, e.g. when the executor's model
/// failed the strict gate). Same size as the Search-lane pre-slice it replaces.
const REAL_INTERNAL_RESCUE_SLICE: Duration = SEARCH_LANE_INTERNAL_PRESLICE;

/// The [`ScalarArith`] class of `expr`, or `None` when the executor-first
/// schedule does not apply: `claimed` by another schedule (nonlinear
/// multiplication, datatypes) or not a pure scalar query. Off the Search lane
/// only Real queries qualify.
pub(super) fn scalar_arith_query(
    expr: &ChcExpr,
    lane: SmtLane,
    claimed: bool,
) -> Option<ScalarArith> {
    if claimed {
        return None;
    }
    let features = expr.scan_features();
    if features.has_array_ops || features.has_bv || features.has_uf_apps || features.has_dt {
        return None;
    }
    let vars = expr.vars();
    // A variable-free (ground) query is decided by the internal lane's constant
    // propagation in microseconds; the adapter refuses it by design (measured:
    // 119,883 such executor-first attempts on kind2 switch_000 in 57 s).
    if vars.is_empty() {
        return None;
    }
    let mut has_real = false;
    for v in &vars {
        match v.sort {
            crate::ChcSort::Bool | crate::ChcSort::Int => {}
            crate::ChcSort::Real => has_real = true,
            _ => return None,
        }
    }
    if lane != SmtLane::Search && !has_real {
        return None;
    }
    // Shapes the SMT-LIB serializer rejects (an arithmetic comparison over a
    // Bool operand, a mixed-sort equality, ...) would be a wasted attempt: the
    // adapter fails closed before parsing (fast_2_000: 6,192 such attempts).
    // Such a query is an ENGINE defect (no clause can contain one): count it so
    // tests can assert the engines never build one (the development design notes at 9598c4206).
    let well_typed = expr
        .conjuncts()
        .iter()
        .all(|c| super::super::executor_sort_guard::unsupported_executor_expr_reason(c).is_none());
    if !well_typed {
        if lane == SmtLane::Search {
            ILL_TYPED_ENGINE_QUERIES.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        }
        return None;
    }
    Some(if has_real {
        ScalarArith::Real
    } else {
        ScalarArith::IntBool
    })
}

/// Process-wide count of Search-lane pure-scalar queries the engines handed to
/// the bridge with an ill-typed conjunct (e.g. `(<= b1 b2)` over Bool
/// variables). Every clause is well-typed, so any such query was BUILT by an
/// engine; the expected value is 0 (`pdr::typed_subst_tests`).
static ILL_TYPED_ENGINE_QUERIES: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);

#[cfg(test)]
pub(crate) fn ill_typed_engine_queries() -> usize {
    ILL_TYPED_ENGINE_QUERIES.load(std::sync::atomic::Ordering::Relaxed)
}

/// A linear query over Real variables, which both `check_sat` entry points
/// send to the executor first on `lane` (see [`ScalarArith::Real`]).
pub(super) fn is_real_executor_first(expr: &ChcExpr, lane: SmtLane) -> bool {
    scalar_arith_query(expr, lane, expr.contains_nonlinear_mul()) == Some(ScalarArith::Real)
}

/// `check_sat`'s internal-loop slice: the datatype schedule's, or the
/// Real SAT-rescue slice after an undecided executor session (`rescue`).
pub(super) fn internal_slice(
    datatype_use: DatatypeUse,
    rescue: bool,
    check_timeout: Option<Duration>,
) -> Option<Duration> {
    if rescue {
        Some(real_rescue_slice(check_timeout))
    } else {
        datatype_use.internal_slice(check_timeout)
    }
}

/// [`REAL_INTERNAL_RESCUE_SLICE`], clamped to the per-check budget.
pub(super) fn real_rescue_slice(check_timeout: Option<Duration>) -> Duration {
    check_timeout.map_or(REAL_INTERNAL_RESCUE_SLICE, |t| {
        t.min(REAL_INTERNAL_RESCUE_SLICE)
    })
}
