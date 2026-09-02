// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Incremental query context for CHC engines.
//!
//! `IncrementalQueryContext` replaces the former `IncrementalSatContext` which
//! carried a persistent SAT solver, Tseitin state, and BV bitblast caches.
//! All solving is now delegated to ay-dpll's Executor via the executor adapter
//! (see `executor_adapter/mod.rs`), or to a fresh `SmtContext` as fallback.
//!
//! The context accumulates background formulas (e.g. transition relation,
//! init constraints) and combines them with per-query assumptions at solve
//! time, producing a single conjunction that is checked from scratch.

use super::context::SmtContext;
use super::types::SmtValue;
use crate::ChcExpr;
use ay_core::kani_compat::DetHashMap as FxHashMap;
use ay_core::TermStore;

/// Incremental query context that accumulates background formulas and delegates
/// solving to the Executor or a fresh SmtContext.
///
/// # Usage pattern
///
/// ```text
/// let mut ctx = IncrementalQueryContext::new();
/// ctx.assert_background(&transition_relation, &mut smt_ctx);
/// ctx.finalize_background(&smt_ctx);
///
/// // Per-obligation queries:
/// ctx.push();
/// let result = ctx.check_sat_incremental(&[lemma, neg_property], &mut smt_ctx, timeout);
/// ctx.pop();
/// ```
pub(crate) struct IncrementalQueryContext {
    /// Accumulated background formulas.
    pub(super) background_exprs: Vec<ChcExpr>,
    /// Whether finalize_background has been called.
    finalized: bool,
}

/// Result of an incremental SAT check.
#[derive(Debug)]
pub(crate) enum IncrementalCheckResult {
    Sat(FxHashMap<String, SmtValue>),
    Unsat,
    Unknown,
}

fn resources_exhausted(smt: &SmtContext, deadline: ay_core::time::Instant) -> bool {
    ay_core::time::Instant::now() >= deadline
        || TermStore::global_memory_exceeded()
        || smt
            .term_memory_budget
            .is_some_and(|limit| smt.terms.true_memory_bytes() > limit)
}

impl IncrementalQueryContext {
    /// Create a new incremental query context.
    pub(crate) fn new() -> Self {
        Self {
            background_exprs: Vec::new(),
            finalized: false,
        }
    }

    /// Assert a background formula that persists across all queries.
    ///
    /// Must be called before `finalize_background()`.
    pub(crate) fn assert_background(&mut self, expr: &ChcExpr, _smt: &mut SmtContext) {
        debug_assert!(!self.finalized, "cannot assert background after finalize");
        self.background_exprs.push(expr.clone());
    }

    /// Assert a permanent formula after finalization.
    ///
    /// Enables monotonic background growth (e.g. TRL depth encoding).
    pub(crate) fn assert_permanent(&mut self, expr: &ChcExpr, _smt: &mut SmtContext) {
        self.background_exprs.push(expr.clone());
    }

    /// Finalize background encoding.
    pub(crate) fn finalize_background(&mut self, _smt: &SmtContext) {
        self.finalized = true;
    }

    /// Refresh the variable map (no-op — kept for API compatibility).
    pub(crate) fn refresh_var_map(&mut self, _smt: &SmtContext) {}

    /// Push a new assertion scope (no-op — kept for API compatibility).
    pub(crate) fn push(&mut self) {}

    /// Pop the most recent assertion scope (no-op — kept for API compatibility).
    pub(crate) fn pop(&mut self) {}

    /// Check satisfiability of background + assumptions.
    ///
    /// Builds the conjunction of all background formulas and assumptions, then
    /// delegates to the executor adapter. Falls back to a fresh SmtContext
    /// if the executor returns Unknown.
    pub(crate) fn check_sat_incremental(
        &self,
        assumptions: &[ChcExpr],
        smt: &mut SmtContext,
        timeout: Option<std::time::Duration>,
    ) -> IncrementalCheckResult {
        // One absolute wall covers admission, both solver attempts, and final
        // publication. The historical ten-second executor default is now the
        // default for the whole query rather than being renewed before an
        // unbounded fresh-context fallback.
        let query_started = ay_core::time::Instant::now();
        let requested = timeout.unwrap_or(std::time::Duration::from_secs(10));
        let Some(requested_deadline) = query_started.checked_add(requested) else {
            return IncrementalCheckResult::Unknown;
        };
        let query_deadline = [
            smt.current_global_deadline(),
            super::context::current_thread_solve_deadline(),
            super::deadline::current_smt_deadline(),
        ]
        .into_iter()
        .flatten()
        .fold(requested_deadline, |deadline, outer| deadline.min(outer));
        if resources_exhausted(smt, query_deadline) {
            return IncrementalCheckResult::Unknown;
        }

        // Global memory budget guard (#8198): if the process has exceeded the
        // global term memory limit, all solving is unreliable — return Unknown.
        if TermStore::global_memory_exceeded() {
            return IncrementalCheckResult::Unknown;
        }
        // Per-engine term memory budget guard (#8600).
        if smt.term_memory_exceeded() {
            return IncrementalCheckResult::Unknown;
        }

        // Sub-millisecond timeout guard (#8198): the executor adapter converts
        // Duration to milliseconds; Duration::from_nanos(1) becomes 0ms which
        // skips the timeout directive entirely, causing unbounded solving.
        if let Some(t) = timeout {
            if t.as_millis() == 0 {
                return IncrementalCheckResult::Unknown;
            }
        }

        let mut conjuncts = self.background_exprs.clone();
        conjuncts.extend(assumptions.iter().cloned());
        if conjuncts.is_empty() {
            return IncrementalCheckResult::Unknown;
        }
        let combined = ChcExpr::and_all(conjuncts);
        if resources_exhausted(smt, query_deadline) {
            return IncrementalCheckResult::Unknown;
        }

        // Expression node count budget guard (#8198): if the combined expression
        // exceeds the conversion budget, solving would produce incorrect partial
        // results. Return Unknown and reset the smt conversion budget state so
        // subsequent small queries are not blocked.
        let budget_limit = super::context::MAX_CONVERSION_NODES;
        if combined.node_count(budget_limit + 1) > budget_limit {
            smt.reset_conversion_budget();
            return IncrementalCheckResult::Unknown;
        }

        // Try executor adapter (full DPLL(T) with theory support).
        let empty_equalities = FxHashMap::default();
        let result =
            super::executor_adapter::check_sat_conjunction_via_executor_with_resource_limits(
                &[combined.clone()],
                &empty_equalities,
                requested,
                Some(query_deadline),
                smt.term_memory_budget,
            );
        if resources_exhausted(smt, query_deadline) {
            return IncrementalCheckResult::Unknown;
        }
        if !matches!(result, IncrementalCheckResult::Unknown) {
            return result;
        }

        // Fallback: one fresh SmtContext under the SAME already-elapsing wall
        // and per-instance term-store ceiling as the executor attempt.
        let mut fresh_smt = SmtContext::new();
        fresh_smt.set_term_memory_budget(smt.term_memory_budget);
        fresh_smt.set_global_solve_deadline(Some(query_deadline));
        if resources_exhausted(&fresh_smt, query_deadline) {
            return IncrementalCheckResult::Unknown;
        }
        let Some(remaining) = query_deadline.checked_duration_since(ay_core::time::Instant::now())
        else {
            return IncrementalCheckResult::Unknown;
        };
        let fresh_result = fresh_smt.check_sat_with_timeout(&combined, remaining);
        if resources_exhausted(smt, query_deadline)
            || resources_exhausted(&fresh_smt, query_deadline)
        {
            return IncrementalCheckResult::Unknown;
        }
        match fresh_result {
            super::types::SmtResult::Sat(model) => IncrementalCheckResult::Sat(model),
            result if result.is_unsat() => IncrementalCheckResult::Unsat,
            _ => IncrementalCheckResult::Unknown,
        }
    }

    /// Run a fresh non-incremental query from background_exprs + assumptions.
    pub(crate) fn check_sat_fresh_query(
        &self,
        assumptions: &[ChcExpr],
        parent_smt: &SmtContext,
        timeout: Option<std::time::Duration>,
    ) -> IncrementalCheckResult {
        let started = ay_core::time::Instant::now();
        let requested = timeout.unwrap_or(std::time::Duration::from_secs(10));
        let Some(requested_deadline) = started.checked_add(requested) else {
            return IncrementalCheckResult::Unknown;
        };
        let deadline = [
            parent_smt.current_global_deadline(),
            super::context::current_thread_solve_deadline(),
            super::deadline::current_smt_deadline(),
        ]
        .into_iter()
        .flatten()
        .fold(requested_deadline, |deadline, outer| deadline.min(outer));
        if resources_exhausted(parent_smt, deadline) {
            return IncrementalCheckResult::Unknown;
        }
        let mut conjuncts = self.background_exprs.clone();
        conjuncts.extend(assumptions.iter().cloned());
        if conjuncts.is_empty() {
            return IncrementalCheckResult::Unknown;
        }
        let combined = ChcExpr::and_all(conjuncts);
        if resources_exhausted(parent_smt, deadline) {
            return IncrementalCheckResult::Unknown;
        }
        let mut fresh_smt = SmtContext::new();
        fresh_smt.set_term_memory_budget(parent_smt.term_memory_budget);
        fresh_smt.set_global_solve_deadline(Some(deadline));
        if resources_exhausted(&fresh_smt, deadline) {
            return IncrementalCheckResult::Unknown;
        }
        let Some(remaining) = deadline.checked_duration_since(ay_core::time::Instant::now()) else {
            return IncrementalCheckResult::Unknown;
        };
        let fresh_result = fresh_smt.check_sat_with_timeout(&combined, remaining);
        if resources_exhausted(parent_smt, deadline) || resources_exhausted(&fresh_smt, deadline) {
            return IncrementalCheckResult::Unknown;
        }
        match fresh_result {
            super::types::SmtResult::Sat(model) => IncrementalCheckResult::Sat(model),
            result if result.is_unsat() => IncrementalCheckResult::Unsat,
            _ => IncrementalCheckResult::Unknown,
        }
    }
}

/// Strip the namespace suffix (`__bgN`, `__qN`, `__permN`) from an auxiliary
/// variable name. Returns the base name if the variable is a namespaced
/// internal aux var (ITE/mod/div), or `None` if no namespace suffix is found.
///
/// The namespace suffixes are added by `SmtContext::rename_internal_aux_vars`
/// during `preprocess_incremental_assumption`. The original expressions in
/// `background_exprs` reference the un-namespaced names, but the SAT/LIA
/// model uses the namespaced versions. This function enables reverse mapping.
pub(crate) fn strip_namespace_suffix(name: &str) -> Option<&str> {
    // Only process internal auxiliary variable names (ITE/mod/div elimination).
    let is_aux = name.starts_with("_ite_")
        || name.starts_with("_mod_q_")
        || name.starts_with("_mod_r_")
        || name.starts_with("_div_q_")
        || name.starts_with("_div_r_");
    if !is_aux {
        return None;
    }
    // Namespace suffixes follow the pattern `__<prefix><digits>`.
    // Find the last `__` that introduces a namespace.
    if let Some(idx) = name.rfind("__") {
        let suffix = &name[idx + 2..];
        if suffix.starts_with("bg") || suffix.starts_with('q') || suffix.starts_with("perm") {
            return Some(&name[..idx]);
        }
    }
    None
}
