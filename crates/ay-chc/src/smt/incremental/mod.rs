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
        let executor_timeout = timeout.unwrap_or(std::time::Duration::from_secs(10));
        let empty_equalities = FxHashMap::default();
        let result = super::executor_adapter::check_sat_conjunction_via_executor(
            &[combined.clone()],
            &empty_equalities,
            executor_timeout,
        );
        if !matches!(result, IncrementalCheckResult::Unknown) {
            return result;
        }

        // Fallback: fresh SmtContext.
        let mut fresh_smt = SmtContext::new();
        let fresh_result = if let Some(t) = timeout {
            fresh_smt.check_sat_with_timeout(&combined, t)
        } else {
            fresh_smt.check_sat(&combined)
        };
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
        timeout: Option<std::time::Duration>,
    ) -> IncrementalCheckResult {
        let mut conjuncts = self.background_exprs.clone();
        conjuncts.extend(assumptions.iter().cloned());
        if conjuncts.is_empty() {
            return IncrementalCheckResult::Unknown;
        }
        let combined = ChcExpr::and_all(conjuncts);
        let mut fresh_smt = SmtContext::new();
        let fresh_result = if let Some(t) = timeout {
            fresh_smt.check_sat_with_timeout(&combined, t)
        } else {
            fresh_smt.check_sat(&combined)
        };
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
