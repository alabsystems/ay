// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Per-predicate persistent SMT solver for PDR queries (#6358).
//!
//! Each predicate gets one persistent incremental context with activation-guarded
//! background segments for different query families (clause blocking, init
//! blocking, inductiveness). Stored in `PdrSolver::prop_solvers`.
//!
//! This matches Z3 Spacer's `prop_solver` pattern:
//! - One solver per predicate (not per clause/fact/lane)
//! - Permanent background: transition relation fragments
//! - Level-scoped: frame lemmas via existing activation literals
//! - Query-scoped: clause/fact selection via query activation variables
//!
//! Reference: `reference/z3/src/muz/spacer/spacer_prop_solver.h:45-48`

use crate::smt::IncrementalCheckResult;
use crate::smt::IncrementalPdrContext;
use crate::smt::SmtValue;
use crate::ChcExpr;
use ay_core::kani_compat::DetHashMap as FxHashMap;
use std::time::Duration;

/// Identifies a reusable background segment within a per-predicate solver.
///
/// Each segment corresponds to a query family that shares the same background
/// constraints. The segment's formulas are asserted once, guarded by an
/// activation variable, and toggled per query via assumptions.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(super) enum SegmentKey {
    /// Clause predecessor check: clause body constraint for a specific clause.
    ClauseBlocking { clause_index: usize },
    /// Clause+fact predecessor check at level 0: clause + fact + init-match.
    ClauseFactBlocking {
        clause_index: usize,
        fact_index: usize,
    },
    /// Init-blocking check: fact constraint for a specific init fact.
    InitBlocking { fact_index: usize },
    /// Level-0 inductiveness: clause + fact + init-match background.
    InitInductiveness {
        clause_index: usize,
        fact_index: usize,
    },
    /// Clause inductiveness: clause body constraint.
    Inductiveness { clause_index: usize },
}

/// Activation state for a registered background segment.
struct SegmentActivation {
    /// SAT variable (1-based) controlling this segment.
    /// Segment is active when `NOT act_var` is assumed.
    act_var: u32,
}

/// Per-predicate persistent SMT solver for PDR queries.
///
/// Owns a single `IncrementalPdrContext` that persists across all query types
/// for this predicate. Different query families (blocking, inductiveness, etc.)
/// are distinguished by activation-guarded background segments, not by separate
/// solver instances.
///
/// This is the Z3 Spacer `prop_solver` pattern: one solver per predicate,
/// transition relation + frame lemmas encoded once, query-specific background
/// selected via SAT assumptions.
pub(in crate::pdr) struct PredicatePropSolver {
    /// The persistent incremental context — owns the SAT solver, Tseitin state,
    /// and theory integration.
    pub(crate) ctx: IncrementalPdrContext,
    /// Registered background segments, keyed by query family.
    segments: FxHashMap<SegmentKey, SegmentActivation>,
}

impl PredicatePropSolver {
    /// Create a new per-predicate solver.
    ///
    /// The caller should assert permanent background (transition relation
    /// fragments common to all queries for this predicate) via `ctx` before
    /// calling `finalize()`.
    pub(super) fn new() -> Self {
        Self {
            ctx: IncrementalPdrContext::new(),
            segments: FxHashMap::default(),
        }
    }

    /// Finalize permanent background. Must be called before any queries.
    pub(super) fn finalize(&mut self) {
        self.ctx.finalize_background();
    }

    /// Register a guarded background segment for a query family.
    ///
    /// The `expr` is encoded as `(expr OR act_var)` in the persistent SAT solver.
    /// The segment is active only when `NOT act_var` is assumed during a query.
    ///
    /// Returns the `SegmentKey` for use in query methods. If the segment was
    /// already registered, this is a no-op.
    pub(super) fn register_segment(&mut self, key: SegmentKey, expr: &ChcExpr) {
        if self.segments.contains_key(&key) {
            return;
        }
        let act_var = self.ctx.alloc_query_activation();
        self.ctx.assert_background_guarded(expr, act_var);
        self.segments.insert(key, SegmentActivation { act_var });
    }

    /// Register multiple guarded background expressions under a single segment key.
    ///
    /// All expressions share the same activation variable — they are all active
    /// or all inactive together. This is useful when a query family has multiple
    /// background conjuncts (e.g., clause_constraint AND fact_constraint AND init_match).
    pub(super) fn register_segment_multi(&mut self, key: SegmentKey, exprs: &[ChcExpr]) {
        if self.segments.contains_key(&key) {
            return;
        }
        let act_var = self.ctx.alloc_query_activation();
        for expr in exprs {
            self.ctx.assert_background_guarded(expr, act_var);
        }
        self.segments.insert(key, SegmentActivation { act_var });
    }

    /// Assert a lemma at a specific frame level (delegates to the underlying context).
    pub(super) fn assert_lemma_at_level(&mut self, lemma: &ChcExpr, level: usize) {
        self.ctx.assert_lemma_at_level(lemma, level);
    }

    /// Check satisfiability with specific segments active.
    ///
    /// `active_segments`: segment keys whose background should constrain the query.
    /// All other registered segments are deactivated.
    ///
    /// This is the core query primitive. The narrow wrapper methods
    /// (`check_already_blocked`, `check_clause_blocking`, etc.) build on this.
    pub(super) fn check_with_segments(
        &mut self,
        level: usize,
        assumptions: &[ChcExpr],
        active_segments: &[SegmentKey],
        timeout: Option<Duration>,
        phase_seed_model: Option<&FxHashMap<String, SmtValue>>,
    ) -> IncrementalCheckResult {
        // Build activation lists: active segments get NOT act_var, all others get act_var.
        let mut active_acts = Vec::new();
        let mut inactive_acts = Vec::new();

        for (key, seg) in &self.segments {
            if active_segments.contains(key) {
                active_acts.push(seg.act_var);
            } else {
                inactive_acts.push(seg.act_var);
            }
        }

        self.ctx.check_sat_at_level_with_activations(
            level,
            assumptions,
            &active_acts,
            &inactive_acts,
            timeout,
            phase_seed_model,
        )
    }

    // --- Narrow wrapper methods (Packet C/D will wire these to call sites) ---

    /// Already-blocked check: frame lemmas + query state, no extra background.
    pub(super) fn check_already_blocked(
        &mut self,
        level: usize,
        state: &ChcExpr,
        timeout: Option<Duration>,
    ) -> IncrementalCheckResult {
        // AlreadyBlocked has no guarded segments — only frame lemmas constrain.
        self.check_with_segments(level, &[state.clone()], &[], timeout, None)
    }

    /// Clause predecessor check: clause body constraint active.
    pub(super) fn check_clause_blocking(
        &mut self,
        level: usize,
        clause_index: usize,
        assumptions: &[ChcExpr],
        timeout: Option<Duration>,
        phase_seed_model: Option<&FxHashMap<String, SmtValue>>,
    ) -> IncrementalCheckResult {
        let key = SegmentKey::ClauseBlocking { clause_index };
        self.check_with_segments(level, assumptions, &[key], timeout, phase_seed_model)
    }

    /// Clause+fact predecessor check at level 0.
    pub(super) fn check_clause_fact_blocking(
        &mut self,
        clause_index: usize,
        fact_index: usize,
        assumptions: &[ChcExpr],
        timeout: Option<Duration>,
        phase_seed_model: Option<&FxHashMap<String, SmtValue>>,
    ) -> IncrementalCheckResult {
        let key = SegmentKey::ClauseFactBlocking {
            clause_index,
            fact_index,
        };
        // Level 0 for init-level predecessor queries.
        self.check_with_segments(0, assumptions, &[key], timeout, phase_seed_model)
    }

    /// Init-blocking check: fact constraint active.
    pub(super) fn check_init_blocking(
        &mut self,
        level: usize,
        fact_index: usize,
        assumptions: &[ChcExpr],
        timeout: Option<Duration>,
    ) -> IncrementalCheckResult {
        let key = SegmentKey::InitBlocking { fact_index };
        self.check_with_segments(level, assumptions, &[key], timeout, None)
    }

    /// Level-0 inductiveness check: clause + fact + init-match active.
    pub(super) fn check_init_inductiveness(
        &mut self,
        level: usize,
        clause_index: usize,
        fact_index: usize,
        assumptions: &[ChcExpr],
        timeout: Option<Duration>,
    ) -> IncrementalCheckResult {
        let key = SegmentKey::InitInductiveness {
            clause_index,
            fact_index,
        };
        self.check_with_segments(level, assumptions, &[key], timeout, None)
    }

    /// Clause inductiveness check: clause body constraint active.
    pub(super) fn check_inductiveness(
        &mut self,
        level: usize,
        clause_index: usize,
        assumptions: &[ChcExpr],
        timeout: Option<Duration>,
        phase_seed_model: Option<&FxHashMap<String, SmtValue>>,
    ) -> IncrementalCheckResult {
        let key = SegmentKey::Inductiveness { clause_index };
        self.check_with_segments(level, assumptions, &[key], timeout, phase_seed_model)
    }

    /// Hyperedge predecessor check: mixed_summary passed entirely as assumptions.
    ///
    /// Unlike linear clause queries, hyperedge queries involve frame constraints
    /// from multiple body predicates (may-summaries) and must-summaries, all
    /// bundled into the mixed_summary by `get_edge_mixed_summary()`. Since the
    /// mixed_summary is dynamic per `last_may_index`, it is passed as an
    /// assumption rather than registered as a persistent segment.
    ///
    /// The persistent solver still benefits from Tseitin caching and SAT state.
    pub(super) fn check_hyperedge_blocking(
        &mut self,
        level: usize,
        assumptions: &[ChcExpr],
        timeout: Option<Duration>,
        phase_seed_model: Option<&FxHashMap<String, SmtValue>>,
    ) -> IncrementalCheckResult {
        // No guarded segments — the mixed_summary in `assumptions` already
        // includes clause constraint + body frame/must-summary constraints.
        self.check_with_segments(level, assumptions, &[], timeout, phase_seed_model)
    }

    /// Utility feasibility check: arbitrary formula with no active segments.
    ///
    /// Used for standalone SAT checks (e.g., interpolation A-side feasibility)
    /// that don't correspond to a PDR query family but still benefit from the
    /// persistent solver's Tseitin cache and SAT state.
    pub(super) fn check_feasibility(
        &mut self,
        level: usize,
        formula: &ChcExpr,
        timeout: Option<Duration>,
    ) -> IncrementalCheckResult {
        self.check_with_segments(level, &[formula.clone()], &[], timeout, None)
    }
}
