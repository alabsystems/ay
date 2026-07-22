// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Incremental interpolating SMT context for TPA.

use super::context::SmtContext;
use super::types::{FarkasConflict, Partition, SmtResult, SmtValue, UnsatCore};
use crate::expr_vars::expr_var_names;
use crate::farkas::compute_interpolant;
use crate::ChcExpr;
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};

/// Result of an incremental interpolating query.
///
/// This is used by TPA to extract interpolants from transition reachability queries.
#[derive(Debug, Clone)]
pub(crate) enum InterpolatingResult {
    /// Formula is satisfiable with a model (model read in tests for verification).
    Sat(FxHashMap<String, SmtValue>),
    /// Formula is unsatisfiable with an interpolant.
    ///
    /// The interpolant I satisfies:
    /// - A ⊨ I (implied by A-partition constraints)
    /// - I ∧ B is UNSAT (B is the query)
    /// - I mentions only shared variables between A and B
    Unsat(ChcExpr),
    /// Formula is unsatisfiable but no interpolant could be extracted.
    ///
    /// The `decode_misses` field counts how many Farkas conflict terms could
    /// not be converted back to `ChcExpr` during interpolant extraction.
    /// Non-zero values indicate the failure is due to decode gaps, not
    /// fundamental interpolation impossibility.
    UnsatNoInterpolant { decode_misses: usize },
    /// Solver couldn't determine satisfiability.
    Unknown,
}

/// Incremental SMT context for TPA-style interpolation queries.
///
/// This wrapper around `SmtContext` implements the pattern from Golem's
/// `SolverWrapperIncrementalWithRestarts`:
/// 1. Keeps transition constraints (A-partition) across queries
/// 2. Allows fresh query formulas (B-partition) per check
/// 3. Extracts interpolants after UNSAT
/// 4. Rebuilds periodically to prevent solver state bloat
///
/// Reference: `reference/golem/src/engine/TPA.cc:96-285`
pub(crate) struct InterpolatingSmtContext {
    /// Underlying SMT context (rebuilt periodically).
    smt: SmtContext,

    /// A-partition constraints (transition system).
    /// These are kept across queries and replayed on rebuild.
    a_constraints: Vec<ChcExpr>,

    /// Number of queries since last rebuild.
    query_count: usize,

    /// Rebuild threshold (default: 100).
    /// After this many queries, the solver is rebuilt with consolidated constraints.
    rebuild_limit: usize,

    /// Most recent interpolant from an UNSAT query.
    ///
    /// Set by `check_with_query()` when the result is UNSAT and an interpolant
    /// is successfully extracted. Cleared on SAT/Unknown results.
    ///
    /// Reference: Golem's `lastQueryTransitionInterpolant()` pattern.
    last_interpolant: Option<ChcExpr>,

    /// Count of `term_to_chc_expr` decode misses during interpolant extraction.
    ///
    /// Incremented when a conflict term from a Farkas certificate cannot be
    /// converted back to `ChcExpr`. This is a diagnostic counter — decode misses
    /// silently downgrade the interpolation result to `UnsatNoInterpolant`.
    decode_miss_count: usize,
}

impl Default for InterpolatingSmtContext {
    fn default() -> Self {
        Self::new()
    }
}

impl InterpolatingSmtContext {
    /// Default rebuild limit (100 queries).
    const DEFAULT_REBUILD_LIMIT: usize = 100;

    /// Create a new incremental interpolating context.
    pub(crate) fn new() -> Self {
        Self {
            smt: SmtContext::new(),
            a_constraints: Vec::new(),
            query_count: 0,
            rebuild_limit: Self::DEFAULT_REBUILD_LIMIT,
            last_interpolant: None,
            decode_miss_count: 0,
        }
    }

    /// Create a context with a custom rebuild limit.
    #[cfg(test)]
    pub(crate) fn with_rebuild_limit(rebuild_limit: usize) -> Self {
        Self {
            smt: SmtContext::new(),
            a_constraints: Vec::new(),
            query_count: 0,
            rebuild_limit,
            last_interpolant: None,
            decode_miss_count: 0,
        }
    }

    /// Add a constraint to the A-partition (transition system).
    ///
    /// These constraints are persistent across queries and are used as the
    /// left side of interpolation (A ⊨ I where I is the interpolant).
    pub(crate) fn assert_a(&mut self, constraint: ChcExpr) {
        self.a_constraints.push(constraint);
    }

    /// Get the current A-partition constraints.
    #[cfg(test)]
    pub(crate) fn a_constraints(&self) -> &[ChcExpr] {
        &self.a_constraints
    }

    /// Check satisfiability of A ∧ B where B is the query.
    ///
    /// If UNSAT, attempts to extract a Craig interpolant I such that:
    /// - A ⊨ I
    /// - I ∧ B is UNSAT
    /// - I mentions only variables shared between A and B
    ///
    /// The query B is not retained after the call (B-partition is fresh per query).
    ///
    /// On successful interpolant extraction, caches the interpolant for retrieval
    /// via [`last_interpolant()`](Self::last_interpolant).
    pub(crate) fn check_with_query(&mut self, query: &ChcExpr) -> InterpolatingResult {
        // Clear cached interpolant from previous query
        self.last_interpolant = None;

        self.query_count += 1;

        // Rebuild if we've exceeded the query limit
        if self.query_count > self.rebuild_limit {
            self.rebuild();
        }

        // Trivial case: empty A means we just check B
        if self.a_constraints.is_empty() {
            self.smt.reset();
            return match self.smt.check_sat(query) {
                SmtResult::Sat(model) => InterpolatingResult::Sat(model),
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                    // With empty A, interpolant is just "true" (A trivially implies true)
                    let interp = ChcExpr::Bool(true);
                    self.last_interpolant = Some(interp.clone());
                    InterpolatingResult::Unsat(interp)
                }
                SmtResult::Unknown => InterpolatingResult::Unknown,
            };
        }

        // Collect shared variables between A and B
        let a_vars: FxHashSet<String> = self
            .a_constraints
            .iter()
            .flat_map(ChcExpr::vars)
            .map(|v| v.name)
            .collect();
        let b_vars: FxHashSet<String> = expr_var_names(query);
        let shared_vars: FxHashSet<String> = a_vars.intersection(&b_vars).cloned().collect();

        // Flatten query into conjuncts for assumption-based solving
        let b_conjuncts: Vec<ChcExpr> = query.collect_conjuncts_nontrivial();

        // Reset SMT context for fresh query
        self.smt.reset();

        // Use the existing assumption-based solver with partition tracking
        let result = self
            .smt
            .check_sat_with_assumption_conjuncts(&self.a_constraints, &b_conjuncts);

        match result {
            SmtResult::Sat(model) => InterpolatingResult::Sat(model),
            SmtResult::Unknown => InterpolatingResult::Unknown,
            SmtResult::Unsat => InterpolatingResult::UnsatNoInterpolant {
                decode_misses: self.decode_miss_count,
            },
            SmtResult::UnsatWithCore(core) => {
                // Try to extract interpolant from Farkas conflicts
                let result = self.extract_interpolant_from_core(&core, &shared_vars);
                // Cache interpolant if extraction succeeded
                if let InterpolatingResult::Unsat(ref interp) = result {
                    self.last_interpolant = Some(interp.clone());
                }
                result
            }
            SmtResult::UnsatWithFarkas(conflict) => {
                // Try to extract interpolant from direct Farkas conflict
                let result = self.extract_interpolant_from_farkas(&conflict, &shared_vars);
                // Cache interpolant if extraction succeeded
                if let InterpolatingResult::Unsat(ref interp) = result {
                    self.last_interpolant = Some(interp.clone());
                }
                result
            }
        }
    }

    /// Get the most recent interpolant from an UNSAT query.
    ///
    /// Returns `Some(interpolant)` if the last call to [`check_with_query()`](Self::check_with_query)
    /// returned UNSAT and successfully extracted an interpolant.
    /// Returns `None` if the last result was SAT, Unknown, or UNSAT without interpolant.
    ///
    /// This method matches Golem's `lastQueryTransitionInterpolant()` pattern
    /// for TPA-style interpolation queries.
    ///
    /// Reference: `reference/golem/src/engine/TPA.cc:132-143`
    #[cfg(test)]
    pub(crate) fn last_interpolant(&self) -> Option<&ChcExpr> {
        self.last_interpolant.as_ref()
    }

    /// Take ownership of the last interpolant (consumes it from the cache).
    ///
    /// Useful when you want to avoid cloning a large interpolant expression.
    #[cfg(test)]
    pub(crate) fn take_last_interpolant(&mut self) -> Option<ChcExpr> {
        self.last_interpolant.take()
    }

    /// Strengthen the transition (add to A-partition).
    ///
    /// This is used when TPA discovers a new invariant that should be
    /// part of the transition abstraction.
    #[cfg(test)]
    pub(crate) fn strengthen_transition(&mut self, constraint: ChcExpr) {
        self.a_constraints.push(constraint);
    }

    /// Rebuild the solver with consolidated A constraints.
    ///
    /// This prevents solver state bloat from accumulated push/pop levels
    /// or learned clauses. The A constraints are ANDed together and
    /// re-asserted to a fresh solver.
    fn rebuild(&mut self) {
        if self.a_constraints.is_empty() {
            self.smt.reset();
            self.query_count = 0;
            return;
        }

        // Consolidate A constraints into a single conjunction
        let consolidated = self
            .a_constraints
            .iter()
            .cloned()
            .reduce(ChcExpr::and)
            .unwrap_or(ChcExpr::Bool(true));

        // Replace with consolidated constraint
        self.a_constraints.clear();
        self.a_constraints.push(consolidated);

        // Reset SMT context
        self.smt.reset();
        self.query_count = 0;
    }

    /// Get query count since last rebuild.
    #[cfg(test)]
    pub(crate) fn query_count(&self) -> usize {
        self.query_count
    }

    /// Count of `term_to_chc_expr` decode misses during interpolant extraction.
    ///
    /// When a Farkas conflict term cannot be converted back to `ChcExpr`,
    /// the interpolation silently downgrades to `UnsatNoInterpolant`. This
    /// counter tracks those events for diagnostics and regression testing.
    #[cfg(test)]
    pub(crate) fn decode_miss_count(&self) -> usize {
        self.decode_miss_count
    }

    /// Test helper: inject an undecodable term and exercise the decode-miss
    /// counting path in `try_farkas_interpolant`.
    ///
    /// Creates a `Let`-binding term in the underlying term store (which
    /// `term_to_chc_expr` does not handle) and passes a synthetic
    /// `FarkasConflict` referencing it through the interpolation path.
    #[cfg(test)]
    pub(crate) fn test_inject_decode_miss(&mut self) {
        use super::types::{FarkasConflict, Partition};
        use ay_core::FarkasAnnotation;

        // Create a Forall term — always returns None from term_to_chc_expr
        // (Let bindings are now handled since #6097, so we use Forall instead)
        let body = self.smt.terms.mk_bool(true);
        let sort = ay_core::Sort::Bool;
        let undecodable = self
            .smt
            .terms
            .mk_forall(vec![("_test_bound".to_string(), sort)], body);

        // Construct a minimal FarkasConflict with the undecodable term
        let conflict = FarkasConflict {
            conflict_terms: vec![undecodable],
            polarities: vec![true],
            farkas: FarkasAnnotation {
                coefficients: vec![num_rational::Rational64::new(1, 1)],
            },
            origins: vec![Partition::A],
        };
        let shared = FxHashSet::default();
        let _ = self.try_farkas_interpolant(&conflict, &shared);
    }

    /// Extract interpolant from UNSAT core with Farkas conflicts.
    fn extract_interpolant_from_core(
        &mut self,
        core: &UnsatCore,
        shared_vars: &FxHashSet<String>,
    ) -> InterpolatingResult {
        // Try each Farkas conflict to find a valid interpolant
        for conflict in &core.farkas_conflicts {
            if let Some(interp) = self.try_farkas_interpolant(conflict, shared_vars) {
                return InterpolatingResult::Unsat(interp);
            }
        }

        // No interpolant could be extracted
        InterpolatingResult::UnsatNoInterpolant {
            decode_misses: self.decode_miss_count,
        }
    }

    /// Extract interpolant from a direct Farkas conflict.
    fn extract_interpolant_from_farkas(
        &mut self,
        conflict: &FarkasConflict,
        shared_vars: &FxHashSet<String>,
    ) -> InterpolatingResult {
        if let Some(interp) = self.try_farkas_interpolant(conflict, shared_vars) {
            InterpolatingResult::Unsat(interp)
        } else {
            InterpolatingResult::UnsatNoInterpolant {
                decode_misses: self.decode_miss_count,
            }
        }
    }

    /// Try to compute an interpolant from a Farkas conflict.
    ///
    /// Uses the existing Farkas interpolation infrastructure.
    /// Increments `decode_miss_count` for each conflict term that
    /// `term_to_chc_expr` cannot decode.
    fn try_farkas_interpolant(
        &mut self,
        conflict: &FarkasConflict,
        shared_vars: &FxHashSet<String>,
    ) -> Option<ChcExpr> {
        // Convert conflict terms to ChcExpr, classified by partition
        let mut a_exprs: Vec<ChcExpr> = Vec::new();
        let mut b_exprs: Vec<ChcExpr> = Vec::new();

        for (i, &term_id) in conflict.conflict_terms.iter().enumerate() {
            let polarity = conflict.polarities.get(i).copied().unwrap_or(true);
            let origin = conflict.origins.get(i).copied().unwrap_or(Partition::AB);

            // Convert term to ChcExpr — count and skip decode misses
            let Some(expr) = self.smt.term_to_chc_expr(term_id) else {
                self.decode_miss_count += 1;
                return None;
            };

            // Apply polarity (negation if false)
            let expr = if polarity { expr } else { ChcExpr::not(expr) };

            // Classify by origin
            match origin {
                Partition::A => a_exprs.push(expr),
                Partition::B => b_exprs.push(expr),
                Partition::AB => {
                    // Shared constraint - include in both (Farkas will handle)
                    a_exprs.push(expr.clone());
                    b_exprs.push(expr);
                }
                Partition::Split => {
                    // Case split atoms (branch-and-bound `NeedSplit`) are excluded from
                    // interpolation. Decomposition splits (disequality/expression) inherit
                    // A/B/AB partition and are handled in the branches above.
                    // See the development design notes
                }
            }
        }

        if a_exprs.is_empty() || b_exprs.is_empty() {
            return None;
        }

        // Use the existing compute_interpolant which handles Farkas internally
        compute_interpolant(&a_exprs, &b_exprs, shared_vars)
    }
}
