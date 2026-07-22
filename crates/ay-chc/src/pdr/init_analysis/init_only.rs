// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Init-only value analysis and bad-state bound extraction.
//!
//! Contains `is_init_only_value` (checks if a variable value can only occur at
//! initialization) and `extract_bound_invariants_from_bad_state` (extracts bound
//! constraints from error states).

use crate::{ChcExpr, ChcVar, PredicateId};

use super::super::solver::PdrSolver;
use super::super::types::BoundType;
use super::{bounded_insert_init_only_value_cache, extract_bounds_recursive};

impl PdrSolver {
    /// Extract bound constraints from a bad state formula.
    ///
    /// Given a bad state like (x > 127) or (x < -128), extracts the variable,
    /// bound type, and bound value so we can try to learn the negation as an invariant.
    pub(in crate::pdr) fn extract_bound_invariants_from_bad_state(
        &self,
        expr: &ChcExpr,
    ) -> Vec<(ChcVar, BoundType, i128)> {
        let mut bounds = Vec::new();
        extract_bounds_recursive(expr, &mut bounds);
        bounds
    }

    /// Check if a variable's init value is "init-only" for a predicate.
    ///
    /// A value `v = c` is init-only if, for every self-loop clause:
    /// - `(body_v = c) AND clause_constraint => (head_v != c)` (UNSAT means OK)
    ///
    /// In other words: once you leave the initial value, you can never return to it.
    /// This is critical for init-guarded implication strengthening (#967).
    ///
    /// Example: In FUN(A, B, C, D, E), if A=0 only at init and A' = A+1 in the
    /// self-loop, then A=0 is init-only.
    pub(in crate::pdr) fn is_init_only_value(
        &mut self,
        predicate: PredicateId,
        var_name: &str,
        init_value: i128,
    ) -> bool {
        let cache_key = (predicate, var_name.to_string(), init_value);

        // Get current frame[1] revision for cache validity check
        let current_frame1_revision = self
            .frames
            .get(1)
            .map_or(0, |f| f.predicate_lemma_revision(predicate));

        if let Some(&(rev, hit)) = self.caches.init_only_value_cache.get(&cache_key) {
            // Cache hit: return if frame[1] lemmas for this predicate haven't changed.
            // If hit is true (init-only), it remains valid as frame grows (more lemmas
            // only strengthen the query). If false, it may become true with new lemmas.
            if rev == current_frame1_revision || hit {
                return hit;
            }
        }

        // Get canonical variables for this predicate
        let canonical_vars = match self.canonical_vars(predicate) {
            Some(v) => v.to_vec(),
            None => {
                bounded_insert_init_only_value_cache(
                    &mut self.caches.init_only_value_cache,
                    cache_key,
                    (current_frame1_revision, false),
                );
                return false;
            }
        };

        // Find the canonical variable index for var_name
        let var_index = canonical_vars.iter().position(|v| v.name == var_name);
        let var_index = match var_index {
            Some(i) => i,
            None => {
                bounded_insert_init_only_value_cache(
                    &mut self.caches.init_only_value_cache,
                    cache_key,
                    (current_frame1_revision, false),
                );
                return false;
            }
        };

        // Check each self-loop clause
        for clause in self.problem.clauses_defining(predicate) {
            // Skip fact clauses (no self-loop)
            if clause.body.predicates.is_empty() {
                continue;
            }

            // Skip hyperedges for simplicity
            if clause.body.predicates.len() != 1 {
                // Conservative: assume not init-only
                bounded_insert_init_only_value_cache(
                    &mut self.caches.init_only_value_cache,
                    cache_key,
                    (current_frame1_revision, false),
                );
                return false;
            }

            let (body_pred, body_args) = &clause.body.predicates[0];

            // Only check self-loops (same predicate in body and head)
            if *body_pred != predicate {
                continue;
            }

            let head_args = match &clause.head {
                crate::ClauseHead::Predicate(_, a) => a.as_slice(),
                crate::ClauseHead::False => continue,
            };

            if body_args.len() != canonical_vars.len() || head_args.len() != canonical_vars.len() {
                bounded_insert_init_only_value_cache(
                    &mut self.caches.init_only_value_cache,
                    cache_key,
                    (current_frame1_revision, false),
                );
                return false;
            }

            let clause_constraint = clause
                .body
                .constraint
                .clone()
                .unwrap_or(ChcExpr::Bool(true));

            // Get body and head variable for this index
            let body_var = body_args[var_index].clone();
            let head_var = head_args[var_index].clone();

            // Query: (body_v = init_value) AND constraint AND (head_v = init_value)
            // If SAT, the value can reoccur after a transition from it -> not init-only
            let body_eq = ChcExpr::eq(body_var.clone(), ChcExpr::Int(init_value));
            let head_eq = ChcExpr::eq(head_var, ChcExpr::Int(init_value));
            let query = ChcExpr::and(
                ChcExpr::and(body_eq.clone(), clause_constraint.clone()),
                head_eq.clone(),
            );

            // #967: Propagate equalities before SMT to avoid spurious Unknown on ITE-heavy constraints.
            let simplified = query.propagate_equalities();
            if matches!(simplified, ChcExpr::Bool(false)) {
                // Contradiction found purely by propagation: value cannot reoccur on this clause.
                continue;
            }

            let (smt_result, _) = Self::check_sat_with_ite_case_split(
                &mut self.smt,
                self.config.verbose,
                &simplified,
            );
            let mut is_sat = match smt_result {
                crate::SmtResult::Sat(_) => true,
                crate::SmtResult::Unsat
                | crate::SmtResult::UnsatWithCore(_)
                | crate::SmtResult::UnsatWithFarkas(_) => false,
                crate::SmtResult::Unknown => {
                    // Conservative: assume not init-only
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: is_init_only_value({}, {} = {}): Unknown (conservative)",
                            predicate.index(),
                            var_name,
                            init_value
                        );
                    }
                    bounded_insert_init_only_value_cache(
                        &mut self.caches.init_only_value_cache,
                        cache_key,
                        (current_frame1_revision, false),
                    );
                    return false;
                }
            };

            // Fix #967: If base check is SAT, retry with frame[1] lemmas on body.
            // This strengthens the query with learned invariants (e.g., A >= 0) that may
            // make the init value unreachable in practice, even if the raw transition allows it.
            if is_sat && self.frames.len() > 1 {
                let mut strengthened_parts = vec![body_eq, clause_constraint];
                for frame_lemma in &self.frames[1].lemmas {
                    if frame_lemma.predicate == predicate {
                        if let Some(applied) =
                            self.apply_to_args(predicate, &frame_lemma.formula, body_args)
                        {
                            strengthened_parts.push(applied);
                        }
                    }
                }
                strengthened_parts.push(head_eq);
                let strengthened_query = ChcExpr::and_all(strengthened_parts);

                let strengthened_simplified = strengthened_query.propagate_equalities();
                if matches!(strengthened_simplified, ChcExpr::Bool(false)) {
                    // UNSAT purely by propagation: under current invariants, value cannot reoccur.
                    is_sat = false;
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: is_init_only_value({}, {} = {}): init-only under frame[1] invariants (propagate_equalities)",
                            predicate.index(),
                            var_name,
                            init_value
                        );
                    }
                } else {
                    let (strengthened_result, _) = Self::check_sat_with_ite_case_split(
                        &mut self.smt,
                        self.config.verbose,
                        &strengthened_simplified,
                    );
                    match strengthened_result {
                        crate::SmtResult::Sat(_) => {
                            // Still SAT even with frame lemmas -> value can reoccur
                            is_sat = true;
                        }
                        crate::SmtResult::Unsat
                        | crate::SmtResult::UnsatWithCore(_)
                        | crate::SmtResult::UnsatWithFarkas(_) => {
                            // UNSAT with frame lemmas -> under current invariants, value cannot reoccur
                            is_sat = false;
                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: is_init_only_value({}, {} = {}): init-only under frame[1] invariants",
                                    predicate.index(),
                                    var_name,
                                    init_value
                                );
                            }
                        }
                        crate::SmtResult::Unknown => {
                            // Conservative: assume can reoccur
                            is_sat = true;
                        }
                    }
                }
            }

            if is_sat {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: is_init_only_value({}, {} = {}): SAT (can reoccur)",
                        predicate.index(),
                        var_name,
                        init_value
                    );
                }
                bounded_insert_init_only_value_cache(
                    &mut self.caches.init_only_value_cache,
                    cache_key,
                    (current_frame1_revision, false),
                );
                return false;
            }
        }

        // All self-loop clauses passed -> value is init-only
        if self.config.verbose {
            safe_eprintln!(
                "PDR: is_init_only_value({}, {} = {}): YES",
                predicate.index(),
                var_name,
                init_value
            );
        }
        bounded_insert_init_only_value_cache(
            &mut self.caches.init_only_value_cache,
            cache_key,
            (current_frame1_revision, true),
        );
        true
    }
}
