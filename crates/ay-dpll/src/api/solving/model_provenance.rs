// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model provenance extraction (#8153).
//!
//! After a SAT result, extracts provenance information for each declared
//! variable: whether its value was a decision, propagation, or default
//! assignment, using real SAT trail data when available.

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::kani_compat::DetHashSet as HashSet;

use crate::api::types::{AssignmentReason, ModelProvenance, SolverError, Term, VariableProvenance};
use crate::api::Solver;

impl Solver {
    /// Model provenance: why each declared variable received its model value.
    ///
    /// After `check_sat()` returns `Sat`, this method returns provenance
    /// information for each declared variable, indicating whether its value
    /// was:
    /// - A decision by the CDCL branching heuristic (with real decision level)
    /// - Forced by unit propagation (BCP)
    /// - A default value for an unconstrained variable
    ///
    /// Returns `None` if:
    /// - The last result was not SAT
    /// - No model is available
    ///
    /// # Note
    ///
    /// This is a consumer-facing API that provides a simplified view of the
    /// solver's internal assignment trail.  For variables in the UNSAT core
    /// of a push/pop scope, use [`annotated_unsat_core`](Self::annotated_unsat_core)
    /// instead.
    #[must_use]
    pub fn model_provenance(&self) -> Option<ModelProvenance> {
        self.try_model_provenance().ok()
    }

    /// Fallible version of [`model_provenance`](Self::model_provenance).
    ///
    /// Returns a typed error distinguishing:
    /// - [`SolverError::NoResult`] -- no `check_sat` has been called
    /// - [`SolverError::NotSat`] -- last result was not SAT
    /// - [`SolverError::ModelGenerationFailed`] -- model extraction failed
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_model_provenance(&self) -> Result<ModelProvenance, SolverError> {
        // Verify last result was SAT
        let last_result = self.executor.last_result().ok_or(SolverError::NoResult)?;
        if !last_result.is_sat() {
            return Err(SolverError::NotSat);
        }

        let trail = self.executor.last_trail_provenance();
        let assertions = self.assertions();

        // Precompute the set of all TermIds reachable from assertions.
        // Single DFS walk: O(A*D) total, then O(1) lookup per variable.
        // This replaces the old per-variable recursive walk which was
        // O(V*A*D) worst case.
        let assertion_term_ids = self.collect_assertion_term_ids(&assertions);

        let mut entries = Vec::new();
        let declared: Vec<(String, Term)> = self
            .declared_variables()
            .map(|(name, term)| (name.to_string(), term))
            .collect();

        for (name, term) in &declared {
            let reason =
                self.classify_variable_reason(term, trail, &assertions, &assertion_term_ids);
            entries.push(VariableProvenance {
                name: name.clone(),
                term: *term,
                reason,
            });
        }

        Ok(ModelProvenance::new(entries))
    }

    /// Precompute the set of all `TermId`s reachable from any assertion.
    ///
    /// Uses an iterative DFS to walk every assertion term tree once,
    /// collecting all encountered `TermId`s into a `HashSet`. This is
    /// O(total nodes across all assertions) and enables O(1) membership
    /// checks, replacing the previous O(V * A * D) per-variable recursive
    /// walk.
    fn collect_assertion_term_ids(&self, assertions: &[Term]) -> HashSet<ay_core::TermId> {
        let terms = self.terms();
        let mut seen = HashSet::default();
        let mut stack: Vec<ay_core::TermId> = assertions.iter().map(|a| a.0).collect();

        while let Some(tid) = stack.pop() {
            if seen.insert(tid) {
                for child in terms.children(tid) {
                    stack.push(child);
                }
            }
        }

        seen
    }

    /// Classify a variable's assignment reason using trail data or assertion fallback.
    ///
    /// When SAT trail provenance is available (incremental mode with persistent SAT
    /// solver), uses real decision levels and propagation detection. For propagated
    /// variables, converts the captured reason clause variable indices back to Term
    /// handles to populate `antecedent_terms` (#8307). Otherwise falls back to the
    /// assertion-analysis heuristic using the precomputed assertion term set for
    /// O(1) lookup.
    fn classify_variable_reason(
        &self,
        term: &Term,
        trail: Option<&HashMap<u32, (u32, bool, Vec<u32>)>>,
        assertions: &[Term],
        assertion_term_ids: &HashSet<ay_core::TermId>,
    ) -> AssignmentReason {
        // Trail-based classification (incremental mode)
        if let Some(trail) = trail {
            if let Some(var_idx) = self.executor.last_model_term_to_var(term.0) {
                if let Some((level, is_propagated, antecedent_vars)) = trail.get(&var_idx) {
                    return if *is_propagated {
                        // Convert SAT variable indices to Term handles (#8307)
                        let var_to_term = self.executor.last_var_to_term();
                        let antecedent_terms: Vec<Term> = antecedent_vars
                            .iter()
                            .filter_map(|&var_idx| {
                                var_to_term
                                    .and_then(|vtm| vtm.get(&var_idx))
                                    .map(|&tid| Term(tid))
                            })
                            .collect();
                        AssignmentReason::Propagation { antecedent_terms }
                    } else {
                        AssignmentReason::Decision { level: *level }
                    };
                }
                // Variable has a SAT mapping but was not assigned -> Default
                return AssignmentReason::Default;
            }
        }

        // Fallback: assertion-based heuristic (non-incremental mode)
        // O(1) lookup in precomputed set instead of per-variable recursive walk.
        if assertions.is_empty() {
            AssignmentReason::Default
        } else if assertion_term_ids.contains(&term.0) {
            AssignmentReason::Decision { level: 0 }
        } else {
            AssignmentReason::Default
        }
    }
}
