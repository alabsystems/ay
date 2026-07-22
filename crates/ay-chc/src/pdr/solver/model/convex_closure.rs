// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Convex closure generalization and affine invariant discovery from blocked states.

use super::super::{
    detect_triangular_pattern, ChcExpr, ChcOp, ChcVar, Counterexample, FxHashMap, FxHashSet, Lemma,
    PdrSolver, PredicateId,
};

impl PdrSolver {
    /// Try to discover invariant constraints via convex closure.
    /// Called periodically when we have enough blocked states for a predicate.
    /// Returns additional lemmas to add if convex closure finds useful constraints.
    pub(in crate::pdr::solver) fn try_convex_closure_generalization(
        &mut self,
        predicate: PredicateId,
        level: usize,
    ) -> Vec<Lemma> {
        if !self.config.use_convex_closure {
            return Vec::new();
        }

        let entries = match self.caches.blocked_states_for_convex.get(&predicate) {
            Some(e) => e,
            None => return Vec::new(),
        };

        // #1362 D1: Lowered from 5→3 to allow CC to fire earlier for problems
        // that produce few blocked states (e.g., s_multipl_14 with 4 predicates).
        // MAX_DATA_POINTS=50 circuit breaker prevents runaway cost.
        const MIN_DATA_POINTS: usize = 3;
        if entries.len() < MIN_DATA_POINTS {
            return Vec::new();
        }

        // CIRCUIT BREAKER #1: Stop running CC after too many data points.
        // After ~50 blocked states, patterns are either found or won't emerge.
        // This prevents runaway CC on hard instances (fixes #107).
        const MAX_DATA_POINTS: usize = 50;
        if entries.len() > MAX_DATA_POINTS {
            return Vec::new();
        }

        // #1362 D1: Lowered from 5→3 to match MIN_DATA_POINTS.
        const RUN_INTERVAL: usize = 3;
        if entries.len() % RUN_INTERVAL != 0 {
            return Vec::new();
        }

        // Get canonical variables for this predicate
        let vars = match self.canonical_vars(predicate) {
            Some(v) => v.to_vec(),
            None => return Vec::new(),
        };

        // Filter to numeric variables supported by the current i64-based CC pipeline.
        // Wider bit-vectors are excluded to avoid silently truncating samples.
        let numeric_vars: Vec<ChcVar> = vars
            .into_iter()
            .filter(|v| Self::supports_i64_numeric_sort(&v.sort))
            .collect();

        if numeric_vars.is_empty() {
            return Vec::new();
        }

        // Set up convex closure engine
        self.convex_closure_engine.reset(numeric_vars.clone());

        // Collect and deduplicate data points from blocked states.
        // Duplicate points don't add information and can cause degenerate CC runs.
        let mut seen_points: FxHashSet<Vec<i64>> =
            FxHashSet::with_capacity_and_hasher(entries.len(), Default::default());

        for entry in entries {
            let data_point: Vec<i64> = numeric_vars
                .iter()
                .map(|v| *entry.get(&v.name).unwrap_or(&0))
                .collect();
            if seen_points.insert(data_point.clone()) {
                self.convex_closure_engine.add_data_point(&data_point);
            }
        }

        // Diversity check: need at least 2 distinct points for CC to be meaningful
        if seen_points.len() < 2 {
            return Vec::new();
        }

        // Compute convex closure
        let result = self.convex_closure_engine.compute();

        if result.is_empty() {
            return Vec::new();
        }

        if self.config.verbose {
            safe_eprintln!(
                "PDR: Convex closure found {} equalities, {} bounds, {} divisibility constraints",
                result.equalities.len(),
                result.bounds.len(),
                result.divisibility.len()
            );
        }

        // Convert discovered constraints to lemmas
        let mut lemmas = Vec::new();

        // CIRCUIT BREAKER #2: Limit inductiveness checks per CC run.
        // Each is_lemma_inductive call does SMT queries. Limit to prevent blowup.
        const MAX_EQUALITIES_TO_CHECK: usize = 3;

        // Get canonical vars for clause-local pre-filtering
        let canonical_vars = match self.canonical_vars(predicate) {
            Some(v) => v.to_vec(),
            None => return Vec::new(),
        };

        // Add equality constraints as lemmas
        for eq in result.equalities.iter().take(MAX_EQUALITIES_TO_CHECK) {
            // Pre-filter: quick clause-local preservation check (short timeout, no full frame).
            // This catches obviously non-preserved equalities cheaply before the expensive
            // is_lemma_inductive call that checks full PDR inductiveness.
            if !self.is_chc_expr_preserved_by_transitions(predicate, eq, &canonical_vars) {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: Convex closure equality {} failed clause-local preservation",
                        eq
                    );
                }
                continue;
            }

            // Full inductiveness check (uses entire frame, more expensive)
            if self.is_lemma_inductive(eq, predicate, level) {
                if self.config.verbose {
                    safe_eprintln!("PDR: Convex closure equality lemma: {}", eq);
                }
                lemmas.push(Lemma::new(predicate, eq.clone(), level));
            }
        }

        // BV range invariants such as `1 <=u x` are the useful convex-closure output
        // for #5877. Bounds are still noisy on some problems, so prefer lower bounds
        // first and cap the number of full inductiveness checks.
        const MAX_BOUNDS_TO_CHECK: usize = 8;
        for bound in result
            .bounds
            .iter()
            .filter(|bound| Self::prefers_convex_lower_bound(bound))
            .chain(
                result
                    .bounds
                    .iter()
                    .filter(|bound| !Self::prefers_convex_lower_bound(bound)),
            )
            .take(MAX_BOUNDS_TO_CHECK)
        {
            if !self.is_chc_expr_preserved_by_transitions(predicate, bound, &canonical_vars) {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: Convex closure bound {} failed clause-local preservation",
                        bound
                    );
                }
                continue;
            }

            if self.is_lemma_inductive(bound, predicate, level) {
                if self.config.verbose {
                    safe_eprintln!("PDR: Convex closure bound lemma: {}", bound);
                }
                lemmas.push(Lemma::new(predicate, bound.clone(), level));
            }
        }

        // Divisibility/parity constraints are sometimes required (e.g. dillig02_m), but can also
        // lead to SMT Unknown depending on query shape. Treat them like equalities: a cheap
        // clause-local preservation check (short timeout) followed by the full inductiveness check.
        const MAX_DIVISIBILITY_TO_CHECK: usize = 2;
        for div in result.divisibility.iter().take(MAX_DIVISIBILITY_TO_CHECK) {
            if !self.is_chc_expr_preserved_by_transitions(predicate, div, &canonical_vars) {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: Convex closure divisibility {} failed clause-local preservation",
                        div
                    );
                }
                continue;
            }

            if self.is_lemma_inductive(div, predicate, level) {
                if self.config.verbose {
                    safe_eprintln!("PDR: Convex closure divisibility lemma: {}", div);
                }
                lemmas.push(Lemma::new(predicate, div.clone(), level));
            }
        }

        // Quadratic pattern detection: s_multipl benchmarks have triangular number growth
        // where c = k*(k+1)/2 + offset. When convex closure doesn't find useful patterns,
        // check if blocked states fit this pattern and emit linear approximations.
        if lemmas.is_empty() && numeric_vars.len() >= 2 {
            // Collect all blocked state data points
            let data_points: Vec<Vec<i64>> = seen_points.iter().cloned().collect();

            if data_points.len() >= 4 {
                // Try each pair of variables to detect triangular pattern
                for i in 0..numeric_vars.len() {
                    for j in 0..numeric_vars.len() {
                        if i == j {
                            continue;
                        }
                        // Try: data_points[j] = data_points[i] * (data_points[i] + 1) / 2 + offset
                        // Equivalent: 2 * data_points[j] = data_points[i]^2 + data_points[i] + 2*offset
                        if let Some(bounds) = detect_triangular_pattern(
                            &data_points,
                            i,
                            j,
                            &numeric_vars,
                            self.config.verbose,
                        ) {
                            for bound in bounds {
                                // Test inductiveness before adding
                                if self.is_chc_expr_preserved_by_transitions(
                                    predicate,
                                    &bound,
                                    &canonical_vars,
                                ) && self.is_lemma_inductive(&bound, predicate, level)
                                {
                                    if self.config.verbose {
                                        safe_eprintln!("PDR: Quadratic pattern lemma: {}", bound);
                                    }
                                    lemmas.push(Lemma::new(predicate, bound, level));
                                }
                            }
                        }
                    }
                }
            }
        }

        lemmas
    }

    /// Try to discover affine invariants from spurious counterexample step values.
    ///
    /// Called during spurious CEX handling to extract numeric values from each CEX step
    /// and feed them to convex closure for affine pattern detection.
    ///
    /// Returns true if any new inductive lemma was learned.
    pub(in crate::pdr::solver) fn try_affine_discovery_from_cex(
        &mut self,
        cex: &Counterexample,
    ) -> bool {
        if !self.config.use_convex_closure {
            return false;
        }

        // Group CEX step values by predicate
        let mut values_by_pred: FxHashMap<PredicateId, Vec<FxHashMap<String, i64>>> =
            FxHashMap::default();
        for step in &cex.steps {
            if !step.assignments.is_empty() {
                values_by_pred
                    .entry(step.predicate)
                    .or_default()
                    .push(step.assignments.clone());
            }
        }

        if values_by_pred.is_empty() {
            return false;
        }

        let mut learned_any = false;

        // For each predicate with data, try convex closure discovery
        for (predicate, step_values) in values_by_pred {
            // Need at least 2 data points for meaningful convex closure
            if step_values.len() < 2 {
                continue;
            }

            // Get canonical variables for this predicate
            let vars = match self.canonical_vars(predicate) {
                Some(v) => v.to_vec(),
                None => continue,
            };

            // Filter to numeric variables supported by the current i64-based CC pipeline.
            let numeric_vars: Vec<ChcVar> = vars
                .into_iter()
                .filter(|v| Self::supports_i64_numeric_sort(&v.sort))
                .collect();

            if numeric_vars.is_empty() {
                continue;
            }

            // Reset convex closure engine for this predicate
            self.convex_closure_engine.reset(numeric_vars.clone());

            // Deduplicate data points
            let mut seen_points: FxHashSet<Vec<i64>> =
                FxHashSet::with_capacity_and_hasher(step_values.len(), Default::default());

            for entry in &step_values {
                let data_point: Vec<i64> = numeric_vars
                    .iter()
                    .map(|v| *entry.get(&v.name).unwrap_or(&0))
                    .collect();
                if seen_points.insert(data_point.clone()) {
                    self.convex_closure_engine.add_data_point(&data_point);
                }
            }

            // Need at least 2 distinct points
            if seen_points.len() < 2 {
                continue;
            }

            // Compute convex closure
            let result = self.convex_closure_engine.compute();

            if result.equalities.is_empty()
                && result.bounds.is_empty()
                && result.divisibility.is_empty()
            {
                continue;
            }

            if self.config.verbose {
                safe_eprintln!(
                    "PDR: Spurious CEX convex closure found {} equalities, {} bounds, {} divisibility constraints for pred {}",
                    result.equalities.len(),
                    result.bounds.len(),
                    result.divisibility.len(),
                    predicate.index()
                );
            }

            // Check equalities for inductiveness and add as lemmas
            const MAX_EQUALITIES_TO_CHECK: usize = 3;
            const MAX_BOUNDS_TO_CHECK: usize = 8;
            const MAX_DIVISIBILITY_TO_CHECK: usize = 2;

            let canonical_vars = match self.canonical_vars(predicate) {
                Some(v) => v.to_vec(),
                None => continue,
            };

            for eq in result.equalities.iter().take(MAX_EQUALITIES_TO_CHECK) {
                // Pre-filter: quick clause-local preservation check
                if !self.is_chc_expr_preserved_by_transitions(predicate, eq, &canonical_vars) {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: Spurious CEX equality {} failed clause-local preservation",
                            eq
                        );
                    }
                    continue;
                }

                // Try inductiveness at level 0 first (strongest), then level 1
                let level = if self.is_lemma_inductive(eq, predicate, 0) {
                    0
                } else if self.is_lemma_inductive(eq, predicate, 1) {
                    1
                } else {
                    continue;
                };

                // Check if already known (#2815: O(1) per frame via hash lookup)
                let already_known = self
                    .frames
                    .iter()
                    .any(|frame| frame.contains_lemma(predicate, eq));

                if !already_known {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: Spurious CEX - learned affine equality {} for pred {} at level {}",
                            eq,
                            predicate.index(),
                            level
                        );
                    }
                    // #2459: Discovery context — use add_lemma_to_frame for
                    // cross-predicate propagation without restart accounting.
                    self.add_lemma_to_frame(Lemma::new(predicate, eq.clone(), level), level);
                    learned_any = true;
                }
            }

            for bound in result
                .bounds
                .iter()
                .filter(|bound| Self::prefers_convex_lower_bound(bound))
                .chain(
                    result
                        .bounds
                        .iter()
                        .filter(|bound| !Self::prefers_convex_lower_bound(bound)),
                )
                .take(MAX_BOUNDS_TO_CHECK)
            {
                if !self.is_chc_expr_preserved_by_transitions(predicate, bound, &canonical_vars) {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: Spurious CEX bound {} failed clause-local preservation",
                            bound
                        );
                    }
                    continue;
                }

                let level = if self.is_lemma_inductive(bound, predicate, 0) {
                    0
                } else if self.is_lemma_inductive(bound, predicate, 1) {
                    1
                } else {
                    continue;
                };

                let already_known = self
                    .frames
                    .iter()
                    .any(|frame| frame.contains_lemma(predicate, bound));

                if !already_known {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: Spurious CEX - learned bound lemma {} for pred {} at level {}",
                            bound,
                            predicate.index(),
                            level
                        );
                    }
                    self.add_lemma_to_frame(Lemma::new(predicate, bound.clone(), level), level);
                    learned_any = true;
                }
            }

            // Check divisibility constraints for inductiveness and add as lemmas.
            for div in result.divisibility.iter().take(MAX_DIVISIBILITY_TO_CHECK) {
                // Pre-filter: quick clause-local preservation check
                if !self.is_chc_expr_preserved_by_transitions(predicate, div, &canonical_vars) {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: Spurious CEX divisibility {} failed clause-local preservation",
                            div
                        );
                    }
                    continue;
                }

                // Try inductiveness at level 0 first (strongest), then level 1
                let level = if self.is_lemma_inductive(div, predicate, 0) {
                    0
                } else if self.is_lemma_inductive(div, predicate, 1) {
                    1
                } else {
                    continue;
                };

                // Check if already known (#2815: O(1) per frame via hash lookup)
                let already_known = self
                    .frames
                    .iter()
                    .any(|frame| frame.contains_lemma(predicate, div));

                if !already_known {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: Spurious CEX - learned divisibility lemma {} for pred {} at level {}",
                            div,
                            predicate.index(),
                            level
                        );
                    }
                    // #2459: Discovery context — use add_lemma_to_frame for
                    // cross-predicate propagation without restart accounting.
                    self.add_lemma_to_frame(Lemma::new(predicate, div.clone(), level), level);
                    learned_any = true;
                }
            }
        }

        learned_any
    }

    fn prefers_convex_lower_bound(expr: &ChcExpr) -> bool {
        match expr {
            ChcExpr::Op(ChcOp::Ge, args) if args.len() == 2 => true,
            ChcExpr::Op(ChcOp::BvULe | ChcOp::BvSLe, args) if args.len() == 2 => {
                !matches!(args[0].as_ref(), ChcExpr::Var(_))
                    && matches!(args[1].as_ref(), ChcExpr::Var(_))
            }
            _ => false,
        }
    }
}
