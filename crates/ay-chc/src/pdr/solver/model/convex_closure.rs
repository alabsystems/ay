// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Convex closure generalization and affine invariant discovery from blocked states.

use super::super::{
    ChcExpr, ChcOp, ChcVar, Counterexample, FxHashMap, FxHashSet, Lemma, PdrSolver, PredicateId,
};

mod lemma_discovery;

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

        self.convex_generalization_lemmas(predicate, level, &numeric_vars, &seen_points, &result)
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
            if self.try_affine_discovery_for_predicate(predicate, &step_values) {
                learned_any = true;
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
