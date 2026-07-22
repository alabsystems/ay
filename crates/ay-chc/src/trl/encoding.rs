// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! TRL incremental SMT encoding and fresh-fallback reset helpers.
//!
//! Extracted from `trl/mod.rs` as part of #4701 wave 2.

use super::*;

impl TrlSolver {
    // ---- Incremental encoding ----

    /// Extend the incremental SAT context to cover transitions up to `depth`.
    ///
    /// Adds step formulas, blocking clauses, and transitivity constraints for
    /// each new depth from `encoded_depth+1` to `depth`. Previously encoded
    /// depths are not re-encoded (monotonic growth, Option A from design).
    pub(super) fn extend_encoding(&mut self, depth: usize) {
        for d in (self.encoded_depth + 1)..=depth {
            // Transition step (d-1) → d
            let step = self.build_step_formula(d - 1);
            self.inc_smt.assert_permanent(&step, &mut self.smt_helper);

            // Blocking clauses for this depth
            let blocking = self.get_blocking_clauses(d);
            for clause in blocking {
                self.inc_smt.assert_permanent(&clause, &mut self.smt_helper);
            }

            // Transitivity constraint: learned relations can't repeat consecutively
            if d >= 2 {
                let constraint = self.build_transitivity_constraint(d);
                self.inc_smt
                    .assert_permanent(&constraint, &mut self.smt_helper);
            }
        }
        if depth > self.encoded_depth {
            self.encoded_depth = depth;
        }
    }

    /// Build a transitivity constraint for depth `d`.
    ///
    /// `trace_id@(d-1) = 0 OR trace_id@(d-1) != trace_id@(d-2)`
    pub(super) fn build_transitivity_constraint(&self, d: usize) -> ChcExpr {
        let trace_var = ChcVar::new("trace_id", ChcSort::Int);
        let trace_d_minus_1 = TransitionSystem::version_var(&trace_var, d - 1);
        let trace_d_minus_2 = TransitionSystem::version_var(&trace_var, d - 2);
        let orig_ok = ChcExpr::eq(ChcExpr::var(trace_d_minus_1.clone()), ChcExpr::int(0));
        let different = ChcExpr::ne(ChcExpr::var(trace_d_minus_1), ChcExpr::var(trace_d_minus_2));
        ChcExpr::or(orig_ok, different)
    }

    /// Reset the incremental SAT solver when learned relations change.
    ///
    /// Creates a fresh `IncrementalQueryContext` with init@0 as background.
    /// The `SmtContext` (term cache) is preserved for faster re-encoding.
    pub(super) fn reset_incremental_solver(&mut self) {
        let mut inc_smt = IncrementalQueryContext::new();
        let init_at_0 = TransitionSystem::version_expr(&self.ts.init, &self.ts.vars, 0);
        inc_smt.assert_background(&init_at_0, &mut self.smt_helper);
        inc_smt.finalize_background(&self.smt_helper);
        self.inc_smt = inc_smt;
        self.encoded_depth = 0;
    }

    /// Build a model-blocking clause that forces a different state at `depth`.
    ///
    /// Returns a disjunction: at least one state variable must differ from the
    /// model value. Analogous to Golem's `neg(project(relation, model))`.
    pub(super) fn build_model_blocking_clause(
        &self,
        depth: usize,
        model: &FxHashMap<String, SmtValue>,
    ) -> ChcExpr {
        let mut negated_eqs = Vec::new();
        for v in &self.ts.vars {
            if let Some(SmtValue::Int(val)) = model.get(&v.name) {
                let versioned = TransitionSystem::version_var(v, depth);
                negated_eqs.push(ChcExpr::ne(ChcExpr::var(versioned), ChcExpr::int(*val)));
            }
        }
        if negated_eqs.is_empty() {
            ChcExpr::Bool(true)
        } else {
            ChcExpr::or_all(negated_eqs)
        }
    }

    /// Check if the error state is reachable at this depth using the incremental solver.
    ///
    /// Extends the encoding to cover `depth`, then checks with query@depth as assumption.
    /// Returns the incremental result so callers can distinguish Unsat from Unknown (#2659).
    ///
    /// #7165: When the incremental check returns Unknown (e.g., mod/div or disequality-heavy
    /// queries), retry with a fresh non-incremental formula via executor fallback. The full
    /// ay-dpll executor handles these via theory propagation + CEGQI.
    pub(super) fn check_error_reachable(&mut self, depth: usize) -> IncrementalCheckResult {
        self.extend_encoding(depth);
        let query_at_depth = self.version_expr(&self.ts.query, depth);
        let result = self.inc_smt.check_sat_incremental(
            &[query_at_depth.clone()],
            &mut self.smt_helper,
            Some(TRL_PER_CHECK_TIMEOUT),
        );

        if matches!(result, IncrementalCheckResult::Unknown) {
            // Build fresh BMC formula: init@0 AND steps AND query@depth
            let fresh = self.build_error_reachability_formula(depth, &query_at_depth);
            self.smt_helper.reset();
            // #7398: Reset incremental solver after TermStore reset to prevent
            // stale TermIds from crashing BvSolver::bitblast_predicate.
            self.reset_incremental_solver();
            let fresh_result = self
                .smt_helper
                .check_sat_with_executor_fallback_timeout(&fresh, TRL_PER_CHECK_TIMEOUT);
            match fresh_result {
                SmtResult::Sat(model) => {
                    return IncrementalCheckResult::Sat(model);
                }
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                    return IncrementalCheckResult::Unsat;
                }
                SmtResult::Unknown => {} // fall through to original Unknown
            }
        }

        result
    }

    /// Build a fresh non-incremental BMC formula for error reachability at `depth`.
    ///
    /// Formula: init@0 AND step(0→1) AND ... AND step(d-1→d) AND blocking AND query@depth.
    pub(super) fn build_error_reachability_formula(
        &self,
        depth: usize,
        query_at_depth: &ChcExpr,
    ) -> ChcExpr {
        let mut conjuncts = vec![self.version_expr(&self.ts.init, 0)];
        for d in 1..=depth {
            conjuncts.push(self.build_step_formula(d - 1));
            for clause in self.get_blocking_clauses(d) {
                conjuncts.push(clause);
            }
            if d >= 2 {
                conjuncts.push(self.build_transitivity_constraint(d));
            }
        }
        conjuncts.push(query_at_depth.clone());
        ChcExpr::and_all(conjuncts)
    }

    // ---- BMC formula building ----

    /// Build transition disjunction for step d -> d+1.
    ///
    /// Each transition is tagged with trace_id = id.
    pub(super) fn build_step_formula(&self, d: usize) -> ChcExpr {
        let disjuncts: Vec<ChcExpr> = self
            .learned
            .iter()
            .enumerate()
            .map(|(id, trans)| {
                // trace_id@d = id
                let trace_var = ChcVar::new("trace_id", ChcSort::Int);
                let trace_var_at = TransitionSystem::version_var(&trace_var, d);
                let id_constraint =
                    ChcExpr::eq(ChcExpr::var(trace_var_at), ChcExpr::int(id as i64));

                // Versioned transition from d to d+1
                let versioned = self.version_transition(trans, d, d + 1);
                ChcExpr::and(id_constraint, versioned)
            })
            .collect();

        if disjuncts.len() == 1 {
            disjuncts.into_iter().next().expect("len == 1")
        } else {
            ChcExpr::or_all(disjuncts)
        }
    }

    /// Get blocking clauses for this depth.
    pub(super) fn get_blocking_clauses(&self, depth: usize) -> Vec<ChcExpr> {
        self.blocked
            .get(&depth)
            .map(|m| m.values().cloned().collect())
            .unwrap_or_default()
    }
}
