// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::super::super::PdrSolver;
use super::super::model_key;
use super::{int_presence_tautology, with_blocking_clauses, with_int_presence_tautologies};
use crate::pdr::cube;
use crate::smt::{SmtResult, SmtValue};
use crate::{ChcExpr, ChcSort, ChcVar, HornClause, PredicateId};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};

impl PdrSolver {
    /// Simulate forward N steps from a set of init samples.
    ///
    /// For self-loop clauses `P(body_args) && constraint => P(head_args)`, this:
    /// 1. Starts with `init_samples` (from facts)
    /// 2. For each init sample, applies the self-loop transition repeatedly
    /// 3. Collects intermediate states as additional diverse samples
    ///
    /// Returns the forward-reached states only (does not include `init_samples` themselves).
    ///
    /// Reference: the development design notes (#2042)
    pub(in crate::pdr::solver) fn simulate_forward_samples_from_init_samples(
        &mut self,
        predicate: PredicateId,
        init_samples: &[FxHashMap<String, i128>],
        n_steps: usize,
    ) -> Vec<FxHashMap<String, i128>> {
        const MAX_SAMPLES: usize = 20;

        if init_samples.is_empty() {
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: forward_sim pred {}: no init_samples provided",
                    predicate.0
                );
            }
            return Vec::new();
        }

        let canonical_vars = match self.canonical_vars(predicate) {
            Some(v) => v.to_vec(),
            None => {
                if self.config.verbose {
                    safe_eprintln!("PDR: forward_sim pred {}: no canonical_vars", predicate.0);
                }
                return Vec::new();
            }
        };

        let int_vars: Vec<ChcVar> = canonical_vars
            .iter()
            .filter(|v| matches!(v.sort, ChcSort::Int))
            .cloned()
            .collect();
        if int_vars.is_empty() {
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: forward_sim pred {}: no int vars in canonical_vars",
                    predicate.0
                );
            }
            return Vec::new();
        }

        // Find self-loop clauses for this predicate (clone to avoid borrowing self.problem).
        let self_loops: Vec<HornClause> = self
            .problem
            .clauses_defining(predicate)
            .filter(|c| {
                crate::lemma_hints::RecurrenceConservedEqualityProvider::is_self_loop(c)
                    .is_some_and(|(pid, _, _)| pid == predicate)
            })
            .cloned()
            .collect();
        if self_loops.is_empty() {
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: forward_sim pred {}: no self-loop clauses found",
                    predicate.0
                );
            }
            return Vec::new();
        }

        if self.config.verbose {
            safe_eprintln!(
                "PDR: forward_sim pred {}: {} init samples, {} self-loops, {} steps",
                predicate.0,
                init_samples.len(),
                self_loops.len(),
                n_steps
            );
        }

        let mut out: Vec<FxHashMap<String, i128>> = Vec::new();
        let mut seen_keys: FxHashSet<String> = FxHashSet::default();
        for init in init_samples {
            seen_keys.insert(model_key(init));
        }

        for (init_idx, init) in init_samples.iter().enumerate() {
            let mut current = init.clone();
            let mut step_count = 0usize;

            for step in 0..n_steps {
                if out.len() >= MAX_SAMPLES {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: forward_sim pred {}: reached max samples {}",
                            predicate.0,
                            MAX_SAMPLES
                        );
                    }
                    return out;
                }

                // Try ALL self-loop clauses to get branch diversity (#7138).
                // Collect results from each applicable branch, add all as samples,
                // but follow only one (round-robin) for the sequential chain.
                let mut branch_results: Vec<FxHashMap<String, i128>> = Vec::new();
                for self_loop in &self_loops {
                    if let Some(next) = self.apply_self_loop_transition(
                        self_loop,
                        &current,
                        &canonical_vars,
                        &int_vars,
                    ) {
                        branch_results.push(next);
                    }
                }
                if branch_results.is_empty() {
                    if self.config.verbose && step == 0 {
                        safe_eprintln!(
                            "PDR: forward_sim pred {}: no transition from init {} {:?}",
                            predicate.0,
                            init_idx,
                            current
                        );
                    }
                    break;
                }

                // Add all branch results as samples (for diversity)
                let mut any_new = false;
                for br in &branch_results {
                    let key = model_key(br);
                    if seen_keys.insert(key) {
                        out.push(br.clone());
                        step_count += 1;
                        any_new = true;
                    }
                }
                if !any_new {
                    break;
                }

                // Follow one branch for the sequential chain (round-robin by step)
                current = branch_results[step % branch_results.len()].clone();
            }

            if self.config.verbose && step_count > 0 {
                safe_eprintln!(
                    "PDR: forward_sim pred {}: init {} produced {} samples",
                    predicate.0,
                    init_idx,
                    step_count
                );
            }
        }

        if self.config.verbose {
            safe_eprintln!(
                "PDR: forward_sim pred {}: total {} forward samples",
                predicate.0,
                out.len()
            );
        }

        out
    }

    /// Apply a single self-loop transition to a concrete state.
    ///
    /// Given `P(body_args) && constraint => P(head_args)` and a model for body_args,
    /// queries SMT to find valid head_args values.
    pub(in crate::pdr::solver) fn apply_self_loop_transition(
        &mut self,
        clause: &HornClause,
        current: &FxHashMap<String, i128>,
        canonical_vars: &[ChcVar],
        int_vars: &[ChcVar],
    ) -> Option<FxHashMap<String, i128>> {
        // Extract body and head args from self-loop
        let (body_args, head_args) = match (&clause.body.predicates.first(), &clause.head) {
            (Some((_, b_args)), crate::ClauseHead::Predicate(_, h_args)) => (b_args, h_args),
            _ => return None,
        };

        if body_args.len() != canonical_vars.len() || head_args.len() != canonical_vars.len() {
            return None;
        }

        // Build substitution: body arg vars -> concrete values from current state
        let mut body_subst: Vec<(ChcVar, ChcExpr)> = Vec::new();
        for (i, arg) in body_args.iter().enumerate() {
            if let ChcExpr::Var(v) = arg {
                let canonical_var = &canonical_vars[i];
                if let Some(&value) = current.get(&canonical_var.name) {
                    body_subst.push((v.clone(), ChcExpr::Int(value)));
                }
            }
        }

        // Apply substitution to constraint
        let constraint = clause
            .body
            .constraint
            .clone()
            .unwrap_or(ChcExpr::Bool(true));
        let mut subst_constraint = constraint;
        for (old_var, new_expr) in &body_subst {
            subst_constraint = subst_constraint.substitute(&[(old_var.clone(), new_expr.clone())]);
        }

        // Prepare substituted head args and build query
        let mut head_var_info: Vec<(String, String, ChcExpr)> = Vec::new();
        for (i, arg) in head_args.iter().enumerate() {
            let canonical_var = &canonical_vars[i];
            if !matches!(canonical_var.sort, ChcSort::Int) {
                continue;
            }
            let mut subst_arg = arg.clone();
            for (old_var, new_expr) in &body_subst {
                subst_arg = subst_arg.substitute(&[(old_var.clone(), new_expr.clone())]);
            }
            let next_var_name = format!("{}_next", canonical_var.name);
            head_var_info.push((canonical_var.name.clone(), next_var_name, subst_arg));
        }

        // Fast path: try algebraic evaluation of head args without SMT.
        // When the constraint uniquely determines clause-local variables (or head args
        // reduce to constants after substitution), we can compute the next state directly.
        // This avoids SMT model incompleteness when the solver eliminates variables.
        if let Some(result) =
            Self::try_algebraic_forward_eval(&subst_constraint, &head_var_info, int_vars)
        {
            return Some(result);
        }

        // Slow path: use SMT solver
        let mut query_conjuncts = vec![subst_constraint];
        for (_, next_var_name, subst_arg) in &head_var_info {
            let next_var = ChcVar::new(next_var_name.clone(), ChcSort::Int);
            query_conjuncts.push(ChcExpr::eq(
                ChcExpr::var(next_var.clone()),
                subst_arg.clone(),
            ));
        }
        for (_, next_var_name, _) in &head_var_info {
            let v = ChcVar::new(next_var_name.clone(), ChcSort::Int);
            query_conjuncts.push(int_presence_tautology(v));
        }
        let query_conjuncts_ref = query_conjuncts.clone();
        let query = ChcExpr::and_all(query_conjuncts);

        // Query SMT solver
        self.smt.reset();
        let smt_result = self
            .smt
            .check_sat_with_timeout(&query, std::time::Duration::from_millis(100));
        match smt_result {
            SmtResult::Sat(model) => {
                let mut result: FxHashMap<String, i128> = FxHashMap::default();

                if self.config.verbose && result.is_empty() {
                    let model_keys: Vec<_> = model.keys().collect();
                    let expected: Vec<_> =
                        head_var_info.iter().map(|(_, n, _)| n.as_str()).collect();
                    safe_eprintln!(
                        "PDR: forward_sim SAT model keys={:?}, expected={:?}",
                        model_keys,
                        expected
                    );
                }

                // Extract values from model.
                // Some SMT solvers eliminate variables by constant propagation, so we have
                // multiple fallback strategies to recover the values.
                for (canonical_name, next_var_name, head_arg_expr) in &head_var_info {
                    // Strategy 1: Direct lookup in model
                    if let Some(SmtValue::Int(v)) = model.get(next_var_name) {
                        result.insert(canonical_name.clone(), *v);
                        continue;
                    }

                    // Strategy 2: Evaluate substituted head_arg expression using model values
                    if let Some(SmtValue::Int(v)) =
                        self.try_eval_head_arg_in_model(&model, head_arg_expr)
                    {
                        result.insert(canonical_name.clone(), v);
                        continue;
                    }

                    // Strategy 3: Augment model using equality definitions from query conjuncts.
                    // When the SMT solver eliminates clause-local variables via constant propagation,
                    // we can resolve them by walking equalities in the query. For example, if the
                    // query contains (= D 1) and head_arg = D, we can evaluate D = 1.
                    // This is safe because equalities in a satisfiable query hold in every model.
                    // See #2175 for why the old Strategy 3 (first-available _next) was unsound.
                    let mut augmented_model = model.clone();
                    let resolved = Self::augment_model_from_equalities(
                        &mut augmented_model,
                        &query_conjuncts_ref,
                    );
                    if resolved {
                        // Try Strategy 1 again with augmented model
                        if let Some(SmtValue::Int(v)) = augmented_model.get(next_var_name) {
                            result.insert(canonical_name.clone(), *v);
                            continue;
                        }
                        // Try Strategy 2 again with augmented model
                        if let Some(SmtValue::Int(v)) =
                            Self::try_eval_head_arg_in_model_static(&augmented_model, head_arg_expr)
                        {
                            result.insert(canonical_name.clone(), v);
                            continue;
                        }
                    }

                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: forward_sim failed to extract {} from model {:?}",
                            canonical_name,
                            model
                        );
                    }
                    // Failed to get complete assignment
                    return None;
                }

                // Verify we have all int vars
                if result.len() == int_vars.len() {
                    Some(result)
                } else {
                    None
                }
            }
            other => {
                // SMT query failed - add verbose logging to help debug
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: forward_sim SMT failed ({:?}) for query: {}",
                        other,
                        query
                    );
                }
                None
            }
        }
    }

    /// Sample diverse models from must-summary constraints at a given level.
    ///
    /// Unlike `sample_init_models` (fact constraints at level 0), this samples from
    /// `must_summaries` which represent concretely reachable states discovered during PDR.
    ///
    /// Returns a vector of models, each mapping canonical variable names to i128 values.
    pub(in crate::pdr::solver) fn sample_reachable_models(
        &mut self,
        predicate: PredicateId,
        level: usize,
        n: usize,
    ) -> Vec<FxHashMap<String, i128>> {
        let canonical_vars = match self.canonical_vars(predicate) {
            Some(v) => v.to_vec(),
            None => return Vec::new(),
        };

        let int_vars: Vec<ChcVar> = canonical_vars
            .iter()
            .filter(|v| matches!(v.sort, ChcSort::Int))
            .cloned()
            .collect();
        if int_vars.is_empty() {
            return Vec::new();
        }

        let Some(formulas) = self
            .reachability
            .must_summaries
            .get_formulas(level, predicate)
        else {
            return Vec::new();
        };
        if formulas.is_empty() {
            return Vec::new();
        }

        let mut models = Vec::with_capacity(n);
        let mut seen_keys: FxHashSet<String> = FxHashSet::default();

        for base_constraint in &formulas {
            if models.len() >= n {
                break;
            }
            if matches!(base_constraint, ChcExpr::Bool(false)) {
                continue;
            }

            // Common case: forward must-summary propagation produces a concrete point cube, so
            // we can avoid SMT by extracting a complete assignment directly from equalities.
            let mut extracted: FxHashMap<String, SmtValue> = FxHashMap::default();
            cube::extract_equalities_from_formula(base_constraint, &mut extracted);
            let mut values: FxHashMap<String, i128> = FxHashMap::default();
            for var in &int_vars {
                if let Some(SmtValue::Int(v)) = extracted.get(&var.name) {
                    values.insert(var.name.clone(), *v);
                }
            }
            if values.len() == int_vars.len() {
                let key = model_key(&values);
                if seen_keys.insert(key) {
                    models.push(values);
                }
                continue;
            }

            // Blocking-based diversity within a single reachable region.
            let mut blocking_clauses: Vec<ChcExpr> = Vec::new();
            let base_with_ints = with_int_presence_tautologies(base_constraint.clone(), &int_vars);
            while models.len() < n {
                let query = with_blocking_clauses(base_with_ints.clone(), &blocking_clauses);

                self.smt.reset();
                match self
                    .smt
                    .check_sat_with_timeout(&query, std::time::Duration::from_millis(100))
                {
                    SmtResult::Sat(model) => {
                        let mut values: FxHashMap<String, i128> = FxHashMap::default();
                        let mut all_values = true;
                        for var in &int_vars {
                            if let Some(SmtValue::Int(v)) = model.get(&var.name) {
                                values.insert(var.name.clone(), *v);
                            } else {
                                all_values = false;
                                break;
                            }
                        }
                        if !all_values {
                            break;
                        }

                        // Global dedup across all reachable regions at this level.
                        let key = model_key(&values);
                        if seen_keys.insert(key) {
                            models.push(values.clone());
                        }

                        // Build blocking clause: NOT(all vars equal this model)
                        let mut diseqs: Vec<ChcExpr> = Vec::new();
                        for var in &int_vars {
                            let Some(value) = values.get(&var.name) else {
                                continue;
                            };
                            diseqs
                                .push(ChcExpr::ne(ChcExpr::var(var.clone()), ChcExpr::Int(*value)));
                        }
                        if !diseqs.is_empty() {
                            let blocking = diseqs
                                .into_iter()
                                .reduce(ChcExpr::or)
                                .unwrap_or(ChcExpr::Bool(true));
                            blocking_clauses.push(blocking);
                        } else {
                            break;
                        }
                    }
                    _ => break, // No more models or timeout
                }
            }
        }

        models
    }
}
