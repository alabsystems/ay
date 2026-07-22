// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::ChcSort;

/// Check if a conjunct is an equality between array-sorted expressions.
///
/// Array equalities like `(= arr (store ...))` pin the entire array to its
/// initial value, which is almost never inductive for transitions that modify
/// the array. Including them in conjunctive fact-clause invariants can lead
/// to false SAFE results (#8675) because the SMT self-inductiveness check
/// may return incorrect UNSAT for complex array formulas.
fn is_array_equality(conjunct: &ChcExpr) -> bool {
    if let ChcExpr::Op(ChcOp::Eq, args) = conjunct {
        if args.len() == 2 {
            return matches!(args[0].sort(), ChcSort::Array(_, _))
                || matches!(args[1].sort(), ChcSort::Array(_, _));
        }
    }
    false
}

/// Check if a conjunct is a select-based equality like `(= (select arr idx) val)`.
///
/// These appear as fact-clause conjuncts in array-heavy CHC encodings (the
/// model-checker-consumer pattern from #8660). The raw equality is usually not self-inductive
/// when the transition may store to `arr[idx]`, but the weakened one-sided
/// form (`>=` or `<=`) often is. We detect these to route them through the
/// weakening admission path.
fn is_select_based_equality(conjunct: &ChcExpr) -> bool {
    let ChcExpr::Op(ChcOp::Eq, args) = conjunct else {
        return false;
    };
    if args.len() != 2 {
        return false;
    }
    let is_select =
        |e: &ChcExpr| matches!(e, ChcExpr::Op(ChcOp::Select, inner) if inner.len() == 2);
    is_select(&args[0]) || is_select(&args[1])
}

impl PdrSolver {
    fn clear_budgeted_fact_admission_cache_entry(&mut self, pred: PredicateId, formula: &ChcExpr) {
        self.rejected_invariants.remove(&(pred, formula.clone()));

        let blocking = ChcExpr::not(formula.clone());
        let blocking_hash = blocking.structural_hash();

        let blocks_init_key = (pred, blocking_hash);
        if matches!(
            self.caches.blocks_init_cache.get(&blocks_init_key),
            Some((cached_expr, false)) if cached_expr == &blocking
        ) {
            self.caches.blocks_init_cache.remove(&blocks_init_key);
        }

        let self_inductive_key = (pred, blocking_hash);
        if matches!(
            self.caches.self_inductive_cache.get(&self_inductive_key),
            Some((cached_expr, _, false)) if cached_expr == &blocking
        ) {
            self.caches.self_inductive_cache.remove(&self_inductive_key);
        }
    }

    fn clear_budgeted_fact_admission_cache_entries(
        &mut self,
        pred: PredicateId,
        formula: &ChcExpr,
    ) {
        self.clear_budgeted_fact_admission_cache_entry(pred, formula);
        if let Some(weakened_forms) = Self::try_weaken_equality_to_inequality(formula) {
            for weakened in weakened_forms {
                self.clear_budgeted_fact_admission_cache_entry(pred, &weakened);
            }
        }
    }

    fn add_budgeted_fact_discovered_invariant(
        &mut self,
        pred: PredicateId,
        formula: ChcExpr,
        clear_timeout_rejections: bool,
    ) -> bool {
        let result = if is_select_based_equality(&formula) {
            self.add_discovered_invariant_with_weakening(pred, formula.clone(), 1)
        } else {
            self.add_discovered_invariant(pred, formula.clone(), 1)
        };

        if clear_timeout_rejections {
            self.clear_budgeted_fact_admission_cache_entries(pred, &formula);
        }

        result
    }

    pub(in crate::pdr::solver) fn build_conjunctive_fact_clause_lemma(
        &self,
        conjuncts: Vec<ChcExpr>,
    ) -> ChcExpr {
        if self.problem_is_pure_lia && !self.problem_is_bitvector_only {
            return ChcExpr::and_all(conjuncts);
        }

        // #7964: Preserve BV/native fact bundles as a single lemma. Bool-only
        // bit-blasted BV problems can also satisfy the broader pure-LIA gate,
        // but plain `And(...)` formulas are split into individual conjunct
        // lemmas by generic frame insertion, which defeats the "only inductive
        // together" startup case for `simple.c_000`.
        ChcExpr::not(ChcExpr::or_all(conjuncts.into_iter().map(ChcExpr::not)))
    }

    /// Try to promote inductive conjuncts from a predicate's fact constraint(s) to frame[1] lemmas.
    ///
    /// Motivation: Some benchmarks have strong init constraints that are also inductive, but PDR
    /// only uses them for level-0 must summaries. Without promoting them, PDR may repeatedly block
    /// unreachable states that violate those constraints.
    ///
    /// Safety: Only applies when the level-0 must-summary is a *single* constraint (not an OR of
    /// multiple fact clauses). Each conjunct is still checked for init-validity and (self-)inductiveness
    /// via `add_discovered_invariant`.
    pub(in crate::pdr::solver) fn discover_fact_clause_conjunct_invariants(&mut self) {
        const FACT_PASS_TIMEOUT: std::time::Duration = std::time::Duration::from_millis(750);
        const FACT_SMT_TIMEOUT: std::time::Duration = std::time::Duration::from_millis(200);

        let budgeted_non_lia = !self.problem_is_pure_lia
            && (self.config.solve_timeout.is_some() || self.config.cancellation_token.is_some());
        let fact_deadline = if budgeted_non_lia {
            Some(ay_core::time::Instant::now() + FACT_PASS_TIMEOUT)
        } else {
            None
        };
        let _fact_smt_timeout = if budgeted_non_lia {
            let now = ay_core::time::Instant::now();
            let timeout = match self.solve_deadline {
                Some(deadline) => {
                    let Some(remaining) = deadline.checked_duration_since(now) else {
                        return;
                    };
                    remaining.min(FACT_SMT_TIMEOUT)
                }
                None => FACT_SMT_TIMEOUT,
            };
            Some(self.smt.scoped_check_timeout(Some(timeout)))
        } else {
            None
        };

        // Collect predicate IDs first to avoid borrow conflict.
        let pred_ids: Vec<PredicateId> = self.problem.predicates().iter().map(|p| p.id).collect();

        for pred_id in pred_ids {
            if self.is_cancelled()
                || fact_deadline.is_some_and(|d| ay_core::time::Instant::now() >= d)
            {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: fact-clause conjunct discovery budget exhausted, stopping"
                    );
                }
                return;
            }

            if !self.predicate_has_facts(pred_id) {
                continue;
            }

            // Use backed-only must-summaries to avoid loop-closure heuristic seeds (#2247).
            // The backed init constraint is a single formula; unbacked loop-closure adds disjuncts.
            let Some(must_summary) = self.reachability.must_summaries.get_backed(0, pred_id) else {
                continue;
            };

            // If there are multiple fact clauses, must-summary is a disjunction; we cannot soundly
            // lift conjuncts from it without case-splitting.
            if matches!(must_summary, ChcExpr::Op(ChcOp::Or, _)) {
                continue;
            }

            let conjuncts = must_summary.collect_conjuncts();
            if conjuncts.len() < 2 {
                continue;
            }

            for conjunct in conjuncts {
                if self.is_cancelled()
                    || fact_deadline.is_some_and(|d| ay_core::time::Instant::now() >= d)
                {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: fact-clause conjunct discovery budget exhausted for pred {}",
                            pred_id.index()
                        );
                    }
                    return;
                }

                // Avoid obvious noise.
                if matches!(conjunct, ChcExpr::Bool(true)) {
                    continue;
                }
                // #6047: Skip non-Bool array conjuncts (e.g., bare const_array, store
                // expressions). Allow Bool-sorted conjuncts that reference arrays via
                // select (e.g., `(= (select arr idx) val)`) — these are valid scalar
                // invariants and the SMT converter now handles BV comparisons correctly.
                if conjunct.contains_array_ops() && !conjunct.is_bool_sorted_top_level() {
                    continue;
                }
                // #8675: Skip array equalities — see discover_conjunctive_fact_clause_invariants.
                if is_array_equality(&conjunct) {
                    continue;
                }
                // #8660: For select-based equalities like `(= (select arr 0) 42)`,
                // route through the weakening admission path. The raw equality
                // is rarely self-inductive when the transition stores into the
                // array, but the weakened `(>= (select arr 0) 42)` form often
                // is. Without this, the equality is deferred indefinitely and
                // the solver gives up with "unknown" on model-checker-consumer-style benchmarks
                // with >=2 Array-sorted params.
                let _ = self.add_budgeted_fact_discovered_invariant(
                    pred_id,
                    conjunct,
                    budgeted_non_lia,
                );
            }
        }
    }

    /// Try adding the conjunction of promotable fact-clause conjuncts as a single lemma.
    ///
    /// Some bit-blasted BV benchmarks need several Boolean init facts together:
    /// each literal is not self-inductive in isolation, but their conjunction is.
    /// `simple.c_000` in #5877 is the motivating case after BV-to-Bool preprocessing.
    pub(in crate::pdr::solver) fn discover_conjunctive_fact_clause_invariants(&mut self) {
        const MAX_CONJUNCTS: usize = 8;

        let pred_ids: Vec<PredicateId> = self.problem.predicates().iter().map(|p| p.id).collect();

        for pred_id in pred_ids {
            if !self.predicate_has_facts(pred_id) {
                continue;
            }

            // Avoid combining fact-derived conjuncts for predicates that can be entered
            // through unrestricted inter-predicate edges. Self-inductiveness alone is
            // not sufficient there, and the conjunction can be much stronger than any
            // single promoted conjunct.
            if self.has_unrestricted_incoming_inter_predicate_transitions(pred_id) {
                continue;
            }

            let Some(must_summary) = self.reachability.must_summaries.get_backed(0, pred_id) else {
                continue;
            };

            if matches!(must_summary, ChcExpr::Op(ChcOp::Or, _)) {
                continue;
            }

            let mut conjuncts = Vec::new();
            for conjunct in must_summary.collect_conjuncts() {
                if matches!(conjunct, ChcExpr::Bool(true)) {
                    continue;
                }
                if conjunct.contains_array_ops() && !conjunct.is_bool_sorted_top_level() {
                    continue;
                }
                // #8675: Skip array equalities (e.g., `(= arr (store ...))`).
                // These pin the entire array to its initial value, which is
                // almost never inductive for transitions that modify the array.
                // Including them causes false SAFE results because the SMT
                // self-inductiveness check may return incorrect UNSAT for
                // complex array formulas.
                if is_array_equality(&conjunct) {
                    continue;
                }
                if !conjuncts.contains(&conjunct) {
                    conjuncts.push(conjunct);
                }
            }

            if conjuncts.len() < 2 || conjuncts.len() > MAX_CONJUNCTS {
                continue;
            }

            let conjunction = self.build_conjunctive_fact_clause_lemma(conjuncts);
            if self.frames.len() > 1 && self.frames[1].contains_lemma(pred_id, &conjunction) {
                continue;
            }

            let _ = self.add_discovered_invariant(pred_id, conjunction, 1);
        }
    }

    /// Discover mutually-inductive lower bounds as a single conjunction.
    ///
    /// `discover_bound_invariants()` only adds bounds that are individually self-inductive. Some
    /// programs require *dependent* bounds, e.g.:
    /// - `b >= 0` depends on `c >= -1`
    /// - `c >= -1` depends on `d >= 0`
    ///
    /// In such cases, the conjunction is inductive even though each bound alone is not.
    ///
    /// Heuristic: For predicates with exact init values, try conjunctions of `var >= init-k`
    /// for small `k` (0..=2) and add the first inductive one (checked via `add_discovered_invariant`).
    pub(in crate::pdr::solver) fn discover_joint_init_shifted_lower_bounds(&mut self) {
        // Keep this cheap and targeted: only try on very small, exact-init predicates.
        const MAX_VARS: usize = 6;
        const MAX_SHIFT: i128 = 2;

        if self.config.verbose {
            safe_eprintln!("PDR: discover_joint_init_shifted_lower_bounds starting");
        }

        // Collect candidate predicates and their data first to avoid borrow conflict.
        // Note: capture verbose outside the closure because self is borrowed by predicates().
        let verbose = self.config.verbose;
        let candidates: Vec<(PredicateId, Vec<(ChcVar, i128)>)> = self
            .problem
            .predicates()
            .iter()
            .filter_map(|pred| {
                if !self.predicate_has_facts(pred.id) {
                    if verbose {
                        safe_eprintln!("PDR: joint bounds: pred {} has no facts", pred.id.index());
                    }
                    return None;
                }

                // Note: We intentionally do NOT skip if there are already lemmas at frame[1].
                // Other discovery passes (e.g., sum invariants) may add lemmas, but those don't
                // substitute for the joint lower bounds needed here. The `add_discovered_invariant`
                // call handles deduplication.

                let canonical_vars = match self.canonical_vars(pred.id) {
                    Some(v) => v.to_vec(),
                    None => {
                        if verbose {
                            safe_eprintln!(
                                "PDR: joint bounds: pred {} has no canonical vars",
                                pred.id.index()
                            );
                        }
                        return None;
                    }
                };
                let init_values = self.get_init_values(pred.id);

                let mut exact_init: Vec<(ChcVar, i128)> = Vec::new();
                for var in &canonical_vars {
                    if !matches!(var.sort, ChcSort::Int) {
                        continue;
                    }
                    let Some(bounds) = init_values.get(&var.name) else {
                        if verbose {
                            safe_eprintln!(
                                "PDR: joint bounds: pred {} var {} has no init bounds",
                                pred.id.index(),
                                var.name
                            );
                        }
                        continue;
                    };
                    if bounds.min == bounds.max {
                        exact_init.push((var.clone(), bounds.min));
                    } else if verbose {
                        safe_eprintln!(
                            "PDR: joint bounds: pred {} var {} init not exact: [{}, {}]",
                            pred.id.index(),
                            var.name,
                            bounds.min,
                            bounds.max
                        );
                    }
                }

                if exact_init.len() < 2 || exact_init.len() > MAX_VARS {
                    if verbose {
                        safe_eprintln!(
                            "PDR: joint bounds: pred {} has {} exact init vars (need 2..={})",
                            pred.id.index(),
                            exact_init.len(),
                            MAX_VARS
                        );
                    }
                    return None;
                }

                Some((pred.id, exact_init))
            })
            .collect();

        if self.config.verbose && !candidates.is_empty() {
            safe_eprintln!(
                "PDR: discover_joint_init_shifted_lower_bounds: {} candidates",
                candidates.len()
            );
        }

        for (pred_id, exact_init) in candidates {
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: trying joint bounds for pred {}: {} vars with exact init",
                    pred_id.index(),
                    exact_init.len()
                );
            }
            // Search by increasing total shift (0,1,2,...) to find the strongest model quickly.
            let max_total = (MAX_SHIFT as usize) * exact_init.len();
            for total_shift in 0..=max_total {
                let mut chosen: Vec<i128> = Vec::with_capacity(exact_init.len());
                if self.try_add_shifted_lower_bound_combo(
                    pred_id,
                    &exact_init,
                    total_shift,
                    &mut chosen,
                ) {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: joint bound succeeded for pred {} at total_shift={}",
                            pred_id.index(),
                            total_shift
                        );
                    }
                    break;
                }
            }
        }
    }

    pub(in crate::pdr::solver) fn try_add_shifted_lower_bound_combo(
        &mut self,
        pred: PredicateId,
        vars: &[(ChcVar, i128)],
        remaining_shift: usize,
        chosen_shifts: &mut Vec<i128>,
    ) -> bool {
        const MAX_SHIFT: i128 = 2;

        if chosen_shifts.len() == vars.len() {
            if remaining_shift != 0 {
                return false;
            }
            let mut conjuncts = Vec::with_capacity(vars.len());
            for ((var, init), shift) in vars.iter().zip(chosen_shifts.iter().copied()) {
                let bound = init.saturating_sub(shift);
                conjuncts.push(ChcExpr::ge(ChcExpr::var(var.clone()), ChcExpr::Int(bound)));
            }
            let candidate = ChcExpr::and_all(conjuncts);
            return self.add_discovered_invariant(pred, candidate, 1);
        }

        let remaining_vars = vars.len() - chosen_shifts.len();
        // Prune: even if we use MAX_SHIFT for all remaining vars, can we spend remaining_shift?
        let max_possible = remaining_vars * (MAX_SHIFT as usize);
        if remaining_shift > max_possible {
            return false;
        }

        // Enumerate shifts for this variable, preferring smaller shifts (stronger bounds).
        for shift in 0..=MAX_SHIFT {
            let shift_usize = shift as usize;
            if shift_usize > remaining_shift {
                break;
            }
            chosen_shifts.push(shift);
            if self.try_add_shifted_lower_bound_combo(
                pred,
                vars,
                remaining_shift - shift_usize,
                chosen_shifts,
            ) {
                return true;
            }
            chosen_shifts.pop();
        }

        false
    }

    /// Extract an upper bound for a variable from a constraint expression.
    /// Returns Some(bound) if the constraint implies var <= bound or var < bound+1.
    pub(in crate::pdr::solver) fn extract_upper_bound_for_var(
        constraint: &ChcExpr,
        var_name: &str,
    ) -> Option<i128> {
        match constraint {
            ChcExpr::Op(ChcOp::And, args) => {
                // Try each conjunct
                for arg in args {
                    if let Some(bound) = Self::extract_upper_bound_for_var(arg, var_name) {
                        return Some(bound);
                    }
                }
                None
            }
            // (not (<= K var)) -> var < K -> var <= K-1
            ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => {
                if let ChcExpr::Op(ChcOp::Le, inner) = args[0].as_ref() {
                    if inner.len() == 2 {
                        if let (ChcExpr::Int(k), ChcExpr::Var(v)) =
                            (inner[0].as_ref(), inner[1].as_ref())
                        {
                            if v.name == var_name {
                                return Some(*k - 1);
                            }
                        }
                    }
                }
                // (not (>= var K)) -> var < K -> var <= K-1
                if let ChcExpr::Op(ChcOp::Ge, inner) = args[0].as_ref() {
                    if inner.len() == 2 {
                        if let (ChcExpr::Var(v), ChcExpr::Int(k)) =
                            (inner[0].as_ref(), inner[1].as_ref())
                        {
                            if v.name == var_name {
                                return Some(*k - 1);
                            }
                        }
                    }
                }
                None
            }
            // (<= var K) -> var <= K
            ChcExpr::Op(ChcOp::Le, args) if args.len() == 2 => {
                if let (ChcExpr::Var(v), ChcExpr::Int(k)) = (args[0].as_ref(), args[1].as_ref()) {
                    if v.name == var_name {
                        return Some(*k);
                    }
                }
                None
            }
            // (< var K) -> var <= K-1
            ChcExpr::Op(ChcOp::Lt, args) if args.len() == 2 => {
                if let (ChcExpr::Var(v), ChcExpr::Int(k)) = (args[0].as_ref(), args[1].as_ref()) {
                    if v.name == var_name {
                        return Some(*k - 1);
                    }
                }
                None
            }
            _ => None,
        }
    }

    /// Check if a variable at a given index is preserved (unchanged) in all self-loop transitions.
    pub(in crate::pdr::solver) fn is_var_preserved_in_self_loop(
        &self,
        predicate: PredicateId,
        var_idx: usize,
    ) -> bool {
        let canonical_vars = match self.canonical_vars(predicate) {
            Some(v) => v,
            None => return false,
        };

        if var_idx >= canonical_vars.len() {
            return false;
        }

        // Track whether we checked at least one self-loop clause (#1388).
        let mut checked_any_self_loop = false;

        // Check all transition clauses
        for clause in self.problem.clauses_defining(predicate) {
            // Skip fact clauses
            if clause.body.predicates.is_empty() {
                continue;
            }

            // Only check self-loops
            if clause.body.predicates.len() != 1 {
                continue;
            }
            let (body_pred, body_args) = &clause.body.predicates[0];
            if *body_pred != predicate {
                // Inter-predicate transition: skip, only check self-loops for preservation.
                // If zero self-loops exist, we'll return false at the end (#1388).
                continue;
            }

            let head_args = match &clause.head {
                crate::ClauseHead::Predicate(_, a) => a.as_slice(),
                crate::ClauseHead::False => continue,
            };

            if head_args.len() != canonical_vars.len() || body_args.len() != canonical_vars.len() {
                return false;
            }

            // This is a self-loop clause - mark that we're checking at least one
            checked_any_self_loop = true;

            // Get the body and head expressions for this variable
            let body_expr = &body_args[var_idx];
            let head_expr = &head_args[var_idx];

            // Check if head == body (variable preserved)
            if let (ChcExpr::Var(body_var), ChcExpr::Var(head_var)) = (body_expr, head_expr) {
                if body_var.name == head_var.name {
                    continue; // Preserved in this self-loop
                }
            }

            // Also check if there's a constraint that establishes equality
            // (e.g., constraint contains (= head_var body_var))
            // For now, conservatively return false if not directly equal
            return false;
        }

        // If zero self-loops were checked, cannot claim preservation vacuously (#1388).
        if !checked_any_self_loop {
            return false;
        }
        true // Preserved in all self-loops
    }
}
