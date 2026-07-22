// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Counterexample construction, fixed-point checks, and model extraction.

mod convex_closure;
mod counterexample;
mod fixed_point;
mod point_blocking;
mod push_lemmas;
#[cfg(test)]
mod tests;

use super::{
    ChcExpr, ChcOp, ChcSort, ChcVar, Frame, FxHashMap, FxHashSet, InvariantModel, PdrSolver,
    PredicateId, SmtResult, SmtValue,
};

// Bounded storage for convex-closure blocked-state history (#2819).
pub(super) const MAX_BLOCKED_STATES_PER_PREDICATE: usize = 100;
pub(super) const MAX_BLOCKED_STATE_PREDICATES: usize = 256;

/// Result of [`PdrSolver::simplify_model`] indicating what modifications were made.
///
/// Callers use this to decide re-verification strategy:
/// - `redundancy_removed`: conjuncts were subsumed. The pre-simplification model was
///   valid, so if the simplified model fails re-verification, fall back to the original.
/// - `free_vars_sanitized`: conjuncts had undeclared variables. The pre-simplification
///   model may be fundamentally invalid (#5805), so callers should NOT fall back.
#[derive(Debug, Clone, Copy)]
pub(in crate::pdr::solver) struct SimplifyResult {
    /// True if redundant conjuncts were eliminated by subsumption checks.
    pub(in crate::pdr::solver) redundancy_removed: bool,
    /// True if conjuncts were stripped due to undeclared variables.
    pub(in crate::pdr::solver) free_vars_sanitized: bool,
}

impl SimplifyResult {
    /// Returns true if the model was modified in any way.
    pub(in crate::pdr::solver) fn modified(&self) -> bool {
        self.redundancy_removed || self.free_vars_sanitized
    }
}

impl PdrSolver {
    /// Add a new frame
    pub(in crate::pdr::solver) fn push_frame(&mut self) {
        let new_frame = Frame::new();
        self.frames.push(new_frame);
        self.tracing.active_pob = None;
        self.tracing.query_level = Some(self.frames.len() - 1);
        // #5970: Clear deferred entry-inductive invariants on level advance.
        // Invariants discovered at level N may not be relevant at level N+1.
        self.deferred_entry_invariants.clear();
        self.deferred_self_inductive_invariants.clear();
        // #7006: Clear rejected-invariant cache on level advance. Frame
        // strengthening may make previously-rejected invariants pass now.
        self.rejected_invariants.clear();
        self.pdr_trace_step("Running", Some("ExpandLevel"), None);
        tracing::info!(
            action = "ExpandLevel",
            frames = self.frames.len(),
            level = self.frames.len() - 1,
            "PDR expanded to new level"
        );
    }

    // ============================================================================
    // Convex Closure Integration (Z3 Spacer technique for multi-lemma generalization)
    // ============================================================================

    /// Record a blocked state for convex closure analysis.
    /// Called when we successfully block a state with a lemma.
    /// Extracts numeric values from the state and stores them for later analysis.
    pub(in crate::pdr::solver) fn record_blocked_state_for_convex(
        &mut self,
        predicate: PredicateId,
        state: &ChcExpr,
    ) {
        if !self.config.use_convex_closure {
            return;
        }

        // Extract numeric variable assignments from the state formula
        let values = self.extract_numeric_values_from_state(state);
        if values.is_empty() {
            return;
        }

        if self.caches.blocked_states_for_convex.len() >= MAX_BLOCKED_STATE_PREDICATES
            && !self
                .caches
                .blocked_states_for_convex
                .contains_key(&predicate)
        {
            self.caches.blocked_states_for_convex.clear();
        }

        // Store for convex closure analysis
        let entries = self
            .caches
            .blocked_states_for_convex
            .entry(predicate)
            .or_default();
        entries.push_back(values);

        // Limit storage to prevent memory bloat
        if entries.len() > MAX_BLOCKED_STATES_PER_PREDICATE {
            entries.pop_front();
        }
    }

    /// Extract numeric variable values from a state formula.
    /// Parses equalities like (= x 5) and (= y (- 3)) to get {x: 5, y: -3}.
    pub(in crate::pdr::solver) fn extract_numeric_values_from_state(
        &self,
        state: &ChcExpr,
    ) -> FxHashMap<String, i64> {
        // i128-lockstep: this feeds the i64-based convex-closure pipeline;
        // values outside i64 range are skipped (fewer data points, and CC
        // candidates are verified before adoption).
        let mut values = FxHashMap::default();
        let conjuncts = state.collect_conjuncts();

        for conjunct in conjuncts {
            // Look for (= var value) patterns
            if let ChcExpr::Op(ChcOp::Eq, args) = &conjunct {
                if args.len() == 2 {
                    // Try both orderings: (= var val) and (= val var)
                    if let (ChcExpr::Var(v), Some(Ok(val))) = (
                        args[0].as_ref(),
                        Self::get_constant(args[1].as_ref()).map(i64::try_from),
                    ) {
                        values.insert(v.name.clone(), val);
                    } else if let (Some(Ok(val)), ChcExpr::Var(v)) = (
                        Self::get_constant(args[0].as_ref()).map(i64::try_from),
                        args[1].as_ref(),
                    ) {
                        values.insert(v.name.clone(), val);
                    }
                }
            }
        }

        values
    }

    /// Extract concrete variable assignments from a state formula.
    ///
    /// Handles:
    /// - Int equalities like (= x 5), (= 5 x)
    /// - Bool literals like x, (not x), (= x true), (= false x)
    pub(in crate::pdr::solver) fn extract_point_values_from_state(
        &self,
        state: &ChcExpr,
    ) -> FxHashMap<String, SmtValue> {
        let mut values = FxHashMap::default();
        let conjuncts = state.collect_conjuncts();

        for conjunct in conjuncts {
            match &conjunct {
                // Look for (= var value) patterns
                ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
                    // Try both orderings: (= var val) and (= val var)
                    if let (ChcExpr::Var(v), Some(val)) =
                        (args[0].as_ref(), Self::get_constant(args[1].as_ref()))
                    {
                        values.insert(v.name.clone(), Self::smt_value_for_var_constant(v, val));
                    } else if let (Some(val), ChcExpr::Var(v)) =
                        (Self::get_constant(args[0].as_ref()), args[1].as_ref())
                    {
                        values.insert(v.name.clone(), Self::smt_value_for_var_constant(v, val));
                    } else if let (ChcExpr::Var(v), ChcExpr::Bool(b)) =
                        (args[0].as_ref(), args[1].as_ref())
                    {
                        values.insert(v.name.clone(), SmtValue::Bool(*b));
                    } else if let (ChcExpr::Bool(b), ChcExpr::Var(v)) =
                        (args[0].as_ref(), args[1].as_ref())
                    {
                        values.insert(v.name.clone(), SmtValue::Bool(*b));
                    }
                    // DT constructor equality: (= var (CtorName a1 a2))
                    else if let (ChcExpr::Var(v), ChcExpr::FuncApp(ctor, _, ctor_args)) =
                        (args[0].as_ref(), args[1].as_ref())
                    {
                        if matches!(v.sort, ChcSort::Datatype { .. }) {
                            if let Some(dt_val) = Self::funcapp_to_smt_value(ctor, ctor_args) {
                                values.insert(v.name.clone(), dt_val);
                            }
                        }
                    } else if let (ChcExpr::FuncApp(ctor, _, ctor_args), ChcExpr::Var(v)) =
                        (args[0].as_ref(), args[1].as_ref())
                    {
                        if matches!(v.sort, ChcSort::Datatype { .. }) {
                            if let Some(dt_val) = Self::funcapp_to_smt_value(ctor, ctor_args) {
                                values.insert(v.name.clone(), dt_val);
                            }
                        }
                    }
                }
                // Bool literal: x
                ChcExpr::Var(v) if matches!(v.sort, ChcSort::Bool) => {
                    values.insert(v.name.clone(), SmtValue::Bool(true));
                }
                // Bool literal: (not x)
                ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => {
                    if let ChcExpr::Var(v) = args[0].as_ref() {
                        if matches!(v.sort, ChcSort::Bool) {
                            values.insert(v.name.clone(), SmtValue::Bool(false));
                        }
                    }
                }
                _ => {}
            }
        }

        values
    }

    pub(in crate::pdr::solver) fn blocked_state_bv_seed_values(
        &self,
        predicate: PredicateId,
        canonical_vars: &[ChcVar],
        per_var_cap: usize,
    ) -> FxHashMap<String, Vec<i64>> {
        let entries = match self.caches.blocked_states_for_convex.get(&predicate) {
            Some(entries) => entries,
            None => return FxHashMap::default(),
        };

        let bv_vars: Vec<_> = canonical_vars
            .iter()
            .filter(|var| {
                matches!(var.sort, ChcSort::BitVec(_)) && Self::supports_i64_numeric_sort(&var.sort)
            })
            .collect();
        if bv_vars.is_empty() || per_var_cap == 0 {
            return FxHashMap::default();
        }

        let mut values_by_var: FxHashMap<String, Vec<i64>> = FxHashMap::default();
        let mut seen_by_var: FxHashMap<String, FxHashSet<i64>> = FxHashMap::default();

        for entry in entries.iter().rev() {
            let mut all_vars_full = true;

            for var in &bv_vars {
                let values = values_by_var.entry(var.name.clone()).or_default();
                if values.len() >= per_var_cap {
                    continue;
                }
                all_vars_full = false;

                let Some(&value) = entry.get(&var.name) else {
                    continue;
                };
                let seen = seen_by_var.entry(var.name.clone()).or_default();
                if seen.insert(value) {
                    values.push(value);
                }
            }

            if all_vars_full {
                break;
            }
        }

        values_by_var.retain(|_, values| !values.is_empty());
        values_by_var
    }

    /// Check if a lemma (invariant form) is inductive at the given level.
    /// This is the dual of is_inductive_blocking: we check NOT(lemma) is blocked.
    pub(in crate::pdr::solver) fn is_lemma_inductive(
        &mut self,
        lemma: &ChcExpr,
        predicate: PredicateId,
        level: usize,
    ) -> bool {
        // A lemma I is inductive if NOT(I) is not reachable from frame[level-1]
        // This is equivalent to: frame[level-1] ∧ T ∧ NOT(I) is UNSAT
        let blocking_formula = ChcExpr::not(lemma.clone());
        self.is_inductive_blocking(&blocking_formula, predicate, level)
    }

    /// Simplify a model by removing semantically redundant conjuncts.
    ///
    /// Ports Z3 Spacer's unconditional `simplify_formulas()` at solve completion
    /// (`spacer_context.cpp:2757-2758`). For each predicate interpretation in the
    /// model, decomposes the formula into conjuncts and checks if any conjunct is
    /// implied by the conjunction of the others (i.e., `AND(others) AND NOT(target)`
    /// is UNSAT). Subsumed conjuncts are removed.
    ///
    /// This produces a cleaner, more minimal invariant without affecting correctness
    /// (only strictly weaker conjuncts are removed).
    ///
    /// Returns `true` if the model was modified (conjuncts removed or free-variable
    /// sanitization triggered). Callers should re-verify the simplified model and,
    /// when re-verification fails, fall back to the pre-simplification model if
    /// one was already verified (#5922, #6049).
    pub(in crate::pdr::solver) fn simplify_model(
        &mut self,
        model: &mut InvariantModel,
    ) -> SimplifyResult {
        let max_group_size = 64;
        let mut total_removed = 0usize;

        for interp in model.interpretations.values_mut() {
            let conjuncts: Vec<ChcExpr> = interp.formula.conjuncts().into_iter().cloned().collect();

            let n = conjuncts.len();
            if n < 2 || n > max_group_size {
                continue;
            }

            let mut deleted = vec![false; n];
            let mut removed = 0usize;

            for i in 0..n {
                if deleted[i] {
                    continue;
                }

                // Build conjunction of all other non-deleted conjuncts
                let others: Vec<ChcExpr> = (0..n)
                    .filter(|&j| j != i && !deleted[j])
                    .map(|j| conjuncts[j].clone())
                    .collect();

                if others.is_empty() {
                    continue;
                }

                // Query: AND(others) AND NOT(target) — UNSAT means target is subsumed
                let conjunction = others
                    .into_iter()
                    .reduce(ChcExpr::and)
                    .expect("others is non-empty");
                let negated_target = ChcExpr::not(conjuncts[i].clone());
                let query = ChcExpr::and(conjunction, negated_target);

                // Skip mod/div-heavy queries: Euclidean decomposition with large
                // moduli (e.g., mod 23468) exceeds the SMT node budget and hangs
                // indefinitely, blocking the engine from returning its result.
                if query.contains_mod_or_div() {
                    continue;
                }
                self.smt.reset();
                match self
                    .smt
                    .check_sat_with_timeout(&query, std::time::Duration::from_millis(200))
                {
                    SmtResult::Unsat
                    | SmtResult::UnsatWithCore(_)
                    | SmtResult::UnsatWithFarkas(_) => {
                        deleted[i] = true;
                        removed += 1;
                    }
                    _ => {}
                }
            }

            if removed > 0 {
                let surviving: Vec<ChcExpr> = conjuncts
                    .into_iter()
                    .enumerate()
                    .filter(|(i, _)| !deleted[*i])
                    .map(|(_, e)| e)
                    .collect();

                interp.formula = if surviving.is_empty() {
                    ChcExpr::Bool(true)
                } else {
                    ChcExpr::and_all(surviving)
                };

                total_removed += removed;
            }
        }

        if total_removed > 0 && self.config.verbose {
            safe_eprintln!(
                "PDR: Simplified model: removed {} redundant conjuncts",
                total_removed
            );
        }

        // Sanitize free variables: remove conjuncts referencing variables not
        // declared as parameters. This prevents model output from containing
        // undeclared variables that cause Z3 "unknown constant" errors during
        // consumer model verification (fixes #5246).
        //
        // Returns true if sanitization weakened the model (removed conjuncts).
        // Callers must re-verify when this happens (#5805).
        let sanitized_free_vars = model.sanitize_free_variables();

        // SOUNDNESS (#5922): Return structured info about what was modified.
        // - redundancy_removed: conjuncts eliminated by subsumption checks.
        //   The pre-simplification model was valid; if the simplified model fails
        //   re-verification, callers should fall back to the pre-simplification model.
        // - free_vars_sanitized: conjuncts stripped due to undeclared variables.
        //   The pre-simplification model may be fundamentally invalid (#5805);
        //   callers should NOT fall back and should instead continue searching.
        SimplifyResult {
            redundancy_removed: total_removed > 0,
            free_vars_sanitized: sanitized_free_vars,
        }
    }
}
