// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model construction from frame lemmas.
//!
//! Contains frame-based model builders, convergence checking,
//! algebraic model builders, and conjunct manipulation utilities.
//! Inductiveness-filtered and iterative weakening builders are in submodules.

mod inductive_lemmas;
mod iterative_weakening;

use super::{
    ChcExpr, ChcVar, FxHashMap, FxHashSet, InvariantModel, PdrSolver, PredicateId,
    PredicateInterpretation,
};
use crate::problem::ArrayScalarizedArg;
use crate::{ChcOp, ChcSort};

impl PdrSolver {
    /// Fallibly translate a model from PDR's internally scalarized array
    /// signature back to the original predicate signatures. Any missing map or
    /// arity mismatch is a solver bug, so callers must fail closed.
    pub(in crate::pdr::solver) fn try_translate_array_scalarized_model(
        &self,
        mut model: InvariantModel,
    ) -> Option<InvariantModel> {
        for map in self.array_scalarization_maps.iter().rev() {
            model = Self::translate_model_through_array_scalarization(model, map)?;
        }
        Some(model)
    }

    fn translate_model_through_array_scalarization(
        model: InvariantModel,
        map: &crate::problem::ArrayScalarizationMap,
    ) -> Option<InvariantModel> {
        let mut result = InvariantModel::new();
        result.verification_method = model.verification_method;
        result.individually_inductive = model.individually_inductive;
        result.convergence_proven = model.convergence_proven;

        for (pid, interp) in model.iter() {
            let arg_map = map.pred_args.get(pid)?;
            let original_pred = map.original_predicates.get(pid.index())?;
            if interp.vars.len() != arg_map.len() {
                return None;
            }

            let original_vars: Vec<ChcVar> = original_pred
                .arg_sorts
                .iter()
                .enumerate()
                .map(|(idx, sort)| ChcVar::new(crate::canonical_var_name(*pid, idx), sort.clone()))
                .collect();
            let mut substitutions = Vec::with_capacity(arg_map.len());
            for (var, mapping) in interp.vars.iter().cloned().zip(arg_map.iter()) {
                let replacement = match mapping {
                    ArrayScalarizedArg::Original(arg_idx) => {
                        original_vars.get(*arg_idx).cloned().map(ChcExpr::var)?
                    }
                    ArrayScalarizedArg::Select {
                        original_arg,
                        index,
                    } => original_vars
                        .get(*original_arg)
                        .cloned()
                        .map(|array_var| ChcExpr::select(ChcExpr::var(array_var), index.clone()))?,
                };
                substitutions.push((var, replacement));
            }

            let formula = interp
                .formula
                .substitute(&substitutions)
                .simplify_constants();
            result.set(*pid, PredicateInterpretation::new(original_vars, formula));
        }

        Some(result)
    }

    /// Build a model from the invariant at a frame.
    ///
    /// Optionally filters out blocking lemmas (not (and ...) patterns) from the model.
    /// This is useful when the full frame contains blocking lemmas that aren't inductive,
    /// but the core invariants (bounds, relations, sums) are correct.
    pub(in crate::pdr::solver) fn build_model_from_frame(
        &self,
        frame_idx: usize,
    ) -> InvariantModel {
        self.build_model_from_frame_impl(frame_idx, false)
    }

    /// Build a model from the invariant at a frame, filtering blocking lemmas.
    pub(in crate::pdr::solver) fn build_model_from_frame_filtered(
        &self,
        frame_idx: usize,
    ) -> InvariantModel {
        self.build_model_from_frame_impl(frame_idx, true)
    }

    pub(in crate::pdr::solver) fn build_model_from_frame_impl(
        &self,
        frame_idx: usize,
        filter_blocking: bool,
    ) -> InvariantModel {
        self.build_model_from_frame_impl_inner(frame_idx, filter_blocking)
            .0
    }

    /// Build the frame model and report whether any non-canonical conjuncts
    /// were removed. When `filtered_any` is false, the returned model is the
    /// full converged frame conjunction and frame convergence proves it
    /// inductive. (#5970)
    fn build_model_from_frame_impl_inner(
        &self,
        frame_idx: usize,
        filter_blocking: bool,
    ) -> (InvariantModel, bool) {
        let mut model = InvariantModel::new();
        let mut filtered_any = false;
        let query_relevant_predicates = self.query_relevant_predicates();

        for pred in self.problem.predicates() {
            let vars = self
                .caches
                .predicate_vars
                .get(&pred.id)
                .cloned()
                .unwrap_or_default();

            // Complete the candidate model's nullary query slice explicitly.
            //
            // PDR can prove a chain such as
            // `State(x) /\ bad(x) => error_p0 => error => false` unreachable
            // while carrying no ordinary state variables for `error_p0` or
            // `error`. Defaulting those missing frame formulas to `true`
            // produces a model that contradicts the very query PDR blocked.
            // A nullary predicate in the backward query slice is therefore
            // seeded as `false`. This includes structural facts: a
            // constraint-only defining clause may itself be UNSAT, so syntax
            // alone cannot decide whether the predicate must be true.
            //
            // This is only candidate completion, not proof authority: mark the
            // model as filtered so frame convergence cannot bypass full model
            // verification. Exact original-clause validation must establish
            // that every defining body is unreachable; otherwise the Safe
            // candidate is rejected.
            if pred.arg_sorts.is_empty() && query_relevant_predicates.contains(&pred.id) {
                model.set(
                    pred.id,
                    PredicateInterpretation::new(vars, ChcExpr::Bool(false)),
                );
                filtered_any = true;
                continue;
            }

            // Predicates outside the forward reachability slice from facts are
            // unreachable, so false is a valid interpretation for them. This
            // covers nullary query predicates with no defining clauses.
            if !self.caches.reachable_predicates.contains(&pred.id) {
                model.set(
                    pred.id,
                    PredicateInterpretation::new(vars, ChcExpr::Bool(false)),
                );
                continue;
            }

            // Reachable predicates outside the backward slice from all queries
            // cannot contribute to an error. Interpret them as true so
            // unrelated heuristic lemmas do not have to satisfy irrelevant
            // transitions.
            if !query_relevant_predicates.contains(&pred.id) {
                model.set(
                    pred.id,
                    PredicateInterpretation::new(vars, ChcExpr::Bool(true)),
                );
                continue;
            }

            let formula = self
                .cumulative_frame_constraint(frame_idx, pred.id)
                .unwrap_or(ChcExpr::Bool(true));

            // Diagnostic: log when cumulative constraint produces false (#3121)
            if matches!(formula, ChcExpr::Bool(false)) && self.config.verbose {
                safe_eprintln!(
                    "PDR: build_model_from_frame_impl: pred {} cumulative constraint is FALSE at frame {}",
                    pred.id.index(), frame_idx
                );
                // Dump individual frame lemmas to diagnose source
                for lvl in 1..=frame_idx.min(self.frames.len() - 1) {
                    for lemma in &self.frames[lvl].lemmas {
                        if lemma.predicate == pred.id {
                            safe_eprintln!(
                                "  frame[{}] lemma: {} (hash={})",
                                lvl,
                                lemma.formula,
                                lemma.formula_hash
                            );
                        }
                    }
                }
            }

            // Optionally filter blocking lemmas from the model
            let formula = if filter_blocking {
                Self::filter_blocking_lemmas(&formula)
            } else {
                formula
            };

            // #7131: Filter out conjuncts containing non-canonical variables
            // (e.g., parity witness vars `_parity_w_*`). These auxiliary variables
            // are free in the model formula. During verify_model's implication check
            // (body AND NOT head), free vars become adversarially quantified, causing
            // valid models to fail verification. Only keep conjuncts whose variables
            // are a subset of the predicate's canonical vars.
            let pre_filter_conjunct_count = formula.collect_conjuncts().len();
            let formula = Self::filter_non_canonical_conjuncts(&formula, &vars);
            let post_filter_conjunct_count = formula.collect_conjuncts().len();
            if post_filter_conjunct_count < pre_filter_conjunct_count {
                filtered_any = true;
            }

            // #7048: Propagate tight bounds as constants. When frame has
            // var >= c AND var <= c for the same variable, substitute var → c
            // throughout and simplify. This reduces invariant size dramatically
            // for multi-predicate problems (e.g., dillig02_m: 66 → ~20 lemmas),
            // making verify_model queries tractable for the LIA solver.
            let formula = Self::propagate_tight_bound_constants(&formula);

            let interp = PredicateInterpretation::new(vars, formula);
            model.set(pred.id, interp);
        }

        (model, filtered_any)
    }

    /// Predicates in the backward dependency slice from any false-head query.
    ///
    /// If a predicate is not in this set, no path from that predicate can reach a
    /// query. A safety model may interpret it as true without affecting the query
    /// result: clauses headed by irrelevant predicates are then trivially
    /// satisfied, and relevant clauses cannot depend on irrelevant body predicates
    /// by construction of the backward closure.
    pub(in crate::pdr::solver) fn query_relevant_predicates(&self) -> FxHashSet<PredicateId> {
        let mut relevant = FxHashSet::default();
        let mut worklist = Vec::new();

        for clause in self.problem.clauses() {
            if clause.head.predicate_id().is_some() {
                continue;
            }
            for (body_pred, _) in &clause.body.predicates {
                if relevant.insert(*body_pred) {
                    worklist.push(*body_pred);
                }
            }
        }

        while let Some(head_pred) = worklist.pop() {
            for clause in self.problem.clauses_defining(head_pred) {
                for (body_pred, _) in &clause.body.predicates {
                    if relevant.insert(*body_pred) {
                        worklist.push(*body_pred);
                    }
                }
            }
        }

        relevant
    }

    /// Build full-frame model and set `convergence_proven` when no conjuncts
    /// were removed by `filter_non_canonical_conjuncts`. (#5970)
    ///
    /// SOUNDNESS (#1398): If any intermediate predicate's frame is
    /// inconsistent (conjunction of lemmas is UNSAT), `convergence_proven`
    /// is NOT set. An inconsistent frame produces a vacuously-true model
    /// for that predicate which would pass query-only verification but
    /// fail transition checks. Full verification must run.
    pub(in crate::pdr::solver) fn build_model_from_frame_for_convergence(
        &self,
        frame_idx: usize,
    ) -> InvariantModel {
        let (mut model, filtered_any) = self.build_model_from_frame_impl_inner(frame_idx, false);
        if !filtered_any {
            // Check for intermediate predicate frame inconsistency.
            // If any no-init-facts predicate has an UNSAT frame, the model
            // for that predicate is vacuously true — force full verification.
            let has_inconsistent_intermediate = self.problem.predicates().iter().any(|pred| {
                if self.predicate_has_facts(pred.id) {
                    return false;
                }
                if let Some(constraint) = self.frames[frame_idx].get_predicate_constraint(pred.id) {
                    Self::formula_is_unsat(&constraint)
                } else {
                    false
                }
            });
            if !has_inconsistent_intermediate {
                model.convergence_proven = true;
            }
        }
        model
    }

    /// Quick standalone SMT check: returns true if `formula` is UNSAT.
    fn formula_is_unsat(formula: &ChcExpr) -> bool {
        use crate::smt::{SmtContext, SmtResult};
        let mut smt = SmtContext::new();
        matches!(
            smt.check_sat_with_timeout(formula, std::time::Duration::from_millis(200)),
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_)
        )
    }

    /// Filter conjuncts that contain non-canonical (auxiliary/witness) variables.
    ///
    /// Parity discovery adds LIA witness lemmas like `X = k * _parity_w + c` that
    /// contain free variables. These are useful for the internal LIA solver but
    /// poison model verification: the free variable becomes universally quantified
    /// under negation in the implication check, causing valid models to fail. (#7131)
    pub(in crate::pdr::solver) fn filter_non_canonical_conjuncts(
        formula: &ChcExpr,
        canonical_vars: &[ChcVar],
    ) -> ChcExpr {
        // Skip trivial formulas (Bool(true) / Bool(false))
        if matches!(formula, ChcExpr::Bool(_)) {
            return formula.clone();
        }
        let conjuncts = formula.collect_conjuncts();
        let canonical_names: ay_core::kani_compat::DetHashSet<&str> =
            canonical_vars.iter().map(|v| v.name.as_str()).collect();
        let filtered: Vec<ChcExpr> = conjuncts
            .into_iter()
            .filter(|c| {
                c.vars()
                    .iter()
                    .all(|v| canonical_names.contains(v.name.as_str()))
            })
            .collect();
        if filtered.is_empty() {
            ChcExpr::Bool(true)
        } else {
            ChcExpr::and_all(filtered)
        }
    }

    /// Propagate tight bounds (var >= c AND var <= c) as constant substitutions.
    ///
    /// Extracts variables with matching lower and upper bounds from a conjunction,
    /// substitutes them with their constant values, and simplifies. This reduces
    /// invariant formula size by eliminating redundant lemmas involving constant vars.
    fn propagate_tight_bound_constants(formula: &ChcExpr) -> ChcExpr {
        let conjuncts = formula.collect_conjuncts();

        // Extract lower and upper bounds for each variable
        let mut lower: FxHashMap<String, i128> = FxHashMap::default();
        let mut upper: FxHashMap<String, i128> = FxHashMap::default();

        for conj in &conjuncts {
            if let ChcExpr::Op(ChcOp::Ge, args) = conj {
                if args.len() == 2 {
                    if let (ChcExpr::Var(v), ChcExpr::Int(c)) = (args[0].as_ref(), args[1].as_ref())
                    {
                        if matches!(v.sort, ChcSort::Int) {
                            lower
                                .entry(v.name.clone())
                                .and_modify(|old| *old = (*old).max(*c))
                                .or_insert(*c);
                        }
                    }
                }
            }
            if let ChcExpr::Op(ChcOp::Le, args) = conj {
                if args.len() == 2 {
                    if let (ChcExpr::Var(v), ChcExpr::Int(c)) = (args[0].as_ref(), args[1].as_ref())
                    {
                        if matches!(v.sort, ChcSort::Int) {
                            upper
                                .entry(v.name.clone())
                                .and_modify(|old| *old = (*old).min(*c))
                                .or_insert(*c);
                        }
                    }
                }
            }
        }

        // Find variables where lower == upper (constant)
        let mut subst: Vec<(ChcVar, ChcExpr)> = Vec::new();
        for (name, lb) in &lower {
            if upper.get(name) == Some(lb) {
                subst.push((
                    ChcVar {
                        name: name.clone(),
                        sort: ChcSort::Int,
                    },
                    ChcExpr::Int(*lb),
                ));
            }
        }

        if subst.is_empty() {
            return formula.clone();
        }

        // Build explicit equalities (var = constant) for each tight-bound variable.
        // These preserve the variable bindings that apply_interp_to_args needs when
        // the substituted formula simplifies to `true`. Without these, an invariant
        // like `(a0 >= 0 AND a0 <= 0 AND a1 >= 0 AND a1 <= 0)` gets propagated to
        // `true`, losing the meaning `a0 = 0 AND a1 = 0`. (#7131)
        let mut equalities: Vec<ChcExpr> = subst
            .iter()
            .map(|(var, val)| ChcExpr::eq(ChcExpr::var(var.clone()), val.clone()))
            .collect();

        // Substitute constants into the remainder and simplify
        let simplified = formula.substitute(&subst).simplify_constants();

        // Combine equalities with any non-trivial remainder
        if matches!(simplified, ChcExpr::Bool(true)) {
            // All bounds were tight — the equalities ARE the invariant
            ChcExpr::and_all(equalities)
        } else {
            equalities.push(simplified);
            ChcExpr::and_all(equalities)
        }
    }

    /// Build a model using ONLY algebraically-verified lemmas (#5401).
    pub(in crate::pdr::solver) fn build_model_from_algebraic_lemmas(
        &self,
        frame_idx: usize,
    ) -> InvariantModel {
        let mut model = InvariantModel::new();
        for pred in self.problem.predicates() {
            let vars = self
                .caches
                .predicate_vars
                .get(&pred.id)
                .cloned()
                .unwrap_or_default();

            let mut alg_lemmas: Vec<ChcExpr> = Vec::new();
            for frame_level in 1..=frame_idx.min(self.frames.len().saturating_sub(1)) {
                for lemma in &self.frames[frame_level].lemmas {
                    if lemma.predicate == pred.id && lemma.algebraically_verified {
                        alg_lemmas.push(lemma.formula.clone());
                    }
                }
            }

            let formula = if alg_lemmas.is_empty() {
                ChcExpr::Bool(true)
            } else {
                alg_lemmas
                    .into_iter()
                    .reduce(ChcExpr::and)
                    .unwrap_or(ChcExpr::Bool(true))
            };
            // #7146: Filter conjuncts with non-canonical (witness) variables
            let formula = Self::filter_non_canonical_conjuncts(&formula, &vars);
            let interp = PredicateInterpretation::new(vars, formula);
            model.set(pred.id, interp);
        }
        model
    }

    /// Build a model from algebraically-verified lemmas PLUS a specified set of
    /// individually-verified inductive non-algebraic lemmas.
    ///
    /// Used by check_invariants_prove_safety when the algebraic-only model doesn't
    /// block errors but adding individually-inductive bounds does. The resulting model
    /// is correct by construction: every lemma is either algebraically verified or
    /// individually self-inductive (and entry-inductive for multi-predicate).
    pub(in crate::pdr::solver) fn build_model_from_algebraic_plus_inductive(
        &self,
        frame_idx: usize,
        inductive_lemmas: &[(PredicateId, ChcExpr)],
    ) -> InvariantModel {
        let mut model = InvariantModel::new();
        for pred in self.problem.predicates() {
            let vars = self
                .caches
                .predicate_vars
                .get(&pred.id)
                .cloned()
                .unwrap_or_default();

            let mut lemmas: Vec<ChcExpr> = Vec::new();
            // Collect algebraically-verified lemmas
            for frame_level in 1..=frame_idx.min(self.frames.len().saturating_sub(1)) {
                for lemma in &self.frames[frame_level].lemmas {
                    if lemma.predicate == pred.id && lemma.algebraically_verified {
                        lemmas.push(lemma.formula.clone());
                    }
                }
            }
            // Add individually-inductive non-algebraic lemmas for this predicate
            for (ind_pred, formula) in inductive_lemmas {
                if *ind_pred == pred.id {
                    lemmas.push(formula.clone());
                }
            }

            let formula = if lemmas.is_empty() {
                ChcExpr::Bool(true)
            } else {
                lemmas
                    .into_iter()
                    .reduce(ChcExpr::and)
                    .unwrap_or(ChcExpr::Bool(true))
            };
            // #7146: Filter conjuncts with non-canonical (witness) variables
            let formula = Self::filter_non_canonical_conjuncts(&formula, &vars);
            let interp = PredicateInterpretation::new(vars, formula);
            model.set(pred.id, interp);
        }
        model
    }
}

#[cfg(test)]
mod tests;
