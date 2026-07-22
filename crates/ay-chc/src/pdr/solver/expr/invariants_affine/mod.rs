// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Affine invariant discovery, propagation, and divisibility.
//!
//! Contains `discover_affine_invariants` (coefficient-based discovery),
//! `filter_f1_for_affine_check` (frame filtering), invariant propagation
//! to derived predicates, and divisibility discovery from samples.

mod kernel;
mod preservation;

#[cfg(test)]
mod tests;

use super::super::invariants::{discover_divisibility_patterns, extract_variable_values};
use super::super::PdrSolver;
use crate::{ChcExpr, ChcOp, ChcSort, ChcVar, PredicateId};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};
use std::sync::Arc;

impl PdrSolver {
    /// Discover affine invariants of the form `c1*vi = c2*vj`.
    ///
    /// This targets common "count-by-k" patterns like `D = 2*E` that are not captured by
    /// simple equality or sum invariants.
    pub(in crate::pdr::solver) fn discover_affine_invariants(&mut self) {
        // Initial coefficient search space (small on purpose).
        // This covers `vi = 2*vj` and `vi = -vj` patterns.
        const COEFFICIENTS: &[(i128, i128)] = &[(2, 1), (1, 2), (-1, 1), (1, -1)];

        // Internal time budget: cap affine discovery to leave room for later passes
        // (kernel, scaled differences, triple sums, etc.) within the nonfixpoint budget.
        // Without this, SMT preservation checks on 4+ variable predicates can consume
        // 13s+, exhausting the 5s nonfixpoint budget and preventing later passes from
        // running. (#5425 s_multipl_25 fragile at 30s timeout)
        let affine_budget = std::time::Duration::from_secs(3);
        let affine_start = ay_core::time::Instant::now();

        let predicates: Vec<_> = self.problem.predicates().to_vec();

        for pred in &predicates {
            // Skip predicates without fact clauses (no initial state)
            if !self.predicate_has_facts(pred.id) {
                continue;
            }

            // Skip predicates with incoming inter-predicate transitions.
            // Affine relations discovered from init may not hold for states injected by other predicates.
            if self.has_unrestricted_incoming_inter_predicate_transitions(pred.id) {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: Skipping affine discovery for pred {} (has incoming inter-predicate transitions)",
                        pred.id.index()
                    );
                }
                continue;
            }

            let canonical_vars = match self.canonical_vars(pred.id) {
                Some(v) => v.to_vec(),
                None => continue,
            };

            // Need at least 2 variables
            if canonical_vars.len() < 2 {
                continue;
            }

            // Get initial values for this predicate
            let init_values = self.get_init_values(pred.id);

            // Sample models for symbolic init values (lazy - only computed if needed)
            let mut sampled_models: Option<Vec<FxHashMap<String, i128>>> = None;

            // Check all ordered pairs (i, j) with all coefficient combinations
            for i in 0..canonical_vars.len() {
                // Check cancellation to support portfolio solving (avoid blocking on SMT queries)
                if self.is_cancelled() {
                    return;
                }
                // Check internal time budget to leave room for later discovery passes
                if affine_start.elapsed() >= affine_budget {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: discover_affine_invariants budget exhausted ({:?} >= {:?}), stopping early",
                            affine_start.elapsed(),
                            affine_budget
                        );
                    }
                    return;
                }
                for j in 0..canonical_vars.len() {
                    if i == j {
                        continue;
                    }

                    let vi = &canonical_vars[i];
                    let vj = &canonical_vars[j];

                    if !matches!(vi.sort, ChcSort::Int) || !matches!(vj.sort, ChcSort::Int) {
                        continue;
                    }

                    // Try to get constant init values
                    let init_i = init_values.get(&vi.name).and_then(|b| {
                        if b.min == b.max {
                            Some(b.min)
                        } else {
                            None
                        }
                    });
                    let init_j = init_values.get(&vj.name).and_then(|b| {
                        if b.min == b.max {
                            Some(b.min)
                        } else {
                            None
                        }
                    });

                    // Determine which verification strategy to use
                    let use_sampling = init_i.is_none() || init_j.is_none();

                    for &(c1, c2) in COEFFICIENTS {
                        // Check budget before each SMT-heavy coefficient test
                        if affine_start.elapsed() >= affine_budget {
                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: discover_affine_invariants budget exhausted ({:?} >= {:?}), stopping early",
                                    affine_start.elapsed(),
                                    affine_budget
                                );
                            }
                            return;
                        }
                        // Skip trivial equality (handled by discover_equality_invariants)
                        if c1 == c2 {
                            continue;
                        }
                        // Skip c1 = -c2 pairs: sum invariants, already handled (#5401).
                        if c1 == -c2 {
                            continue;
                        }

                        // Check init: c1*vi = c2*vj
                        let init_valid = if let (Some(vi_val), Some(vj_val)) = (init_i, init_j) {
                            // Skip vacuously true all-zero pairs (#5401).
                            if vi_val == 0 && vj_val == 0 {
                                false
                            } else {
                                // Constant init values - direct check
                                c1.saturating_mul(vi_val) == c2.saturating_mul(vj_val)
                            }
                        } else if use_sampling {
                            // Symbolic init values - use model sampling
                            let models = sampled_models
                                .get_or_insert_with(|| self.sample_init_models(pred.id, 5));

                            // Need at least 2 diverse samples to have any confidence
                            if models.len() < 2 {
                                false
                            } else {
                                // Check if the relation holds for all COMPLETE sampled models
                                // #2268: Skip incomplete models instead of assuming 0
                                let mut complete_count = 0;
                                let mut all_valid = true;
                                for m in models.iter() {
                                    // Incomplete model - skip (SMT solver eliminated variable)
                                    if let (Some(vi_val), Some(vj_val)) =
                                        (m.get(&vi.name).copied(), m.get(&vj.name).copied())
                                    {
                                        complete_count += 1;
                                        if c1.saturating_mul(vi_val) != c2.saturating_mul(vj_val) {
                                            all_valid = false;
                                            break;
                                        }
                                    }
                                }
                                // Require at least 2 complete models for confidence
                                complete_count >= 2 && all_valid
                            }
                        } else {
                            false
                        };

                        if !init_valid {
                            continue;
                        }

                        // Check preservation by all transitions (relative to already-learned invariants)
                        if !self.is_affine_preserved_by_transitions(pred.id, i, j, c1, c2) {
                            continue;
                        }

                        let lhs = if c1 == 1 {
                            ChcExpr::var(vi.clone())
                        } else {
                            ChcExpr::mul(ChcExpr::Int(c1), ChcExpr::var(vi.clone()))
                        };
                        let rhs = if c2 == 1 {
                            ChcExpr::var(vj.clone())
                        } else {
                            ChcExpr::mul(ChcExpr::Int(c2), ChcExpr::var(vj.clone()))
                        };
                        let affine_inv = ChcExpr::eq(lhs, rhs);

                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: Discovered affine invariant for pred {}: {}*{} = {}*{}",
                                pred.id.index(),
                                c1,
                                vi.name,
                                c2,
                                vj.name
                            );
                        }

                        self.add_discovered_invariant(pred.id, affine_inv, 1);
                    }
                }
            }
        }
    }

    /// Filter F1 constraint to only include lemmas relevant for affine preservation checks.
    ///
    /// Keeps:
    /// - Equalities (Eq operations): direct support for the relation being checked
    /// - Simple bounds (Lt, Le, Gt, Ge): may constrain variable ranges
    ///
    /// Excludes:
    /// - Parity/divisibility lemmas (Mod operations): often cause SMT Unknown
    /// - Complex disjunctions (Or at top level): may blow up search space
    ///
    /// Caps at MAX_CONTEXT_LEMMAS to avoid SMT query explosion.
    pub(in crate::pdr::solver) fn filter_f1_for_affine_check(
        &self,
        f1: &ChcExpr,
    ) -> Option<ChcExpr> {
        const MAX_CONTEXT_LEMMAS: usize = 10;

        // Helper to check if a lemma is relevant for affine checks
        fn is_relevant_lemma(expr: &ChcExpr) -> bool {
            match expr {
                // Exclude parity/divisibility constraints
                _ if expr.contains_mod() => false,

                // Include equalities
                ChcExpr::Op(ChcOp::Eq, _) => true,

                // Include simple bounds
                ChcExpr::Op(ChcOp::Lt | ChcOp::Le | ChcOp::Gt | ChcOp::Ge, _) => true,

                // Exclude top-level disjunctions
                ChcExpr::Op(ChcOp::Or, _) => false,

                // Include negations of equalities (disequalities)
                ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => {
                    matches!(args[0].as_ref(), ChcExpr::Op(ChcOp::Eq, _))
                }

                // Skip other forms
                _ => false,
            }
        }

        // Flatten conjuncts
        let mut conjuncts = f1.collect_conjuncts();
        conjuncts.retain(|c| !matches!(c, ChcExpr::Bool(true)));

        // Deduplicate conjuncts: collect_conjuncts on nested And trees can
        // produce duplicates when the same lemma appears at different levels.
        let mut seen_hashes: FxHashSet<u64> = FxHashSet::default();
        conjuncts.retain(|c| {
            let h = c.structural_hash();
            seen_hashes.insert(h)
        });

        // Partition into equalities (high-value context) and other relevant lemmas.
        // Equalities like A=B are strictly more informative than bounds for scaled-diff
        // and affine preservation checks — they constrain both directions at once.
        // Without prioritization, simple bounds fill the cap before equalities (#1306).
        let mut equalities: Vec<ChcExpr> = Vec::new();
        let mut others: Vec<ChcExpr> = Vec::new();
        for c in conjuncts {
            if !is_relevant_lemma(&c) {
                continue;
            }
            if matches!(&c, ChcExpr::Op(ChcOp::Eq, _)) {
                equalities.push(c);
            } else {
                others.push(c);
            }
        }

        // Include all equalities first, then fill remaining slots with bounds.
        let filtered: Vec<ChcExpr> = equalities
            .into_iter()
            .chain(others)
            .take(MAX_CONTEXT_LEMMAS)
            .collect();

        if filtered.is_empty() {
            None
        } else if filtered.len() == 1 {
            Some(filtered.into_iter().next().expect("len == 1"))
        } else {
            Some(ChcExpr::Op(
                ChcOp::And,
                filtered.into_iter().map(Arc::new).collect(),
            ))
        }
    }

    /// Propagate discovered affine invariants from predicates with facts to derived predicates.
    ///
    /// Problem: Predicates without fact clauses (like SAD in s_multipl_24) can't have
    /// invariants discovered directly via kernel synthesis because there are no samples.
    ///
    /// Solution: If predicate A has discovered affine invariants and there's a transition
    /// A -> B, project A's invariants through the transition to get candidate invariants for B.
    ///
    /// Part of #1970 - enables solving s_multipl_24 and similar benchmarks.
    pub(in crate::pdr::solver) fn propagate_affine_invariants_to_derived_predicates(&mut self) {
        // Phase 1: Identify predicates with fact clauses (sources of affine invariants)
        let predicates_with_facts: Vec<PredicateId> = self
            .problem
            .predicates()
            .iter()
            .filter(|p| self.predicate_has_facts(p.id))
            .map(|p| p.id)
            .collect();

        if predicates_with_facts.is_empty() {
            return;
        }

        // Phase 2: Find transitions from fact-predicates to derived predicates
        let mut transitions: Vec<(PredicateId, PredicateId, Vec<ChcExpr>, Vec<ChcExpr>)> =
            Vec::new();

        for clause in self.problem.clauses() {
            let head_pred = match &clause.head {
                crate::ClauseHead::Predicate(pred, args) => {
                    if args.is_empty() {
                        continue;
                    }
                    (*pred, args.clone())
                }
                crate::ClauseHead::False => continue,
            };

            if clause.body.predicates.len() != 1 {
                continue;
            }

            let (body_pred, body_args) = &clause.body.predicates[0];

            if !predicates_with_facts.contains(body_pred) {
                continue;
            }

            if predicates_with_facts.contains(&head_pred.0) {
                continue;
            }

            transitions.push((*body_pred, head_pred.0, body_args.clone(), head_pred.1));
        }

        if transitions.is_empty() {
            return;
        }

        if self.config.verbose {
            safe_eprintln!(
                "PDR: propagate_affine_invariants: {} transitions to derived predicates",
                transitions.len()
            );
        }

        // Phase 3: Project source affine invariants through transitions
        for (src_pred, dst_pred, body_args, head_args) in transitions {
            let dst_vars = match self.canonical_vars(dst_pred) {
                Some(v) => v.to_vec(),
                None => continue,
            };

            let f1_lemmas: Vec<ChcExpr> = if self.frames.len() > 1 {
                self.frames[1]
                    .lemmas
                    .iter()
                    .filter(|l| l.predicate == src_pred)
                    .map(|l| l.formula.clone())
                    .collect()
            } else {
                Vec::new()
            };

            for lemma in &f1_lemmas {
                if let ChcExpr::Op(ChcOp::Eq, _) = lemma {
                    if let Some(projected) = Self::project_equality_through_args(
                        lemma, &body_args, &head_args, &dst_vars,
                    ) {
                        if self
                            .is_chc_expr_preserved_by_transitions(dst_pred, &projected, &dst_vars)
                        {
                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: Propagated affine invariant from pred {} to pred {}: {}",
                                    src_pred.index(),
                                    dst_pred.index(),
                                    projected
                                );
                            }
                            self.add_discovered_invariant(dst_pred, projected, 1);
                        }
                    }
                }
            }
        }
    }

    fn project_equality_through_args(
        lemma: &ChcExpr,
        body_args: &[ChcExpr],
        head_args: &[ChcExpr],
        dst_vars: &[ChcVar],
    ) -> Option<ChcExpr> {
        if let ChcExpr::Op(ChcOp::Eq, args) = lemma {
            if args.len() != 2 {
                return None;
            }

            let subst: Vec<(ChcExpr, ChcExpr)> = body_args
                .iter()
                .zip(head_args.iter())
                .map(|(b, h)| (b.clone(), h.clone()))
                .collect();

            let lhs_subst = args[0].substitute_expr_pairs(&subst);
            let rhs_subst = args[1].substitute_expr_pairs(&subst);

            let projected = ChcExpr::eq(lhs_subst, rhs_subst);

            if Self::expr_uses_only_vars(&projected, dst_vars) {
                return Some(projected);
            }
        }
        None
    }

    fn expr_uses_only_vars(expr: &ChcExpr, allowed_vars: &[ChcVar]) -> bool {
        crate::expr::maybe_grow_expr_stack(|| match expr {
            ChcExpr::Var(v) => allowed_vars.iter().any(|av| av.name == v.name),
            ChcExpr::Op(_, args) => args
                .iter()
                .all(|a| Self::expr_uses_only_vars(a, allowed_vars)),
            ChcExpr::Int(_) | ChcExpr::Bool(_) | ChcExpr::Real(_, _) => true,
            _ => false,
        })
    }

    /// Discover divisibility invariants from sampled model values.
    ///
    /// For each variable and common modulus (2, 3, 4, 5, 6), checks if all sampled
    /// values share a common remainder. If so, and the modular constraint is preserved
    /// by all transitions, adds it as a level-1 lemma.
    ///
    /// This implements Phase 1 of the development design notes:
    /// sample-based divisibility inference that complements kernel-based affine discovery.
    ///
    /// Unlike the existing `discover_parity_invariants` (which requires constant init
    /// values), this approach discovers modular patterns from diverse sampled points.
    pub(in crate::pdr::solver) fn discover_divisibility_invariants_from_samples(
        &mut self,
        predicate: PredicateId,
        int_vars: &[ChcVar],
        models: &[FxHashMap<String, i128>],
    ) {
        // Functions imported in solver.rs from self::invariants, available via `use super::*`

        // Need at least 2 diverse samples for confidence
        if models.len() < 2 {
            return;
        }

        // Extract per-variable values from samples
        let values_per_var = extract_variable_values(models, int_vars);

        // Discover divisibility patterns
        let patterns = discover_divisibility_patterns(&values_per_var);

        // Verify and add each pattern as an invariant
        for constraint in patterns {
            // Find the corresponding variable
            let var = match int_vars.iter().find(|v| v.name == constraint.var_name) {
                Some(v) => v.clone(),
                None => continue,
            };

            let div_expr = constraint.to_expr(&var);

            // Check if this modular constraint is preserved by transitions
            if self.is_chc_expr_preserved_by_transitions(predicate, &div_expr, int_vars) {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: Sample-discovered divisibility invariant for pred {}: {} mod {} = {}",
                        predicate.index(),
                        constraint.var_name,
                        constraint.modulus,
                        constraint.remainder
                    );
                }
                self.add_discovered_invariant(predicate, div_expr, 1);
            }
        }
    }
}
