// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Spurious counterexample handling: bound learning, ITE blocking,
//! affine discovery, and concrete value blocking from spurious CEX paths.

use super::*;

impl PdrSolver {
    /// Learn invariants from a spurious counterexample.
    ///
    /// Tries multiple strategies in priority order:
    /// 1. Bound negation from query bad states
    /// 2. ITE-aware blocking from witness
    /// 3. Affine relation discovery from CEX step values
    /// 4. Concrete value blocking as fallback
    pub(super) fn learn_from_spurious_cex(&mut self, cex: &Counterexample) {
        // Strategy 1: Extract bound constraints from query bad states and try
        // to learn their negations as invariants. For example, if bad state
        // is (x > 127), try to learn (x <= 127) as an invariant.
        let mut learned_bound = false;

        // Collect query info first to avoid borrow conflicts
        let query_bounds: Vec<_> = self
            .problem
            .queries()
            .filter_map(|query| {
                let (pred, _args) = query.body.predicates.first()?;
                let constraint = query.body.constraint.as_ref()?;
                let bounds = self.extract_bound_invariants_from_bad_state(constraint);
                Some((*pred, bounds))
            })
            .collect();

        for (pred, bounds) in query_bounds {
            for (var, bound_type, bound_val) in bounds {
                // Create candidate invariant: negation of bad state bound
                let candidate = match bound_type {
                    BoundType::Gt => {
                        // Bad: x > bound_val => Invariant: x <= bound_val
                        ChcExpr::le(ChcExpr::var(var.clone()), ChcExpr::Int(bound_val))
                    }
                    BoundType::Ge => {
                        // Bad: x >= bound_val => Invariant: x < bound_val
                        ChcExpr::lt(ChcExpr::var(var.clone()), ChcExpr::Int(bound_val))
                    }
                    BoundType::Lt => {
                        // Bad: x < bound_val => Invariant: x >= bound_val
                        ChcExpr::ge(ChcExpr::var(var.clone()), ChcExpr::Int(bound_val))
                    }
                    BoundType::Le => {
                        // Bad: x <= bound_val => Invariant: x > bound_val
                        ChcExpr::gt(ChcExpr::var(var.clone()), ChcExpr::Int(bound_val))
                    }
                };

                // Map to canonical variables
                if let Some(canonical_vars) = self.canonical_vars(pred) {
                    // Hoist suffix computation out of find() to avoid
                    // per-candidate String allocation in the inner loop.
                    let var_suffix = format!(
                        "_a{}",
                        var.name
                            .chars()
                            .last()
                            .unwrap_or('0')
                            .to_digit(10)
                            .unwrap_or(0)
                    );
                    let canon_candidate = if let Some(canon_var) = canonical_vars
                        .iter()
                        .find(|cv| cv.name.ends_with(&var_suffix))
                    {
                        candidate.substitute(&[(var.clone(), ChcExpr::var(canon_var.clone()))])
                    } else {
                        candidate.clone()
                    };

                    // Check if this bound is already known (#2815: O(1) per frame)
                    let already_known = self
                        .frames
                        .iter()
                        .any(|frame| frame.contains_lemma(pred, &canon_candidate));

                    // #5970: Skip bounds already rejected by self-inductiveness.
                    // Without this, the same invariant is re-checked hundreds of
                    // times in the main loop (e.g., s_multipl_11 retries
                    // (<= a0 500) 252 times, each costing an SMT query).
                    if self
                        .rejected_invariants
                        .contains(&(pred, canon_candidate.clone()))
                    {
                        continue;
                    }

                    // Check if the bound is inductive at level 0 (strongest)
                    // This ensures it will block predecessors effectively
                    let blocking_formula = ChcExpr::not(canon_candidate.clone());
                    let level = if self.is_inductive_blocking(&blocking_formula, pred, 0) {
                        0
                    } else if self.is_inductive_blocking(&blocking_formula, pred, 1) {
                        1
                    } else {
                        continue; // Not inductive, skip
                    };

                    // BUG FIX #685: Also check self-inductiveness
                    // 1-step inductiveness from init is not sufficient for bounds
                    // that can grow beyond the initial range.
                    if !self.is_self_inductive_blocking(&blocking_formula, pred) {
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: Bound invariant {} rejected (not self-inductive)",
                                canon_candidate
                            );
                        }
                        self.rejected_invariants
                            .insert((pred, canon_candidate.clone()));
                        continue;
                    }

                    if !already_known {
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: Spurious CEX - learned bound invariant {} for pred {} at level {}",
                                canon_candidate,
                                pred.index(),
                                level
                            );
                        }
                        // #2459: Discovery context — invariant represents
                        // states that ARE allowed (not a blocking lemma).
                        self.add_lemma_to_frame(Lemma::new(pred, canon_candidate, level), level);
                        learned_bound = true;
                    }
                }
            }
        }

        // Strategy 2: Try to learn ITE-aware blocking lemmas from witness
        // When the CEX involves clauses with ITE expressions, the spurious
        // path may be due to incorrect ITE branch assumptions. Extract the
        // ITE conditions and learn blocking lemmas based on init constraints.
        if !learned_bound {
            learned_bound = self.try_learn_ite_blocking_from_cex(cex);
        }

        // Strategy 3: Try convex closure on CEX step values
        // The numeric values from spurious CEX steps may reveal affine
        // relations (e.g., D = 2*C) that can be learned as invariants.
        if !learned_bound {
            learned_bound = self.try_affine_discovery_from_cex(cex);
        }

        // Fallback: if no bound learned, try blocking concrete values from CEX
        if !learned_bound {
            self.try_block_concrete_cex_values(cex);
        }
    }

    /// Block concrete variable values from the last CEX step as a fallback
    /// when no other learning strategy succeeded.
    fn try_block_concrete_cex_values(&mut self, cex: &Counterexample) {
        if let Some(last_step) = cex.steps.last() {
            // Block the values that led to the bad state
            if let Some(canonical_vars) = self.canonical_vars(last_step.predicate) {
                let conjuncts: Vec<ChcExpr> = canonical_vars
                    .iter()
                    .filter_map(|v| {
                        last_step
                            .assignments
                            .get(&v.name)
                            .map(|&val| ChcExpr::eq(ChcExpr::var(v.clone()), ChcExpr::int(val)))
                    })
                    .collect();
                if !conjuncts.is_empty() {
                    let state = ChcExpr::and_all(conjuncts);
                    // BUG FIX #685: Check self-inductiveness before blocking
                    // Point blocking lemmas can block reachable states if the
                    // blocked state is reachable in multiple transitions.
                    if self.is_self_inductive_blocking(&state, last_step.predicate) {
                        let blocking_lemma =
                            Lemma::new(last_step.predicate, ChcExpr::not(state.clone()), 1);
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: Blocking spurious last step: {}",
                                blocking_lemma.formula
                            );
                        }
                        // #2459: Blocking context.
                        self.add_blocking_lemma(blocking_lemma, 1);
                    } else if self.config.verbose {
                        safe_eprintln!(
                            "PDR: Spurious last step blocking rejected (not self-inductive): {}",
                            state
                        );
                    }
                }
            }
        }
    }
}
