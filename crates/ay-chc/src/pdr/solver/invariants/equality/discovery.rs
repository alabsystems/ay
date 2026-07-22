// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl PdrSolver {
    /// Discover equality invariants proactively before starting the main PDR loop.
    ///
    /// This function finds pairs of variables (vi, vj) such that:
    /// 1. vi = vj in the initial state
    /// 2. vi = vj is preserved by all transitions
    ///
    /// Such equalities are added as lemmas at level 1 to help PDR converge faster.
    /// Additionally, equality invariants are propagated to predicates defined by
    /// identity-like transitions from predicates with known equalities.
    pub(in crate::pdr::solver) fn discover_equality_invariants(&mut self) {
        // #7123: Clear the rejected-invariant cache before re-checking equalities.
        // Frame[1] content may have changed since the last pass (e.g., parity
        // invariants added by discover_parity_invariants). Previously-rejected
        // equalities may now be provable with the updated frame context.
        self.rejected_invariants.clear();

        let predicates: Vec<_> = self.problem.predicates().to_vec();

        // Store discovered equalities: (pred_id, var_i_idx, var_j_idx)
        let mut discovered_equalities: Vec<(PredicateId, usize, usize)> = Vec::new();

        // Phase 1: Discover equalities for predicates with fact clauses
        for pred in &predicates {
            // Skip predicates without fact clauses (no initial state)
            if !self.predicate_has_facts(pred.id) {
                continue;
            }

            // #3121 regression fix: removed inter-predicate skip for equality discovery.
            // Equalities discovered from init are verified by add_discovered_invariant which
            // checks: (1) init-validity, (2) SCC joint inductiveness across all predicates
            // in the cyclic SCC, and (3) entry-inductiveness for inter-predicate transitions.
            // False equalities (e.g., dillig03_m where itp can inject states violating A=B)
            // are correctly rejected by the SCC check or entry-inductiveness check.

            let canonical_vars = match self.canonical_vars(pred.id) {
                Some(v) => v.to_vec(),
                None => continue,
            };

            if canonical_vars.len() > MAX_PAIRWISE_DISCOVERY_VARS {
                continue;
            }

            // Get initial values for this predicate
            let init_values = self.get_init_values(pred.id);

            // Get var=var equalities from init constraint (e.g., B = C)
            let init_var_var_equalities = self.get_init_var_var_equalities(pred.id);

            if self.config.verbose && !init_var_var_equalities.is_empty() {
                safe_eprintln!(
                    "PDR: Found var=var equalities for pred {}: {:?}",
                    pred.id.index(),
                    init_var_var_equalities
                );
            }

            // Find pairs of variables with equal initial values
            for i in 0..canonical_vars.len() {
                // Check cancellation to support solve_timeout / portfolio solving
                if self.is_cancelled() {
                    return;
                }
                for j in (i + 1)..canonical_vars.len() {
                    let var_i = &canonical_vars[i];
                    let var_j = &canonical_vars[j];

                    // Only check integer or same-width BV variable pairs.
                    if !same_equality_candidate_sort(&var_i.sort, &var_j.sort) {
                        continue;
                    }

                    // Check if they have the same constant initial value
                    let init_i = init_values.get(&var_i.name);
                    let init_j = init_values.get(&var_j.name);

                    let equal_by_constants = match (init_i, init_j) {
                        (Some(bounds_i), Some(bounds_j)) => {
                            // Both have constant initial values that are equal
                            bounds_i.min == bounds_i.max
                                && bounds_j.min == bounds_j.max
                                && bounds_i.min == bounds_j.min
                        }
                        _ => false,
                    };

                    // Also check if there's a direct var=var equality in init constraint
                    let equal_by_var_equality = {
                        let (a, b) = if var_i.name < var_j.name {
                            (var_i.name.clone(), var_j.name.clone())
                        } else {
                            (var_j.name.clone(), var_i.name.clone())
                        };
                        init_var_var_equalities.contains(&(a, b))
                    };

                    if !equal_by_constants && !equal_by_var_equality {
                        continue;
                    }

                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: Checking equality invariant for pred {}: {} = {} (by_constants={}, by_var={})",
                            pred.id.index(),
                            var_i.name,
                            var_j.name,
                            equal_by_constants,
                            equal_by_var_equality
                        );
                    }

                    // Build the equality invariant
                    let eq_invariant =
                        ChcExpr::eq(ChcExpr::var(var_i.clone()), ChcExpr::var(var_j.clone()));

                    // Use add_discovered_invariant as the gate (not is_equality_preserved_by_transitions).
                    // This allows dependent equalities to pass once their prerequisites are in frame[1].
                    // (#1398: Relative equality discovery for phase-chain benchmarks like gj2007_m_3)
                    let added = self.add_discovered_invariant(pred.id, eq_invariant, 1);
                    if !added {
                        continue; // Will retry next fixpoint iteration
                    }

                    discovered_equalities.push((pred.id, i, j));

                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: Discovered equality invariant for pred {}: {} = {}",
                            pred.id.index(),
                            var_i.name,
                            var_j.name
                        );
                    }
                }
            }
        }

        // Phase 2: Propagate equalities through identity-like transitions
        // For clauses like: P(args) => Q(args') where args maps bijectively to args',
        // propagate equalities from P to Q

        // First, collect all propagation candidates (without mutable borrows)
        let mut propagation_candidates: Vec<(
            PredicateId,
            usize,
            usize,
            PredicateId,
            usize,
            usize,
        )> = Vec::new();

        for clause in self.problem.clauses() {
            // Must have exactly one body predicate
            if clause.body.predicates.len() != 1 {
                continue;
            }

            // Must have a predicate head (not false)
            let (head_pred, head_args) = match &clause.head {
                crate::ClauseHead::Predicate(p, args) => (*p, args),
                crate::ClauseHead::False => continue,
            };

            let (body_pred, body_args) = &clause.body.predicates[0];

            // Skip self-transitions
            if head_pred == *body_pred {
                continue;
            }

            // Build mapping: body_idx -> head_idx (for variable positions).
            // Also check if head args are direct copies of body args (bijective mapping).
            // #2492: Match by exact variable name (original behavior) or structural
            // equality for expression args. Partial var overlap is NOT sufficient
            // for equality propagation soundness.
            let mut body_to_head: FxHashMap<usize, usize> = FxHashMap::default();
            let mut is_direct_copy = true;
            for (h_idx, head_arg) in head_args.iter().enumerate() {
                let mut found = false;
                for (b_idx, body_arg) in body_args.iter().enumerate() {
                    // Match if both are the same Var, or structurally equal expressions
                    let is_match = match (head_arg, body_arg) {
                        (ChcExpr::Var(hv), ChcExpr::Var(bv)) => hv.name == bv.name,
                        (h, b) => h == b, // structural equality for expressions
                    };
                    if is_match {
                        body_to_head.insert(b_idx, h_idx);
                        found = true;
                        break;
                    }
                }
                if !found {
                    is_direct_copy = false;
                }
            }

            // Check if the constraint is trivial OR if head args are direct copies of body args
            // If head args are direct copies, equalities transfer regardless of the constraint
            // because the constraint only guards WHETHER the transition fires, not HOW values change
            let is_trivial = clause
                .body
                .constraint
                .as_ref()
                .is_none_or(|c| matches!(c, ChcExpr::Bool(true)));

            if !is_trivial && !is_direct_copy {
                continue;
            }

            // Collect propagation candidates from body_pred to head_pred
            for &(eq_pred, idx_i, idx_j) in &discovered_equalities {
                if eq_pred != *body_pred {
                    continue;
                }

                // Map indices from body to head
                let head_i = body_to_head.get(&idx_i);
                let head_j = body_to_head.get(&idx_j);

                if let (Some(&h_i), Some(&h_j)) = (head_i, head_j) {
                    propagation_candidates.push((*body_pred, idx_i, idx_j, head_pred, h_i, h_j));
                }
            }
        }

        // Now process candidates with mutable borrow
        for (body_pred, _idx_i, _idx_j, head_pred, h_i, h_j) in propagation_candidates {
            // Get canonical vars for head predicate
            let head_vars = match self.canonical_vars(head_pred) {
                Some(v) => v.to_vec(),
                None => continue,
            };

            if h_i < head_vars.len() && h_j < head_vars.len() {
                let eq_invariant = ChcExpr::eq(
                    ChcExpr::var(head_vars[h_i].clone()),
                    ChcExpr::var(head_vars[h_j].clone()),
                );

                // (#1362) Gate: check frame-strengthened self-inductiveness before adding.
                // Cross-predicate equalities from init states (e.g., inv1) may be false
                // for the target predicate (e.g., inv) when ITE transitions break the
                // equality (half_true_modif_m: a0=a2 holds at inv1 init but not through
                // inv's ITE self-loop). The check defers false equalities; they will be
                // retried on subsequent fixpoint iterations when more frame context may
                // make dependent equalities provable (gj2007_m_1 phase-chain pattern).
                let not_eq = ChcExpr::not(eq_invariant.clone());
                if !self.is_self_inductive_blocking(&not_eq, head_pred) {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: Deferring cross-predicate equality {} for pred {} \
                             (not frame-strengthened self-inductive, will retry)",
                            eq_invariant,
                            head_pred.index()
                        );
                    }
                    // (#1362 D1) Weaken equality to pair of inequalities and try each half.
                    // When x = y fails self-inductiveness, x >= y or x <= y may still hold.
                    if let ChcExpr::Op(ChcOp::Eq, ref args) = eq_invariant {
                        if args.len() == 2 {
                            let lhs = (*args[0]).clone();
                            let rhs = (*args[1]).clone();
                            let ge_ineq = ChcExpr::le(rhs.clone(), lhs.clone());
                            let added_ge =
                                self.add_discovered_invariant(head_pred, ge_ineq.clone(), 1);
                            if added_ge && self.config.verbose {
                                safe_eprintln!(
                                    "PDR: Propagated weakened >= from pred {} to pred {}: {}",
                                    body_pred.index(),
                                    head_pred.index(),
                                    ge_ineq
                                );
                            }
                            let le_ineq = ChcExpr::le(lhs, rhs);
                            let added_le =
                                self.add_discovered_invariant(head_pred, le_ineq.clone(), 1);
                            if added_le && self.config.verbose {
                                safe_eprintln!(
                                    "PDR: Propagated weakened <= from pred {} to pred {}: {}",
                                    body_pred.index(),
                                    head_pred.index(),
                                    le_ineq
                                );
                            }
                        }
                    }
                    continue;
                }

                // Equality passes frame-strengthened self-inductiveness check.
                // Use add_discovered_invariant for init-validity and deduplication gates.
                // (#1398: Relative equality propagation for phase-chain benchmarks like gj2007_m_3)
                let added = self.add_discovered_invariant(head_pred, eq_invariant.clone(), 1);
                if !added {
                    continue; // Will retry next fixpoint iteration
                }

                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: Propagated equality invariant from pred {} to pred {}: {} = {}",
                        body_pred.index(),
                        head_pred.index(),
                        head_vars[h_i].name,
                        head_vars[h_j].name
                    );
                }
            }
        }

        // Phase 3: Discover NEW equalities established at inter-predicate transitions
        // This handles cases like gj2007_m_* where at the transition P -> Q:
        // - P has invariant B = E
        // - Transition guard is A >= E
        // - At the transition point, B = E AND A >= E
        // - If transitions fire at boundary (A = E), then B = A holds
        // - B = A becomes a NEW invariant for Q (not propagated from P)
        //
        // We iterate until fixpoint because newly discovered equalities can enable
        // discovery of more equalities in subsequent transitions (chained predicates).
        let mut all_equalities = discovered_equalities;
        const MAX_TRANSITION_ITERATIONS: usize = 10;
        for iter in 0..MAX_TRANSITION_ITERATIONS {
            let new_eqs = self.discover_transition_equalities(&all_equalities);
            if new_eqs.is_empty() {
                if self.config.verbose && iter > 0 {
                    safe_eprintln!(
                        "PDR: Transition equality discovery converged after {} iterations",
                        iter + 1
                    );
                }
                break;
            }
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: Transition iteration {} discovered {} new equalities",
                    iter + 1,
                    new_eqs.len()
                );
            }
            all_equalities.extend(new_eqs);
        }
    }
}
