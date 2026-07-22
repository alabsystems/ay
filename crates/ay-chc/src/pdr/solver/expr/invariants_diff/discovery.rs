// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Difference invariant discovery — main entry point.

use super::*;

impl PdrSolver {
    /// Discover difference invariants proactively before the PDR loop starts.
    ///
    /// For each predicate with fact clauses, finds pairs of integer variables (vi, vj) where:
    /// 1. vi and vj have constant initial values
    /// 2. vi - vj = c for some constant c in the initial state
    /// 3. The difference is preserved by all self-transitions
    ///
    /// Such difference invariants are added as lemmas at level 1.
    pub(in crate::pdr::solver) fn discover_difference_invariants(&mut self) {
        let predicates: Vec<_> = self.problem.predicates().to_vec();

        for pred in &predicates {
            // Skip predicates without fact clauses (no initial state)
            if !self.predicate_has_facts(pred.id) {
                continue;
            }

            // Skip predicates with incoming inter-predicate transitions.
            // Difference invariants from init may not hold for states injected by other predicates.
            if self.has_unrestricted_incoming_inter_predicate_transitions(pred.id) {
                continue;
            }

            let canonical_vars = match self.canonical_vars(pred.id) {
                Some(v) => v.to_vec(),
                None => continue,
            };

            if canonical_vars.len() > crate::pdr::solver::invariants::MAX_PAIRWISE_DISCOVERY_VARS {
                continue;
            }

            // Get initial values for this predicate
            let init_values = self.get_init_values(pred.id);

            // Find pairs of variables with constant initial values
            for i in 0..canonical_vars.len() {
                // Check cancellation to support solve_timeout / portfolio solving
                if self.is_cancelled() {
                    return;
                }
                for j in 0..canonical_vars.len() {
                    if i == j {
                        continue;
                    }

                    let var_i = &canonical_vars[i];
                    let var_j = &canonical_vars[j];

                    // Only check integer variables
                    if !matches!(var_i.sort, ChcSort::Int) || !matches!(var_j.sort, ChcSort::Int) {
                        continue;
                    }

                    // Check if both have constant initial values
                    let init_i = init_values.get(&var_i.name);
                    let init_j = init_values.get(&var_j.name);

                    let init_diff = match (init_i, init_j) {
                        (Some(bounds_i), Some(bounds_j))
                            if bounds_i.min == bounds_i.max && bounds_j.min == bounds_j.max =>
                        {
                            match bounds_i.min.checked_sub(bounds_j.min) {
                                Some(d) => d,
                                None => continue, // overflow: bounds too far apart
                            }
                        }
                        _ => continue,
                    };

                    // Skip if difference is 0 (equality invariant already handled)
                    if init_diff == 0 {
                        continue;
                    }

                    // Check if the difference is preserved by all transitions
                    if !self.is_difference_preserved_by_transitions(pred.id, var_i, var_j) {
                        continue;
                    }

                    // Found a valid difference invariant! Add it as a lemma.
                    let diff_expr =
                        ChcExpr::sub(ChcExpr::var(var_i.clone()), ChcExpr::var(var_j.clone()));
                    let diff_invariant = ChcExpr::eq(diff_expr, ChcExpr::Int(init_diff));

                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: Discovered difference invariant for pred {}: {} - {} = {}",
                            pred.id.index(),
                            var_i.name,
                            var_j.name,
                            init_diff
                        );
                    }

                    // Add to frame 1 (not 0, since 0 is for initial constraints)
                    self.add_discovered_invariant(pred.id, diff_invariant, 1);
                }
            }
        }

        // Phase 2: Propagate difference invariants to predicates without fact clauses
        //
        // This must support multi-phase systems (e.g. FUN -> SAD -> WEE) where invariants
        // propagated to one derived predicate enable further propagation downstream.
        //
        // We do a small fixpoint iteration: in each round, attempt to propagate new
        // (exact or lower-bound) difference constraints into no-facts predicates using
        // the CURRENT frame[1] lemmas of their predecessors.
        const MAX_PROP_ROUNDS: usize = 8;
        // Covers k=5 for benchmarks like gj2007_m_1 which need `5*C` patterns (#1545).
        const MAX_SYMBOLIC_COEFF: i128 = 6;

        let no_fact_preds: Vec<_> = predicates
            .iter()
            .filter(|p| !self.predicate_has_facts(p.id))
            .map(|p| p.id)
            .collect();

        // Precompute incoming single-source transitions for no-facts predicates.
        let mut incoming_clauses: FxHashMap<PredicateId, Vec<(HornClause, PredicateId)>> =
            FxHashMap::default();
        for pred_id in &no_fact_preds {
            let clause_info: Vec<_> = self
                .problem
                .clauses_defining(*pred_id)
                .filter_map(|clause| {
                    if clause.body.predicates.len() != 1 {
                        return None;
                    }
                    let (source_pred, _) = &clause.body.predicates[0];
                    if *source_pred == *pred_id {
                        return None;
                    }
                    Some((clause.clone(), *source_pred))
                })
                .collect();
            if !clause_info.is_empty() {
                incoming_clauses.insert(*pred_id, clause_info);
            }
        }

        // Precompute (vi, vj) pairs where vi - vj is preserved by self-loops.
        let mut preserved_diff_pairs: FxHashMap<PredicateId, Vec<(usize, usize)>> =
            FxHashMap::default();
        for pred_id in &no_fact_preds {
            let canonical_vars = match self.canonical_vars(*pred_id) {
                Some(v) => v.to_vec(),
                None => continue,
            };
            let check_level = 1;
            let entry_domain = self.entry_domain_constraint(*pred_id, check_level);
            let mut pairs = Vec::new();
            for i in 0..canonical_vars.len() {
                for j in 0..canonical_vars.len() {
                    if i == j {
                        continue;
                    }
                    let var_i = &canonical_vars[i];
                    let var_j = &canonical_vars[j];
                    if !matches!(var_i.sort, ChcSort::Int) || !matches!(var_j.sort, ChcSort::Int) {
                        continue;
                    }
                    // #1545/#1398: Condition preservation checks on the entry domain when available.
                    // Conditional-update self-loops (ITE) often preserve differences only on the
                    // reachable domain, not for arbitrary syntactic pre-states.
                    let preserved = if let Some(ed) = entry_domain.as_ref() {
                        self.is_difference_preserved_with_entry_domain(*pred_id, var_i, var_j, ed)
                    } else {
                        self.is_difference_preserved_by_transitions(*pred_id, var_i, var_j)
                    };
                    if preserved {
                        pairs.push((i, j));
                    }
                }
            }
            if !pairs.is_empty() {
                preserved_diff_pairs.insert(*pred_id, pairs);
            }
        }

        // Precompute arg indices that are syntactically preserved across all self-loops.
        // These are good symbolic RHS candidates (e.g. the loop parameter E in s_multipl_*).
        let mut preserved_self_loop_args: FxHashMap<PredicateId, Vec<usize>> = FxHashMap::default();
        for pred_id in &no_fact_preds {
            let canonical_vars = match self.canonical_vars(*pred_id) {
                Some(v) => v.to_vec(),
                None => continue,
            };

            let mut self_loops: Vec<(Vec<ChcExpr>, Vec<ChcExpr>)> = Vec::new();
            for clause in self.problem.clauses_defining(*pred_id) {
                if clause.body.predicates.len() != 1 {
                    continue;
                }
                let (body_pred, body_args) = &clause.body.predicates[0];
                if *body_pred != *pred_id {
                    continue;
                }
                let head_args = match &clause.head {
                    crate::ClauseHead::Predicate(_, a) => a.as_slice(),
                    crate::ClauseHead::False => continue,
                };
                self_loops.push((body_args.clone(), head_args.to_vec()));
            }
            if self_loops.is_empty() {
                continue;
            }

            let mut preserved = Vec::new();
            for idx in 0..canonical_vars.len() {
                let ok = self_loops.iter().all(|(body_args, head_args)| {
                    if idx >= body_args.len() || idx >= head_args.len() {
                        return false;
                    }
                    match (&body_args[idx], &head_args[idx]) {
                        (ChcExpr::Var(bv), ChcExpr::Var(hv)) => bv.name == hv.name,
                        _ => false,
                    }
                });
                if ok {
                    preserved.push(idx);
                }
            }

            if !preserved.is_empty() {
                preserved_self_loop_args.insert(*pred_id, preserved);
            }
        }

        let mut round = 0;
        let mut changed = true;
        while changed && round < MAX_PROP_ROUNDS {
            round += 1;
            changed = false;

            for pred_id in &no_fact_preds {
                let canonical_vars = match self.canonical_vars(*pred_id) {
                    Some(v) => v.to_vec(),
                    None => continue,
                };

                let diff_pairs = match preserved_diff_pairs.get(pred_id) {
                    Some(p) => p.as_slice(),
                    None => continue,
                };

                // Attempt constant-entry propagation (exact and bounded), per incoming transition.
                if let Some(clause_info) = incoming_clauses.get(pred_id) {
                    for (clause, source_pred) in clause_info {
                        let entry_values = self.compute_entry_values_from_transition(
                            clause,
                            *source_pred,
                            *pred_id,
                        );

                        for &(i, j) in diff_pairs {
                            let var_i = &canonical_vars[i];
                            let var_j = &canonical_vars[j];

                            let entry_i = entry_values.get(&var_i.name);
                            let entry_j = entry_values.get(&var_j.name);

                            // Case 1: Both have exact values -> exact difference vi - vj = k
                            if let (Some(bi), Some(bj)) = (entry_i, entry_j) {
                                if bi.min == bi.max && bj.min == bj.max {
                                    let entry_diff = bi.min - bj.min;
                                    if entry_diff != 0 {
                                        let diff_expr = ChcExpr::sub(
                                            ChcExpr::var(var_i.clone()),
                                            ChcExpr::var(var_j.clone()),
                                        );
                                        let diff_invariant =
                                            ChcExpr::eq(diff_expr, ChcExpr::Int(entry_diff));

                                        if !self.frames[1].contains_lemma(*pred_id, &diff_invariant)
                                            && self.add_discovered_invariant(
                                                *pred_id,
                                                diff_invariant.clone(),
                                                1,
                                            )
                                        {
                                            if self.config.verbose {
                                                safe_eprintln!(
                                                    "PDR: Propagated difference invariant for pred {} (no facts): {} - {} = {}",
                                                    pred_id.index(),
                                                    var_i.name,
                                                    var_j.name,
                                                    entry_diff
                                                );
                                            }
                                            changed = true;
                                        }
                                    }
                                }
                            }

                            // Case 2: Lower bound difference vi - vj >= k from min/max bounds
                            if let (Some(bi), Some(bj)) = (entry_i, entry_j) {
                                let min_i = bi.min;
                                let max_j = bj.max;
                                if min_i > i128::MIN / 2
                                    && max_j < i128::MAX / 2
                                    && min_i - max_j > 0
                                {
                                    let lower_bound = min_i - max_j;
                                    let diff_expr = ChcExpr::sub(
                                        ChcExpr::var(var_i.clone()),
                                        ChcExpr::var(var_j.clone()),
                                    );
                                    let bound_invariant =
                                        ChcExpr::ge(diff_expr, ChcExpr::Int(lower_bound));

                                    if !self.frames[1].contains_lemma(*pred_id, &bound_invariant)
                                        && self.add_discovered_invariant(
                                            *pred_id,
                                            bound_invariant.clone(),
                                            1,
                                        )
                                    {
                                        if self.config.verbose {
                                            safe_eprintln!(
                                                "PDR: Propagated bounded difference invariant for pred {} (no facts): {} - {} >= {}",
                                                pred_id.index(),
                                                var_i.name,
                                                var_j.name,
                                                lower_bound
                                            );
                                        }
                                        changed = true;
                                    }
                                }
                            }
                        }
                    }
                }

                // Attempt symbolic propagation: vi - vj >= c * vk for vk preserved by self-loops.
                //
                // IMPORTANT: This must be validated on the entry domain. Blindly adding both
                // directions (vi-vj and vj-vi) for large coefficients can create inconsistent
                // startup invariant sets (e.g. s_mutants_16_m_000).
                let rhs_indices = match preserved_self_loop_args.get(pred_id) {
                    Some(v) => v.as_slice(),
                    None => continue,
                };

                // We can only validate symbolic bounds when we have an entry-domain constraint.
                // This is an over-approx of reachable entry states; if it implies the bound,
                // the bound is safe to add as a discovered invariant.
                let check_level = 1;
                let Some(entry_domain) = self.entry_domain_constraint(*pred_id, check_level) else {
                    continue;
                };

                // If the entry domain itself is UNSAT (or UNKNOWN), skip symbolic propagation.
                // An UNSAT entry domain would vacuously imply any bound and reintroduce
                // inconsistent lemma sets.
                self.smt.reset();
                match self
                    .smt
                    .check_sat_with_timeout(&entry_domain, std::time::Duration::from_millis(200))
                {
                    SmtResult::Sat(_) => {}
                    SmtResult::Unsat
                    | SmtResult::UnsatWithCore(_)
                    | SmtResult::UnsatWithFarkas(_) => {
                        continue;
                    }
                    SmtResult::Unknown => continue,
                }

                for &(i, j) in diff_pairs {
                    let var_i = &canonical_vars[i];
                    let var_j = &canonical_vars[j];
                    let diff_expr =
                        ChcExpr::sub(ChcExpr::var(var_i.clone()), ChcExpr::var(var_j.clone()));

                    for &k_idx in rhs_indices {
                        if k_idx >= canonical_vars.len() || k_idx == i || k_idx == j {
                            continue;
                        }
                        let var_k = &canonical_vars[k_idx];
                        if !matches!(var_k.sort, ChcSort::Int) {
                            continue;
                        }

                        // Pick the strongest coefficient c <= MAX_SYMBOLIC_COEFF such that:
                        // entry_domain => (vi - vj >= c * vk)
                        let mut chosen: Option<i128> = None;
                        for coeff in (1..=MAX_SYMBOLIC_COEFF).rev() {
                            let rhs = if coeff == 1 {
                                ChcExpr::var(var_k.clone())
                            } else {
                                ChcExpr::mul(ChcExpr::Int(coeff), ChcExpr::var(var_k.clone()))
                            };
                            let bound_invariant = ChcExpr::ge(diff_expr.clone(), rhs);

                            // Check implication via UNSAT of entry_domain ∧ ¬bound.
                            let query = ChcExpr::and(
                                entry_domain.clone(),
                                ChcExpr::not(bound_invariant.clone()),
                            );
                            self.smt.reset();
                            match self.smt.check_sat_with_timeout(
                                &query,
                                std::time::Duration::from_millis(200),
                            ) {
                                SmtResult::Unsat
                                | SmtResult::UnsatWithCore(_)
                                | SmtResult::UnsatWithFarkas(_) => {
                                    chosen = Some(coeff);
                                    break;
                                }
                                SmtResult::Sat(_) | SmtResult::Unknown => {}
                            }
                        }

                        let Some(coeff) = chosen else { continue };
                        let rhs = if coeff == 1 {
                            ChcExpr::var(var_k.clone())
                        } else {
                            ChcExpr::mul(ChcExpr::Int(coeff), ChcExpr::var(var_k.clone()))
                        };
                        let bound_invariant = ChcExpr::ge(diff_expr.clone(), rhs);

                        if self.frames[1].contains_lemma(*pred_id, &bound_invariant) {
                            continue;
                        }

                        if self.add_discovered_invariant(*pred_id, bound_invariant.clone(), 1) {
                            // Upgrade the stored lemma through the normal discovered-invariant
                            // path so algebraic-model building can combine it with propagated
                            // sum invariants. This is the critical proof shape for benchmarks
                            // like s_multipl_25.
                            let _ = self.add_discovered_invariant_algebraic(
                                *pred_id,
                                bound_invariant.clone(),
                                1,
                            );
                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: Propagated symbolic diff bound for pred {} (no facts): {} - {} >= {}*{}",
                                    pred_id.index(),
                                    var_i.name,
                                    var_j.name,
                                    coeff,
                                    var_k.name
                                );
                            }
                            changed = true;
                        }
                    }
                }
            }
        }
    }
}
