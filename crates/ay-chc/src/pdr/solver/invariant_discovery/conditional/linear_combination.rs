// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl PdrSolver {
    /// Discover linear combination bounds combining step-bounded invariants with
    /// complementary increment relationships.
    pub(in crate::pdr::solver) fn discover_linear_combination_bounds(&mut self) {
        if self.frames.len() <= 1 {
            return;
        }

        // First collect all candidates to avoid borrow issues
        let candidates = self.collect_linear_combination_candidates();

        // Then verify and add each candidate
        for (target_pred_id, var_a, var_b, var_c, coeff, step) in candidates {
            // Build invariant: var_a + coeff*var_c < var_b + step
            let lhs = if coeff == 1 {
                ChcExpr::add(ChcExpr::var(var_a.clone()), ChcExpr::var(var_c.clone()))
            } else {
                ChcExpr::add(
                    ChcExpr::var(var_a.clone()),
                    ChcExpr::mul(ChcExpr::Int(coeff), ChcExpr::var(var_c.clone())),
                )
            };
            let rhs = ChcExpr::add(ChcExpr::var(var_b.clone()), ChcExpr::Int(step));
            let invariant = ChcExpr::lt(lhs, rhs);

            // Check if already known
            let already_known = self.frames[1]
                .lemmas
                .iter()
                .any(|l| l.predicate == target_pred_id && l.formula == invariant);
            if already_known {
                continue;
            }

            // Verify preservation
            if !self.verify_linear_combination_preserved(
                target_pred_id,
                &var_a,
                &var_b,
                &var_c,
                coeff,
                step,
            ) {
                continue;
            }

            if self.config.verbose {
                safe_eprintln!(
                    "PDR: Discovered linear combination bound for pred {}: {} + {}*{} < {} + {}",
                    target_pred_id.index(),
                    var_a.name,
                    coeff,
                    var_c.name,
                    var_b.name,
                    step,
                );
            }

            self.add_discovered_invariant(target_pred_id, invariant, 1);
        }
    }

    /// Collect linear combination bound candidates (avoids borrow issues)
    pub(in crate::pdr::solver) fn collect_linear_combination_candidates(
        &self,
    ) -> Vec<(PredicateId, ChcVar, ChcVar, ChcVar, i128, i128)> {
        let mut candidates = Vec::new();
        let predicates: Vec<_> = self.problem.predicates().to_vec();

        for target_pred in &predicates {
            let target_vars = match self.canonical_vars(target_pred.id) {
                Some(v) => v.to_vec(),
                None => continue,
            };

            // Find cross-predicate transitions to this target
            for clause in self.problem.clauses_defining(target_pred.id) {
                if clause.body.predicates.len() != 1 {
                    continue;
                }
                let (source_pred, source_args) = &clause.body.predicates[0];
                if *source_pred == target_pred.id {
                    continue;
                }

                // Get source's step-bounded invariants: var_i < var_j + step
                let source_step_bounded: Vec<_> = self.frames[1]
                    .lemmas
                    .iter()
                    .filter(|l| l.predicate == *source_pred)
                    .filter_map(|l| {
                        if let ChcExpr::Op(ChcOp::Lt, args) = &l.formula {
                            if args.len() == 2 {
                                if let ChcExpr::Var(var_i) = args[0].as_ref() {
                                    if let ChcExpr::Op(ChcOp::Add, add_args) = args[1].as_ref() {
                                        if add_args.len() == 2 {
                                            if let (ChcExpr::Var(var_j), ChcExpr::Int(step)) =
                                                (add_args[0].as_ref(), add_args[1].as_ref())
                                            {
                                                return Some((
                                                    var_i.name.clone(),
                                                    var_j.name.clone(),
                                                    *step,
                                                ));
                                            }
                                        }
                                    }
                                }
                            }
                        }
                        None
                    })
                    .collect();

                if source_step_bounded.is_empty() {
                    continue;
                }

                // Analyze target's self-loop increments
                let increment_info = self.analyze_self_loop_increments(target_pred.id);
                if increment_info.is_empty() {
                    continue;
                }

                let source_vars = match self.canonical_vars(*source_pred) {
                    Some(v) => v.to_vec(),
                    None => continue,
                };

                let head_args = match &clause.head {
                    crate::ClauseHead::Predicate(_, args) => args.as_slice(),
                    crate::ClauseHead::False => continue,
                };

                if head_args.len() != target_vars.len() {
                    continue;
                }

                // For each step-bounded invariant: var_i < var_j + step
                for (src_var_i, src_var_j, step) in &source_step_bounded {
                    let src_i_idx = source_vars.iter().position(|v| v.name == *src_var_i);
                    let src_j_idx = source_vars.iter().position(|v| v.name == *src_var_j);

                    let (src_i, src_j) = match (src_i_idx, src_j_idx) {
                        (Some(i), Some(j)) => (i, j),
                        _ => continue,
                    };

                    let src_arg_i = source_args.get(src_i);
                    let src_arg_j = source_args.get(src_j);

                    if src_arg_i.is_none() || src_arg_j.is_none() {
                        continue;
                    }

                    // #2492: Also handle expression source/head args by extracting vars
                    let mut tgt_i_idx = None;
                    let mut tgt_j_idx = None;

                    let src_name_i = src_arg_i.and_then(|a| match a {
                        ChcExpr::Var(v) => Some(v.name.clone()),
                        expr => expr.vars().into_iter().next().map(|v| v.name),
                    });
                    let src_name_j = src_arg_j.and_then(|a| match a {
                        ChcExpr::Var(v) => Some(v.name.clone()),
                        expr => expr.vars().into_iter().next().map(|v| v.name),
                    });

                    if let (Some(name_i), Some(name_j)) = (&src_name_i, &src_name_j) {
                        for (tgt_idx, head_arg) in head_args.iter().enumerate() {
                            let head_var_name: Option<String> = match head_arg {
                                ChcExpr::Var(hv) => Some(hv.name.clone()),
                                expr => expr.vars().first().map(|v| v.name.clone()),
                            };
                            if let Some(ref hname) = head_var_name {
                                if hname == name_i {
                                    tgt_i_idx = Some(tgt_idx);
                                }
                                if hname == name_j {
                                    tgt_j_idx = Some(tgt_idx);
                                }
                            }
                        }
                    }

                    let (tgt_i, tgt_j) = match (tgt_i_idx, tgt_j_idx) {
                        (Some(i), Some(j)) if i < target_vars.len() && j < target_vars.len() => {
                            (i, j)
                        }
                        _ => continue,
                    };

                    let var_a = &target_vars[tgt_i];
                    let var_b = &target_vars[tgt_j];

                    let incr_a = increment_info.get(&var_a.name).copied().unwrap_or(0);
                    let incr_b = increment_info.get(&var_b.name).copied().unwrap_or(0);

                    if incr_a != 0 || incr_b == 0 {
                        continue;
                    }

                    for (counter_name, &incr_c) in &increment_info {
                        if counter_name == &var_a.name || counter_name == &var_b.name {
                            continue;
                        }
                        if incr_c == 0 {
                            continue;
                        }
                        // Guard against i64::MIN / -1 panic
                        if incr_c == -1 && incr_b == i128::MIN {
                            continue;
                        }
                        if incr_b % incr_c != 0 {
                            continue;
                        }
                        let coeff = incr_b / incr_c;

                        let counter_idx = target_vars.iter().position(|v| v.name == *counter_name);
                        let counter_idx = match counter_idx {
                            Some(idx) => idx,
                            None => continue,
                        };
                        let var_c = &target_vars[counter_idx];

                        candidates.push((
                            target_pred.id,
                            var_a.clone(),
                            var_b.clone(),
                            var_c.clone(),
                            coeff,
                            *step,
                        ));
                    }
                }
            }
        }

        candidates
    }

    /// Analyze self-loop increments for a predicate
    pub(in crate::pdr::solver) fn analyze_self_loop_increments(
        &self,
        predicate: PredicateId,
    ) -> FxHashMap<String, i128> {
        let mut increments = FxHashMap::default();

        let canonical_vars = match self.canonical_vars(predicate) {
            Some(v) => v.to_vec(),
            None => return increments,
        };

        // Track whether we found at least one self-loop clause (#1388).
        let mut found_any_self_loop = false;

        for clause in self.problem.clauses_defining(predicate) {
            if clause.body.predicates.len() != 1 {
                continue;
            }
            let (body_pred, body_args) = &clause.body.predicates[0];
            if *body_pred != predicate {
                // Inter-predicate transition: skip, only check self-loops.
                // If zero self-loops exist, we'll return empty at the end (#1388).
                continue;
            }

            let head_args = match &clause.head {
                crate::ClauseHead::Predicate(_, args) => args.as_slice(),
                crate::ClauseHead::False => continue,
            };

            if head_args.len() != canonical_vars.len() || body_args.len() != canonical_vars.len() {
                continue;
            }

            // This is a self-loop clause
            found_any_self_loop = true;

            // For each variable, compute the increment
            for (idx, canon_var) in canonical_vars.iter().enumerate() {
                if !matches!(canon_var.sort, ChcSort::Int) {
                    continue;
                }

                let body_var_name = body_args.get(idx).and_then(|e| {
                    if let ChcExpr::Var(v) = e {
                        Some(v.name.clone())
                    } else {
                        None
                    }
                });

                let body_var_name = match body_var_name {
                    Some(n) => n,
                    None => continue,
                };

                let head_expr = &head_args[idx];

                // Check if head_expr = body_var + c for some constant c
                if let Some(offset) = Self::extract_addition_offset(head_expr, &body_var_name) {
                    increments.insert(canon_var.name.clone(), offset);
                }
            }
        }

        // If no self-loops exist, return empty (#1388).
        if !found_any_self_loop {
            return FxHashMap::default();
        }
        increments
    }
}
