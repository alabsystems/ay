// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl PdrSolver {
    /// Discover bounds for variables that are defined by ITE toggle patterns.
    ///
    /// For transitions with `var' = ite(cond, 0, 1)` or `var' = ite(cond, 1, 0)`,
    /// the variable is always in {0, 1}, so we can add `var >= 0 AND var <= 1`.
    pub(in crate::pdr::solver) fn discover_ite_toggle_bounds(&mut self) {
        let predicates: Vec<_> = self.problem.predicates().to_vec();

        // Collect candidates first to avoid borrow issues
        // (predicate_id, var, var_idx, min_val, max_val)
        let mut candidates: Vec<(PredicateId, ChcVar, usize, i128, i128)> = Vec::new();

        for pred in &predicates {
            let canonical_vars = match self.canonical_vars(pred.id) {
                Some(v) => v.to_vec(),
                None => continue,
            };

            // Check all transition clauses that define this predicate
            for clause in self.problem.clauses_defining(pred.id) {
                // Skip fact clauses
                if clause.body.predicates.is_empty() {
                    continue;
                }

                let head_args = match &clause.head {
                    crate::ClauseHead::Predicate(_, args) => args,
                    crate::ClauseHead::False => continue,
                };

                // Check each head argument for ITE toggle pattern
                for (idx, head_expr) in head_args.iter().enumerate() {
                    if idx >= canonical_vars.len() {
                        continue;
                    }
                    let var = &canonical_vars[idx];
                    if !matches!(var.sort, ChcSort::Int) {
                        continue;
                    }

                    // Check if this is an ITE toggle: ite(cond, 0, 1) or ite(cond, 1, 0)
                    let (min_val, max_val) = match head_expr {
                        ChcExpr::Op(ChcOp::Ite, args) if args.len() == 3 => {
                            let then_val = Self::extract_constant(&args[1]);
                            let else_val = Self::extract_constant(&args[2]);
                            match (then_val, else_val) {
                                (Some(a), Some(b)) => (a.min(b), a.max(b)),
                                _ => continue,
                            }
                        }
                        _ => continue,
                    };

                    // Only add bounds for small ranges (like 0-1 toggle)
                    if max_val - min_val > 10 {
                        continue;
                    }

                    candidates.push((pred.id, var.clone(), idx, min_val, max_val));
                }
            }
        }

        // Deduplicate candidates by (pred_id, var_idx, min, max)
        candidates.sort_by_key(|(pid, _, idx, min, max)| (pid.index(), *idx, *min, *max));
        candidates.dedup_by_key(|(pid, _, idx, min, max)| (pid.index(), *idx, *min, *max));

        // Now verify and add bounds
        for (pred_id, var, var_idx, min_val, max_val) in candidates {
            // Verify the bounds are preserved (entry and self-loops)
            if !self.verify_ite_toggle_bounds(pred_id, &var, var_idx, min_val, max_val) {
                continue;
            }

            // Add lower bound
            let lower_bound = ChcExpr::ge(ChcExpr::var(var.clone()), ChcExpr::Int(min_val));
            let lower_already_known = self.frames.len() > 1
                && self.frames[1]
                    .lemmas
                    .iter()
                    .any(|l| l.predicate == pred_id && l.formula == lower_bound);

            if !lower_already_known {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: Discovered ITE toggle lower bound for pred {}: {} >= {}",
                        pred_id.index(),
                        var.name,
                        min_val
                    );
                }
                self.add_discovered_invariant(pred_id, lower_bound, 1);
            }

            // Add upper bound
            let upper_bound = ChcExpr::le(ChcExpr::var(var.clone()), ChcExpr::Int(max_val));
            let upper_already_known = self.frames.len() > 1
                && self.frames[1]
                    .lemmas
                    .iter()
                    .any(|l| l.predicate == pred_id && l.formula == upper_bound);

            if !upper_already_known {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: Discovered ITE toggle upper bound for pred {}: {} <= {}",
                        pred_id.index(),
                        var.name,
                        max_val
                    );
                }
                self.add_discovered_invariant(pred_id, upper_bound, 1);
            }
        }
    }

    /// Verify that ITE toggle bounds are established by entry transitions and preserved by self-loops.
    fn verify_ite_toggle_bounds(
        &mut self,
        predicate: PredicateId,
        _var: &ChcVar,
        var_idx: usize,
        min_val: i128,
        max_val: i128,
    ) -> bool {
        let canonical_vars = match self.canonical_vars(predicate) {
            Some(v) => v.to_vec(),
            None => return false,
        };

        // Check all transition clauses that define this predicate
        for clause in self.problem.clauses_defining(predicate) {
            if clause.body.predicates.is_empty() {
                continue;
            }

            if clause.body.predicates.len() != 1 {
                return false; // Conservative for hyperedges
            }

            let head_args = match &clause.head {
                crate::ClauseHead::Predicate(_, args) => args,
                crate::ClauseHead::False => continue,
            };

            if head_args.len() != canonical_vars.len() {
                return false;
            }

            let head_expr = &head_args[var_idx];
            let (body_pred, body_args) = &clause.body.predicates[0];
            let clause_constraint = clause
                .body
                .constraint
                .clone()
                .unwrap_or(ChcExpr::Bool(true));

            if *body_pred == predicate {
                // Self-loop: check preservation
                if body_args.len() != canonical_vars.len() {
                    return false;
                }
                let body_expr = &body_args[var_idx];

                // Pre-condition: body_expr in [min_val, max_val]
                let pre_lower = ChcExpr::ge(body_expr.clone(), ChcExpr::Int(min_val));
                let pre_upper = ChcExpr::le(body_expr.clone(), ChcExpr::Int(max_val));
                let pre_cond = ChcExpr::and(pre_lower, pre_upper);

                // Post must be in [min_val, max_val]
                let post_lt_min = ChcExpr::lt(head_expr.clone(), ChcExpr::Int(min_val));
                let post_gt_max = ChcExpr::gt(head_expr.clone(), ChcExpr::Int(max_val));
                let post_out_of_range = ChcExpr::or(post_lt_min, post_gt_max);

                // Query: constraint AND pre_cond AND post_out_of_range should be UNSAT
                let query =
                    ChcExpr::and(ChcExpr::and(clause_constraint, pre_cond), post_out_of_range);

                self.smt.reset();
                match self
                    .smt
                    .check_sat_with_timeout(&query, std::time::Duration::from_millis(500))
                {
                    SmtResult::Sat(_) => return false,
                    SmtResult::Unsat
                    | SmtResult::UnsatWithCore(_)
                    | SmtResult::UnsatWithFarkas(_) => continue,
                    SmtResult::Unknown => return false,
                }
            } else {
                // Entry transition: check that bounds are established
                // Get source predicate's init values to constrain the check
                let source_init_values = self.get_init_values(*body_pred);
                let source_canonical_vars = self.canonical_vars(*body_pred).map(<[ChcVar]>::to_vec);

                // Build source constraints from init values
                let mut source_constraints: Vec<ChcExpr> = Vec::new();
                if let Some(ref src_vars) = source_canonical_vars {
                    for (src_idx, src_var) in src_vars.iter().enumerate() {
                        if let Some(bounds) = source_init_values.get(&src_var.name) {
                            if bounds.min == bounds.max && src_idx < body_args.len() {
                                let constraint = ChcExpr::eq(
                                    body_args[src_idx].clone(),
                                    ChcExpr::Int(bounds.min),
                                );
                                source_constraints.push(constraint);
                            }
                        }
                    }
                }

                // Combine constraints
                let mut full_constraint = clause_constraint;
                for src_constraint in source_constraints {
                    full_constraint = ChcExpr::and(full_constraint, src_constraint);
                }

                // Post must be in [min_val, max_val]
                let post_lt_min = ChcExpr::lt(head_expr.clone(), ChcExpr::Int(min_val));
                let post_gt_max = ChcExpr::gt(head_expr.clone(), ChcExpr::Int(max_val));
                let post_out_of_range = ChcExpr::or(post_lt_min, post_gt_max);

                let query = ChcExpr::and(full_constraint, post_out_of_range);

                self.smt.reset();
                match self
                    .smt
                    .check_sat_with_timeout(&query, std::time::Duration::from_millis(500))
                {
                    SmtResult::Sat(_) => return false,
                    SmtResult::Unsat
                    | SmtResult::UnsatWithCore(_)
                    | SmtResult::UnsatWithFarkas(_) => continue,
                    SmtResult::Unknown => return false,
                }
            }
        }

        true
    }
}
