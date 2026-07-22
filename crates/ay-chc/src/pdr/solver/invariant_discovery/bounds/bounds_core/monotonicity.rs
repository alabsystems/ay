// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl PdrSolver {
    /// Conservative guard for phase-0 no-facts bound discovery.
    ///
    /// If any incoming source predicate also has transition clauses, source
    /// fact-derived init bounds are not a sound summary of target entry states.
    pub(in crate::pdr::solver) fn has_transitioning_source_predicate(
        &self,
        target: PredicateId,
    ) -> bool {
        self.problem.clauses_defining(target).any(|clause| {
            clause
                .body
                .predicates
                .iter()
                .map(|(pred, _)| *pred)
                .any(|source| {
                    source != target
                        && self
                            .problem
                            .clauses_defining(source)
                            .any(|source_clause| !source_clause.body.predicates.is_empty())
                })
        })
    }

    /// Check if a variable is monotonically non-decreasing (never goes below init value).
    ///
    /// Returns true if for all transitions: body_var >= init_val => head_var >= init_val
    pub(in crate::pdr::solver) fn is_var_non_decreasing(
        &mut self,
        predicate: PredicateId,
        var: &ChcVar,
        init_val: i128,
    ) -> bool {
        let canonical_vars = match self.canonical_vars(predicate) {
            Some(v) => v.to_vec(),
            None => return false,
        };

        // Find the index of this variable
        let var_idx = canonical_vars.iter().position(|v| v.name == var.name);
        let var_idx = match var_idx {
            Some(i) => i,
            None => return false,
        };

        // Check all transition clauses that define this predicate
        for clause in self.problem.clauses_defining(predicate) {
            // Skip fact clauses (no body predicates)
            if clause.body.predicates.is_empty() {
                continue;
            }

            // For simplicity, only handle single-body-predicate transitions
            if clause.body.predicates.len() != 1 {
                return false;
            }

            let (body_pred, body_args) = &clause.body.predicates[0];

            let head_args = match &clause.head {
                crate::ClauseHead::Predicate(_, args) => args,
                crate::ClauseHead::False => continue,
            };

            if head_args.len() != canonical_vars.len() {
                return false;
            }

            let head_var_expr = head_args[var_idx].clone();

            let clause_constraint = clause
                .body
                .constraint
                .clone()
                .unwrap_or(ChcExpr::Bool(true));

            // For cross-predicate transitions, include the source predicate's bound on
            // the body variable. The bound is preserved if:
            //   body_var >= source_init AND constraint => head_var >= target_init
            // For self-loop transitions, also check that body bound implies head bound.
            //
            // Note: For LOWER bounds (non-decreasing check), we can trust source init bounds
            // even if the source has cycles that increase the variable, because the bound only
            // gets stronger (larger). The key is that the init value is a valid lower bound.
            let query = if *body_pred != predicate {
                // Cross-predicate: get source predicate's init bounds for the body variable
                let source_canonical = self.canonical_vars(*body_pred);
                let source_bounds = self.get_init_values(*body_pred);

                if body_args.len() != source_canonical.map_or(0, <[ChcVar]>::len) {
                    return false;
                }

                // Find the body variable at the corresponding position
                if var_idx >= body_args.len() {
                    return false;
                }
                let body_var_expr = body_args[var_idx].clone();

                // Get the source predicate's init bound for this body variable position
                let source_init = source_canonical
                    .and_then(|cvars| cvars.get(var_idx).map(|cv| cv.name.clone()))
                    .and_then(|name| source_bounds.get(&name))
                    .filter(|b| b.is_valid())
                    .map(|b| b.min);

                let head_lt_init = ChcExpr::lt(head_var_expr.clone(), ChcExpr::Int(init_val));

                // If we have source bounds, include body_var >= source_min in the query
                if let Some(source_min) = source_init {
                    let body_ge_source =
                        ChcExpr::ge(body_var_expr.clone(), ChcExpr::Int(source_min));
                    ChcExpr::and(
                        ChcExpr::and(body_ge_source, clause_constraint.clone()),
                        head_lt_init,
                    )
                } else {
                    // No source bounds available, fall back to constraint-only check
                    ChcExpr::and(clause_constraint.clone(), head_lt_init)
                }
            } else {
                // Self-loop: check body_var >= init_val AND constraint => head_var >= init_val
                if body_args.len() != canonical_vars.len() {
                    return false;
                }
                let body_var_expr = body_args[var_idx].clone();
                let body_ge_init = ChcExpr::ge(body_var_expr.clone(), ChcExpr::Int(init_val));
                let head_lt_init = ChcExpr::lt(head_var_expr.clone(), ChcExpr::Int(init_val));

                // Include all known bounds for body variables in the query.
                // This ensures that when checking var_i, we use bounds on var_0..var_{i-1}
                // that have already been verified. This is critical for transitive bounds
                // like a2' = a2 + a0 + 1 where a0 >= 0 affects a2's bound.
                //
                // We use two sources of bounds:
                // 1. Init values (from fact clauses or propagation)
                // 2. Proven frame[1] lemmas (already validated bounds)
                // Frame[1] bounds are stronger than init values for predicates
                // without direct fact clauses (e.g., intermediate predicates in
                // multi-predicate chains like dillig03_m's itp predicate).
                let init_values = self.get_init_values(predicate);
                let mut all_body_bounds = vec![body_ge_init];
                for (idx, arg) in body_args.iter().enumerate() {
                    if idx == var_idx {
                        continue; // Already added above
                    }
                    let canon_name = &canonical_vars[idx].name;
                    // First try init values
                    let mut has_lower = false;
                    if let Some(bounds) = init_values.get(canon_name) {
                        if bounds.is_valid() && bounds.min > i128::MIN {
                            all_body_bounds
                                .push(ChcExpr::ge(arg.clone(), ChcExpr::Int(bounds.min)));
                            has_lower = true;
                        }
                    }
                    // If no init bound, check frame[1] for proven lower bounds
                    if !has_lower && self.frames.len() > 1 {
                        for lemma in &self.frames[1].lemmas {
                            if lemma.predicate != predicate {
                                continue;
                            }
                            if let ChcExpr::Op(ChcOp::Ge, largs) = &lemma.formula {
                                if largs.len() == 2 {
                                    if let (ChcExpr::Var(v), ChcExpr::Int(b)) =
                                        (largs[0].as_ref(), largs[1].as_ref())
                                    {
                                        if v.name == *canon_name {
                                            all_body_bounds
                                                .push(ChcExpr::ge(arg.clone(), ChcExpr::Int(*b)));
                                            break;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }

                let mut all = vec![clause_constraint.clone()];
                all.extend(all_body_bounds);
                all.push(head_lt_init);
                ChcExpr::and_all(all)
            };

            self.smt.reset();
            // Use timeout to avoid hanging on complex queries with ITE
            match self
                .smt
                .check_sat_with_timeout(&query, std::time::Duration::from_millis(500))
            {
                SmtResult::Sat(_) => {
                    // Found a transition that can decrease below init
                    return false;
                }
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                    // This transition preserves the lower bound
                    continue;
                }
                SmtResult::Unknown => {
                    // Can't verify - be conservative
                    return false;
                }
            }
        }

        true
    }

    /// Check if a variable is monotonically non-increasing (never goes above init value).
    ///
    /// Returns true if for all transitions: body_var <= init_val => head_var <= init_val
    pub(in crate::pdr::solver) fn is_var_non_increasing(
        &mut self,
        predicate: PredicateId,
        var: &ChcVar,
        init_val: i128,
    ) -> bool {
        let canonical_vars = match self.canonical_vars(predicate) {
            Some(v) => v.to_vec(),
            None => return false,
        };

        // Find the index of this variable
        let var_idx = canonical_vars.iter().position(|v| v.name == var.name);
        let var_idx = match var_idx {
            Some(i) => i,
            None => return false,
        };

        // Check all transition clauses that define this predicate
        for clause in self.problem.clauses_defining(predicate) {
            // Skip fact clauses (no body predicates)
            if clause.body.predicates.is_empty() {
                continue;
            }

            // For simplicity, only handle single-body-predicate transitions
            if clause.body.predicates.len() != 1 {
                return false;
            }

            let (body_pred, body_args) = &clause.body.predicates[0];

            let head_args = match &clause.head {
                crate::ClauseHead::Predicate(_, args) => args,
                crate::ClauseHead::False => continue,
            };

            if head_args.len() != canonical_vars.len() {
                return false;
            }

            let head_var_expr = head_args[var_idx].clone();

            let clause_constraint = clause
                .body
                .constraint
                .clone()
                .unwrap_or(ChcExpr::Bool(true));

            // For cross-predicate transitions, check if bound is preserved.
            // For self-loop transitions, also check that body bound implies head bound.
            let query = if *body_pred != predicate {
                // Cross-predicate: Only trust source predicate bounds if they're already
                // proven inductive (exist in frames). Unverified init bounds might not be
                // inductive - e.g., a source predicate might start at 0 but grow over iterations.
                let source_canonical = self.canonical_vars(*body_pred);

                if body_args.len() != source_canonical.map_or(0, <[ChcVar]>::len) {
                    return false;
                }
                if var_idx >= body_args.len() {
                    return false;
                }
                let body_var_expr = body_args[var_idx].clone();

                // Check if source predicate already has a proven upper bound for this variable
                let source_var_name =
                    source_canonical.and_then(|cvars| cvars.get(var_idx).map(|cv| cv.name.clone()));

                let verified_source_bound = source_var_name.and_then(|name| {
                    // Look for a proven bound in frames[1]
                    if self.frames.len() > 1 {
                        for lemma in &self.frames[1].lemmas {
                            if lemma.predicate == *body_pred {
                                // Check if lemma is of form (<= var bound)
                                if let ChcExpr::Op(ChcOp::Le, args) = &lemma.formula {
                                    if args.len() == 2 {
                                        if let (ChcExpr::Var(v), ChcExpr::Int(b)) =
                                            (args[0].as_ref(), args[1].as_ref())
                                        {
                                            if v.name == name {
                                                return Some(*b);
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                    None
                });

                let head_gt_init = ChcExpr::gt(head_var_expr.clone(), ChcExpr::Int(init_val));

                // If we have a verified source bound, use it; otherwise constraint-only check
                if let Some(source_max) = verified_source_bound {
                    let body_le_source =
                        ChcExpr::le(body_var_expr.clone(), ChcExpr::Int(source_max));
                    ChcExpr::and(
                        ChcExpr::and(body_le_source, clause_constraint.clone()),
                        head_gt_init,
                    )
                } else {
                    // No verified source bound - just check constraint alone
                    ChcExpr::and(clause_constraint.clone(), head_gt_init)
                }
            } else {
                // Self-loop: check body_var <= init_val AND constraint => head_var <= init_val
                if body_args.len() != canonical_vars.len() {
                    return false;
                }
                let body_var_expr = body_args[var_idx].clone();
                let body_le_init = ChcExpr::le(body_var_expr.clone(), ChcExpr::Int(init_val));
                let head_gt_init = ChcExpr::gt(head_var_expr.clone(), ChcExpr::Int(init_val));

                // Include all known bounds for body variables in the query.
                // This ensures that when checking var_i, we use bounds on var_0..var_{i-1}
                // that have already been verified.
                // Use both init values and proven frame[1] lemmas (see non-decreasing).
                let init_values = self.get_init_values(predicate);
                let mut all_body_bounds = vec![body_le_init];
                for (idx, arg) in body_args.iter().enumerate() {
                    if idx == var_idx {
                        continue; // Already added above
                    }
                    let canon_name = &canonical_vars[idx].name;
                    let mut has_lower = false;
                    let mut has_upper = false;
                    if let Some(bounds) = init_values.get(canon_name) {
                        if bounds.is_valid() {
                            if bounds.min > i128::MIN {
                                all_body_bounds
                                    .push(ChcExpr::ge(arg.clone(), ChcExpr::Int(bounds.min)));
                                has_lower = true;
                            }
                            if bounds.max < i128::MAX {
                                all_body_bounds
                                    .push(ChcExpr::le(arg.clone(), ChcExpr::Int(bounds.max)));
                                has_upper = true;
                            }
                        }
                    }
                    // Supplement with frame[1] proven bounds if init values are incomplete
                    if (!has_lower || !has_upper) && self.frames.len() > 1 {
                        for lemma in &self.frames[1].lemmas {
                            if lemma.predicate != predicate {
                                continue;
                            }
                            match &lemma.formula {
                                ChcExpr::Op(ChcOp::Ge, largs) if !has_lower && largs.len() == 2 => {
                                    if let (ChcExpr::Var(v), ChcExpr::Int(b)) =
                                        (largs[0].as_ref(), largs[1].as_ref())
                                    {
                                        if v.name == *canon_name {
                                            all_body_bounds
                                                .push(ChcExpr::ge(arg.clone(), ChcExpr::Int(*b)));
                                            has_lower = true;
                                        }
                                    }
                                }
                                ChcExpr::Op(ChcOp::Le, largs) if !has_upper && largs.len() == 2 => {
                                    if let (ChcExpr::Var(v), ChcExpr::Int(b)) =
                                        (largs[0].as_ref(), largs[1].as_ref())
                                    {
                                        if v.name == *canon_name {
                                            all_body_bounds
                                                .push(ChcExpr::le(arg.clone(), ChcExpr::Int(*b)));
                                            has_upper = true;
                                        }
                                    }
                                }
                                _ => {}
                            }
                        }
                    }
                }

                let mut all = vec![clause_constraint.clone()];
                all.extend(all_body_bounds);
                all.push(head_gt_init);
                ChcExpr::and_all(all)
            };

            self.smt.reset();
            // Use timeout to avoid hanging on complex queries with ITE
            match self
                .smt
                .check_sat_with_timeout(&query, std::time::Duration::from_millis(500))
            {
                SmtResult::Sat(_) => {
                    // Found a transition that can increase above init
                    return false;
                }
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                    // This transition preserves the upper bound
                    continue;
                }
                SmtResult::Unknown => {
                    // Can't verify - be conservative
                    return false;
                }
            }
        }

        true
    }
}
