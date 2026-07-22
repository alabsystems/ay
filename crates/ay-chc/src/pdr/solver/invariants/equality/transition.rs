// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl PdrSolver {
    /// Discover new equalities established at inter-predicate transition points.
    ///
    /// For transitions P -> Q, checks if any equality var_i = var_j holds at the
    /// transition point (under the transition constraint and P's known invariants),
    /// even if that equality wasn't an invariant of P.
    ///
    /// Returns newly discovered equalities so they can be used in subsequent iterations.
    pub(in crate::pdr::solver) fn discover_transition_equalities(
        &mut self,
        source_equalities: &[(PredicateId, usize, usize)],
    ) -> Vec<(PredicateId, usize, usize)> {
        let mut newly_discovered: Vec<(PredicateId, usize, usize)> = Vec::new();
        // Collect candidates: (body_pred, head_pred, constraint, body_args, head_args)
        let mut transition_candidates: Vec<(
            PredicateId,
            PredicateId,
            Option<ChcExpr>,
            Vec<ChcExpr>,
            Vec<ChcExpr>,
        )> = Vec::new();

        for clause in self.problem.clauses() {
            // Must have exactly one body predicate
            if clause.body.predicates.len() != 1 {
                continue;
            }

            let (head_pred, head_args) = match &clause.head {
                crate::ClauseHead::Predicate(p, args) => (*p, args.clone()),
                crate::ClauseHead::False => continue,
            };

            let (body_pred, body_args) = &clause.body.predicates[0];

            // Only inter-predicate transitions
            if head_pred == *body_pred {
                continue;
            }

            transition_candidates.push((
                *body_pred,
                head_pred,
                clause.body.constraint.clone(),
                body_args.clone(),
                head_args,
            ));
        }

        let n_candidates = transition_candidates.len();
        if self.config.verbose {
            safe_eprintln!(
                "PDR: discover_transition_equalities - {} transition candidates",
                n_candidates
            );
        }

        // Process each transition
        for (body_pred, head_pred, constraint, body_args, head_args) in transition_candidates {
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: Checking transition equalities from pred {} to pred {} (constraint: {:?})",
                    body_pred.index(),
                    head_pred.index(),
                    constraint.as_ref().map(|c| format!("{c}"))
                );
            }

            let head_vars = match self.canonical_vars(head_pred) {
                Some(v) => v.to_vec(),
                None => continue,
            };

            if head_vars.len() < 2 || head_vars.len() > MAX_PAIRWISE_DISCOVERY_VARS {
                continue;
            }

            // Build context from source predicate's equalities
            let mut source_eqs: Vec<ChcExpr> = Vec::new();
            for &(eq_pred, idx_i, idx_j) in source_equalities {
                if eq_pred == body_pred && idx_i < body_args.len() && idx_j < body_args.len() {
                    let src_eq = ChcExpr::eq(body_args[idx_i].clone(), body_args[idx_j].clone());
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: Adding source equality from pred {}: {} = {} (indices {}, {})",
                            eq_pred.index(),
                            body_args[idx_i],
                            body_args[idx_j],
                            idx_i,
                            idx_j
                        );
                    }
                    source_eqs.push(src_eq);
                }
            }
            if self.config.verbose && source_eqs.is_empty() {
                safe_eprintln!(
                    "PDR: No source equalities for body_pred {}",
                    body_pred.index()
                );
            }

            // Build mapping from head variables to body/constraint expressions
            let mut head_to_expr: FxHashMap<usize, ChcExpr> = FxHashMap::default();
            for (h_idx, head_arg) in head_args.iter().enumerate() {
                head_to_expr.insert(h_idx, head_arg.clone());
            }

            // Check each pair of head variables for new equalities
            for i in 0..head_vars.len() {
                for j in (i + 1)..head_vars.len() {
                    // Equality candidates include Ints and same-width BVs. The BV case is
                    // important after datatype flattening: constructor payload selectors
                    // become BV-sorted predicate arguments.
                    if !same_equality_candidate_sort(&head_vars[i].sort, &head_vars[j].sort) {
                        continue;
                    }

                    // Skip if this equality is already known (discovered in previous iteration)
                    // This check must be here (not just in propagated_from block) because
                    // boundary-strengthening discovery path also needs to skip already-known equalities
                    if source_equalities.iter().any(|&(p, ii, jj)| {
                        p == head_pred && ((ii == i && jj == j) || (ii == j && jj == i))
                    }) {
                        continue;
                    }

                    let expr_i = match head_to_expr.get(&i) {
                        Some(e) => e.clone(),
                        None => continue,
                    };
                    let expr_j = match head_to_expr.get(&j) {
                        Some(e) => e.clone(),
                        None => continue,
                    };

                    // Skip if trivially equal (same expression)
                    if expr_i == expr_j {
                        continue;
                    }

                    // Check if this equality would be propagated from source (same mapping)
                    // For gate clauses (head = body + constraint), equalities pass through directly.
                    // #2660: Only variable head args can map directly to body args. Expression head
                    // args (e.g., x+1) have no direct variable mapping, so propagated_from is None
                    // and the full SMT check at line ~918 handles them correctly.
                    fn var_name(e: &ChcExpr) -> Option<&str> {
                        match e {
                            ChcExpr::Var(v) => Some(&v.name),
                            _ => None,
                        }
                    }
                    let propagated_from =
                        source_equalities.iter().find(|&&(eq_pred, idx_i, idx_j)| {
                            if eq_pred != body_pred {
                                return false;
                            }
                            let hi = var_name(&head_args[i]);
                            let hj = var_name(&head_args[j]);
                            let bi = body_args.get(idx_i).and_then(|b| var_name(b));
                            let bj = body_args.get(idx_j).and_then(|b| var_name(b));
                            let maps_direct = hi.is_some() && hi == bi && hj.is_some() && hj == bj;
                            let maps_swapped = hi.is_some() && hi == bj && hj.is_some() && hj == bi;
                            maps_direct || maps_swapped
                        });

                    if propagated_from.is_some() {
                        // This equality would be propagated through the gate clause.
                        // BUT: we must verify it's preserved by the HEAD predicate's own transitions.
                        // Gate clause only says "if source holds, head holds too" but doesn't mean
                        // the equality is preserved by head's self-transitions.
                        if !newly_discovered
                            .iter()
                            .any(|&(p, ii, jj)| p == head_pred && ii == i && jj == j)
                            && !source_equalities
                                .iter()
                                .any(|&(p, ii, jj)| p == head_pred && ii == i && jj == j)
                        {
                            // Build entry constraint from the gate clause:
                            // - The propagated equality itself (we know it holds at entry)
                            // - Any multiplicative bounds from the gate constraint (e.g., A >= 2*E)
                            let entry_constraint = Self::build_propagation_entry_constraint(
                                &constraint,
                                &head_args,
                                &head_vars,
                                i,
                                j,
                            );

                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: Checking propagation {} = {} to pred {} with entry: {:?}",
                                    head_vars[i].name,
                                    head_vars[j].name,
                                    head_pred.index(),
                                    entry_constraint.as_ref().map(|e| format!("{e}"))
                                );
                            }

                            // Verify the equality is preserved by head predicate's transitions
                            // with the derived entry constraint
                            if self.is_equality_preserved_by_transitions_with_entry(
                                head_pred,
                                i,
                                j,
                                entry_constraint,
                            ) {
                                if self.config.verbose {
                                    safe_eprintln!(
                                        "PDR: Propagating equality from pred {} to pred {}: {} = {} (indices {}, {})",
                                        body_pred.index(),
                                        head_pred.index(),
                                        head_vars[i].name,
                                        head_vars[j].name,
                                        i, j
                                    );
                                }
                                newly_discovered.push((head_pred, i, j));

                                // Add as lemma for the head predicate
                                let eq_invariant = ChcExpr::eq(
                                    ChcExpr::var(head_vars[i].clone()),
                                    ChcExpr::var(head_vars[j].clone()),
                                );
                                if !self.frames[1]
                                    .lemmas
                                    .iter()
                                    .any(|l| l.predicate == head_pred && l.formula == eq_invariant)
                                {
                                    self.add_discovered_invariant(head_pred, eq_invariant, 1);
                                }
                            } else if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: Skipping propagation {} = {} to pred {} (not preserved by transitions)",
                                    head_vars[i].name,
                                    head_vars[j].name,
                                    head_pred.index()
                                );
                            }
                        }
                        continue;
                    }

                    // Build query: constraint AND source_eqs AND (expr_i != expr_j)
                    // If UNSAT, the equality holds at the transition point
                    let mut conjuncts: Vec<ChcExpr> = Vec::new();
                    if let Some(c) = &constraint {
                        conjuncts.push(c.clone());
                    }
                    conjuncts.extend(source_eqs.clone());
                    conjuncts.push(ChcExpr::ne(expr_i.clone(), expr_j.clone()));

                    let query = conjuncts
                        .iter()
                        .cloned()
                        .reduce(ChcExpr::and)
                        .unwrap_or(ChcExpr::Bool(true));

                    let syntactic_equality = constraint
                        .as_ref()
                        .is_some_and(|c| Self::constraint_contains_equality(c, &expr_i, &expr_j));
                    self.smt.reset();
                    let result = if syntactic_equality {
                        SmtResult::Unsat
                    } else {
                        self.smt
                            .check_sat_with_timeout(&query, std::time::Duration::from_millis(200))
                    };

                    let equality_established = syntactic_equality
                        || matches!(
                            result,
                            SmtResult::Unsat
                                | SmtResult::UnsatWithCore(_)
                                | SmtResult::UnsatWithFarkas(_)
                        );

                    // If not immediately UNSAT, try boundary strengthening heuristic
                    // When constraint is `A >= E`, try adding `A = E` (boundary condition)
                    // This handles cases where the source loop increments A and exits at boundary
                    let equality_at_boundary = if !equality_established {
                        if let Some(c) = &constraint {
                            let boundary_eqs = Self::extract_boundary_equalities(c);
                            if !boundary_eqs.is_empty() {
                                if self.config.verbose {
                                    safe_eprintln!(
                                        "PDR: Trying boundary strengthening for {} = {} with {} boundary eq(s): {:?}",
                                        head_vars[i].name,
                                        head_vars[j].name,
                                        boundary_eqs.len(),
                                        boundary_eqs.iter().map(|e| format!("{e}")).collect::<Vec<_>>()
                                    );
                                    safe_eprintln!(
                                        "PDR: conjuncts = {:?}",
                                        conjuncts
                                            .iter()
                                            .map(|e| format!("{e}"))
                                            .collect::<Vec<_>>()
                                    );
                                }
                                let mut strengthened = conjuncts.clone();
                                strengthened.extend(boundary_eqs);

                                // Add body predicate's frame invariants to constrain the boundary check
                                // This ensures constraints like E >= 1 are included (from init)
                                if self.frames.len() > 1 {
                                    if let Some(frame_constraint) =
                                        self.cumulative_frame_constraint(1, body_pred)
                                    {
                                        if let Some(frame_on_body) = self.apply_to_args(
                                            body_pred,
                                            &frame_constraint,
                                            &body_args,
                                        ) {
                                            strengthened.push(frame_on_body);
                                        }
                                    }
                                }

                                let strengthened_query = strengthened
                                    .into_iter()
                                    .reduce(ChcExpr::and)
                                    .unwrap_or(ChcExpr::Bool(true));
                                if self.config.verbose {
                                    safe_eprintln!(
                                        "PDR: strengthened_query = {}",
                                        strengthened_query
                                    );
                                }

                                self.smt.reset();
                                let boundary_result = self.smt.check_sat_with_timeout(
                                    &strengthened_query,
                                    std::time::Duration::from_millis(200),
                                );
                                if self.config.verbose {
                                    safe_eprintln!(
                                        "PDR: Boundary check result: {:?}",
                                        match &boundary_result {
                                            SmtResult::Sat(m) => format!("SAT({m:?})"),
                                            SmtResult::Unsat => "UNSAT".to_string(),
                                            SmtResult::UnsatWithCore(_) => "UNSAT+core".to_string(),
                                            SmtResult::UnsatWithFarkas(_) =>
                                                "UNSAT+farkas".to_string(),
                                            SmtResult::Unknown => "UNKNOWN".to_string(),
                                        }
                                    );
                                }
                                let is_unsat = matches!(
                                    boundary_result,
                                    SmtResult::Unsat
                                        | SmtResult::UnsatWithCore(_)
                                        | SmtResult::UnsatWithFarkas(_)
                                );
                                if self.config.verbose && is_unsat {
                                    safe_eprintln!(
                                        "PDR: Boundary strengthening succeeded for {} = {}",
                                        head_vars[i].name,
                                        head_vars[j].name
                                    );
                                }
                                is_unsat
                            } else {
                                false
                            }
                        } else {
                            false
                        }
                    } else {
                        false
                    };

                    if !equality_established && !equality_at_boundary {
                        continue;
                    }

                    if self.config.verbose {
                        safe_eprintln!("PDR: Equality {} = {} established at transition (established={}, boundary={})",
                            head_vars[i].name, head_vars[j].name, equality_established, equality_at_boundary);
                    }

                    // Equality holds at transition! Check if preserved by head's transitions.
                    // For boundary-discovered equalities, we need to add an entry constraint
                    // that restricts the self-loop domain to where the equality actually holds.
                    //
                    // The boundary equality (e.g., A = C from A >= C) needs to be converted
                    // to canonical variable names for the self-loop check.
                    let entry_constraint = if equality_at_boundary {
                        if let Some(c) = &constraint {
                            // Convert boundary equalities to canonical form
                            Self::boundary_to_canonical_entry_constraint(c, &head_args, &head_vars)
                        } else {
                            None
                        }
                    } else {
                        None
                    };

                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: Checking if {} = {} is preserved by pred {}'s transitions (entry: {:?})",
                            head_vars[i].name,
                            head_vars[j].name,
                            head_pred.index(),
                            entry_constraint.as_ref().map(|e| format!("{e}"))
                        );
                    }
                    if !self.is_equality_preserved_by_transitions_with_entry(
                        head_pred,
                        i,
                        j,
                        entry_constraint,
                    ) {
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: {} = {} is NOT preserved by pred {}'s transitions",
                                head_vars[i].name,
                                head_vars[j].name,
                                head_pred.index()
                            );
                        }
                        continue;
                    }

                    // Found a new equality invariant for head predicate
                    let eq_invariant = ChcExpr::eq(
                        ChcExpr::var(head_vars[i].clone()),
                        ChcExpr::var(head_vars[j].clone()),
                    );

                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: Discovered transition equality for pred {} (from {} transition): {} = {}",
                            head_pred.index(),
                            body_pred.index(),
                            head_vars[i].name,
                            head_vars[j].name
                        );
                    }

                    let added = self.add_discovered_invariant(head_pred, eq_invariant, 1);
                    if !added {
                        // If the invariant is not actually inductive, do not treat it as a
                        // discovered source equality for later transitions. Otherwise we can
                        // chain invalid equalities and waste time on spurious candidates.
                        continue;
                    }

                    // Track this newly discovered equality for propagation
                    newly_discovered.push((head_pred, i, j));
                }
            }
        }

        newly_discovered
    }
}
