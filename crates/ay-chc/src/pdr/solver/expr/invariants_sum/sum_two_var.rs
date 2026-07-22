// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl PdrSolver {
    pub(in crate::pdr::solver) fn discover_sum_invariants(&mut self) {
        let predicates: Vec<_> = self.problem.predicates().to_vec();

        // Store discovered sum invariants: (pred_id, var_i_idx, var_j_idx, sum_value)
        let mut discovered_sums: Vec<(PredicateId, usize, usize, i128)> = Vec::new();

        // Phase 1: Discover sum invariants for predicates with fact clauses
        for pred in &predicates {
            // Skip predicates without fact clauses (no initial state)
            if !self.predicate_has_facts(pred.id) {
                continue;
            }

            // Skip predicates with incoming inter-predicate transitions.
            // Sum invariants from init may not hold for states injected by other predicates.
            if self.has_unrestricted_incoming_inter_predicate_transitions(pred.id) {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: Skipping sum discovery for pred {} (has incoming inter-predicate transitions)",
                        pred.id.index()
                    );
                }
                continue;
            }

            let canonical_vars = match self.canonical_vars(pred.id) {
                Some(v) => v.to_vec(),
                None => continue,
            };

            // Get initial values for this predicate
            let init_values = self.get_init_values(pred.id);

            // Find pairs of variables with constant initial values
            for i in 0..canonical_vars.len() {
                // Check cancellation to support solve_timeout / portfolio solving
                if self.is_cancelled() {
                    return;
                }
                for j in (i + 1)..canonical_vars.len() {
                    let var_i = &canonical_vars[i];
                    let var_j = &canonical_vars[j];

                    // Only check integer variables
                    if !matches!(var_i.sort, ChcSort::Int) || !matches!(var_j.sort, ChcSort::Int) {
                        continue;
                    }

                    // Check if both have constant initial values
                    let init_i = init_values.get(&var_i.name);
                    let init_j = init_values.get(&var_j.name);

                    let init_sum = match (init_i, init_j) {
                        (Some(bounds_i), Some(bounds_j))
                            if bounds_i.min == bounds_i.max && bounds_j.min == bounds_j.max =>
                        {
                            bounds_i.min + bounds_j.min
                        }
                        _ => continue,
                    };

                    // Check if the sum is preserved by all transitions
                    if !self.is_sum_preserved_by_transitions(pred.id, var_i, var_j) {
                        continue;
                    }

                    // Track this sum invariant for propagation
                    discovered_sums.push((pred.id, i, j, init_sum));

                    // Found a valid sum invariant! Add it as a lemma.
                    let sum_expr =
                        ChcExpr::add(ChcExpr::var(var_i.clone()), ChcExpr::var(var_j.clone()));
                    let sum_invariant = ChcExpr::eq(sum_expr, ChcExpr::Int(init_sum));

                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: Discovered sum invariant for pred {}: {} + {} = {}",
                            pred.id.index(),
                            var_i.name,
                            var_j.name,
                            init_sum
                        );
                    }

                    // Add to frame 1 (not 0, since 0 is for initial constraints)
                    // Use algebraic variant since is_sum_preserved_by_transitions
                    // verifies via algebraic analysis (bypasses SMT Unknown issue #955)
                    self.add_discovered_invariant_algebraic(pred.id, sum_invariant, 1);
                }
            }
        }

        // Phase 2: Propagate sum invariants through identity-like transitions
        // For clauses like: P(args) => Q(args') where args maps bijectively to args',
        // propagate sum invariants from P to Q if the sum is preserved by Q's transitions.
        //
        // This handles cases like s_multipl_25 where:
        // - inv1 has fact clause and discovers sum invariant
        // - inv2 is populated from inv1 via identity transition
        // - inv2 does NOT have fact clause, so Phase 1 skips it
        // - But inv2 SHOULD have the same sum invariant

        // Collect propagation candidates (without mutable borrows)
        let mut propagation_candidates: Vec<(
            PredicateId, // body_pred (source)
            PredicateId, // head_pred (target)
            usize,       // source idx_i
            usize,       // source idx_j
            usize,       // target idx_i (mapped)
            usize,       // target idx_j (mapped)
            i128,        // sum_value
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

            // Build mapping: body_idx -> head_idx for variable positions that
            // are direct copies (same variable name in body and head).
            let mut body_to_head: FxHashMap<usize, usize> = FxHashMap::default();
            for (h_idx, head_arg) in head_args.iter().enumerate() {
                if let ChcExpr::Var(hv) = head_arg {
                    for (b_idx, body_arg) in body_args.iter().enumerate() {
                        if let ChcExpr::Var(bv) = body_arg {
                            if hv.name == bv.name {
                                body_to_head.insert(b_idx, h_idx);
                                break;
                            }
                        }
                    }
                }
            }

            // Propagation is sound when the specific sum-relevant head args are
            // direct variable copies from body args. The constraint only guards
            // WHETHER the transition fires, not HOW the copied values change.
            // The body_to_head mapping tracks which args are direct copies;
            // the inner loop checks that both sum vars (idx_i, idx_j) map.
            // Non-identity args (like D = -A in PRE→POST) don't affect the sum
            // of the identity-mapped args (#5401).

            // Collect propagation candidates from body_pred to head_pred
            for &(sum_pred, idx_i, idx_j, sum_value) in &discovered_sums {
                if sum_pred != *body_pred {
                    continue;
                }

                // Map indices from body to head
                let head_i = body_to_head.get(&idx_i);
                let head_j = body_to_head.get(&idx_j);

                if let (Some(&h_i), Some(&h_j)) = (head_i, head_j) {
                    propagation_candidates
                        .push((*body_pred, head_pred, idx_i, idx_j, h_i, h_j, sum_value));
                }
            }
        }

        // Process candidates with mutable borrow
        for (body_pred, head_pred, _src_i, _src_j, h_i, h_j, sum_value) in propagation_candidates {
            // Get canonical vars for head predicate
            let head_vars = match self.canonical_vars(head_pred) {
                Some(v) => v.to_vec(),
                None => continue,
            };

            if h_i >= head_vars.len() || h_j >= head_vars.len() {
                continue;
            }

            let var_i = &head_vars[h_i];
            let var_j = &head_vars[h_j];

            // Check if sum is preserved by the head predicate's transitions
            if !self.is_sum_preserved_by_transitions(head_pred, var_i, var_j) {
                continue;
            }

            // Create and add the sum invariant for the head predicate
            let sum_expr = ChcExpr::add(ChcExpr::var(var_i.clone()), ChcExpr::var(var_j.clone()));
            let sum_invariant = ChcExpr::eq(sum_expr, ChcExpr::Int(sum_value));

            if self.config.verbose {
                safe_eprintln!(
                    "PDR: Propagated sum invariant from pred {} to pred {}: {} + {} = {}",
                    body_pred.index(),
                    head_pred.index(),
                    var_i.name,
                    var_j.name,
                    sum_value
                );
            }

            // Add to frame 1
            // Use algebraic variant since is_sum_preserved_by_transitions
            // verifies via algebraic analysis (bypasses SMT Unknown issue #955)
            self.add_discovered_invariant_algebraic(head_pred, sum_invariant, 1);
        }
    }

    /// Discover sum-equals-variable invariants: vi + vj = vk
    ///
    /// Targets s_mutants_20 where the invariant is B + C = D.
    pub(in crate::pdr::solver) fn discover_sum_equals_var_invariants(&mut self) {
        let predicates: Vec<_> = self.problem.predicates().to_vec();

        for pred in &predicates {
            if !self.predicate_has_facts(pred.id)
                || self.has_unrestricted_incoming_inter_predicate_transitions(pred.id)
            {
                continue;
            }

            let vars = match self.canonical_vars(pred.id) {
                Some(v) => v.to_vec(),
                None => continue,
            };

            if vars.len() < 3 {
                continue;
            }

            // Cap at 15 integer variables — sum-equals-var is O(n^3) and the
            // candidate space grows as C(n,2)*(n-2). For n=15: 1365 candidates,
            // n=20: 3420. Cap to keep startup fast (#2816).
            let int_var_count = vars
                .iter()
                .filter(|v| matches!(v.sort, ChcSort::Int))
                .count();
            if int_var_count > 15 {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: Skipping sum-equals-var discovery for pred {} ({} int vars > 15 threshold)",
                        pred.id.index(),
                        int_var_count,
                    );
                }
                continue;
            }

            // Pre-compute init values for algebraic fast-path (#2833).
            // Avoids redundant SMT queries when init values are known constants.
            let init_values = self.get_init_values(pred.id);

            for i in 0..vars.len() {
                // Check cancellation to support solve_timeout / portfolio solving
                if self.is_cancelled() {
                    return;
                }
                for j in (i + 1)..vars.len() {
                    for k in 0..vars.len() {
                        if k == i || k == j {
                            continue;
                        }

                        let (vi, vj, vk) = (&vars[i], &vars[j], &vars[k]);

                        if !matches!(vi.sort, ChcSort::Int)
                            || !matches!(vj.sort, ChcSort::Int)
                            || !matches!(vk.sort, ChcSort::Int)
                        {
                            continue;
                        }

                        // Algebraic fast-path: if all init values are known constants,
                        // check vi_init + vj_init == vk_init without SMT (#2833).
                        let init_ok = {
                            let vi_init = init_values
                                .get(&vi.name)
                                .filter(|b| b.min == b.max)
                                .map(|b| b.min);
                            let vj_init = init_values
                                .get(&vj.name)
                                .filter(|b| b.min == b.max)
                                .map(|b| b.min);
                            let vk_init = init_values
                                .get(&vk.name)
                                .filter(|b| b.min == b.max)
                                .map(|b| b.min);
                            match (vi_init, vj_init, vk_init) {
                                (Some(a), Some(b), Some(c)) => a + b == c,
                                _ => self.sum_eq_var_holds_at_init(pred.id, vi, vj, vk),
                            }
                        };

                        if !init_ok || !self.sum_eq_var_preserved(pred.id, vi, vj, vk) {
                            continue;
                        }

                        let inv = ChcExpr::eq(
                            ChcExpr::add(ChcExpr::var(vi.clone()), ChcExpr::var(vj.clone())),
                            ChcExpr::var(vk.clone()),
                        );

                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: Discovered sum-equals-var: {} + {} = {}",
                                vi.name,
                                vj.name,
                                vk.name
                            );
                        }

                        // Use algebraic variant since sum_eq_var_preserved verifies
                        // via algebraic analysis (bypasses SMT Unknown issue #955)
                        self.add_discovered_invariant_algebraic(pred.id, inv, 1);
                    }
                }
            }
        }
    }

    fn sum_eq_var_holds_at_init(
        &mut self,
        pred: PredicateId,
        vi: &ChcVar,
        vj: &ChcVar,
        vk: &ChcVar,
    ) -> bool {
        let cvars = match self.canonical_vars(pred) {
            Some(v) => v.to_vec(),
            None => return false,
        };

        let mut fc: Option<ChcExpr> = None;
        for fact in self
            .problem
            .facts()
            .filter(|f| f.head.predicate_id() == Some(pred))
        {
            let c = fact.body.constraint.clone().unwrap_or(ChcExpr::Bool(true));
            let ha = match &fact.head {
                crate::ClauseHead::Predicate(_, a) => a.as_slice(),
                _ => continue,
            };
            if ha.len() != cvars.len() {
                continue;
            }
            let mut subst = Vec::new();
            for (arg, cv) in ha.iter().zip(cvars.iter()) {
                if let ChcExpr::Var(v) = arg {
                    if v.name != cv.name {
                        subst.push((v.clone(), ChcExpr::var(cv.clone())));
                    }
                }
            }
            let ren = if subst.is_empty() {
                c
            } else {
                c.substitute(&subst)
            };
            fc = Some(match fc {
                None => ren,
                Some(e) => ChcExpr::or(e, ren),
            });
        }

        let init = match fc {
            Some(c) => c,
            None => return false,
        };
        let sum = ChcExpr::add(ChcExpr::var(vi.clone()), ChcExpr::var(vj.clone()));
        let q = ChcExpr::and(
            init,
            ChcExpr::not(ChcExpr::eq(sum, ChcExpr::var(vk.clone()))),
        );

        self.smt.reset();
        matches!(
            self.smt
                .check_sat_with_timeout(&q, std::time::Duration::from_millis(500)),
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_)
        )
    }

    /// Propagate sum-equals-var invariants across inter-predicate transitions.
    ///
    pub(super) fn sum_eq_var_preserved(
        &mut self,
        pred: PredicateId,
        vi: &ChcVar,
        vj: &ChcVar,
        vk: &ChcVar,
    ) -> bool {
        let cvars = match self.canonical_vars(pred) {
            Some(v) => v.to_vec(),
            None => return false,
        };
        let (ii, ij, ik) = (
            cvars.iter().position(|v| v.name == vi.name),
            cvars.iter().position(|v| v.name == vj.name),
            cvars.iter().position(|v| v.name == vk.name),
        );
        let (ii, ij, ik) = match (ii, ij, ik) {
            (Some(a), Some(b), Some(c)) => (a, b, c),
            _ => return false,
        };

        let mut any = false;
        for cl in self.problem.clauses_defining(pred) {
            if cl.body.predicates.is_empty() || cl.body.predicates.len() != 1 {
                continue;
            }
            let ha = match &cl.head {
                crate::ClauseHead::Predicate(_, a) => a.as_slice(),
                _ => continue,
            };
            if ha.len() != cvars.len() {
                return false;
            }
            let (bp, ba) = &cl.body.predicates[0];
            if *bp != pred || ba.len() != cvars.len() {
                continue;
            }

            any = true;
            let con = cl.body.constraint.clone().unwrap_or(ChcExpr::Bool(true));
            let pre = ChcExpr::add(ba[ii].clone(), ba[ij].clone());
            let post = ChcExpr::add(ha[ii].clone(), ha[ij].clone());
            // Algebraic preservation check for vi + vj = vk:
            // If pre_i + pre_j = pre_k (invariant holds at pre-state), we need
            // post_i + post_j = post_k (invariant holds at post-state).
            // Equivalently: (pre_i + pre_j) - pre_k = (post_i + post_j) - post_k
            // Which is: pre_i + pre_j + post_k = post_i + post_j + pre_k
            let q = ChcExpr::and(
                con,
                ChcExpr::not(ChcExpr::eq(
                    ChcExpr::add(pre, ha[ik].clone()),
                    ChcExpr::add(post, ba[ik].clone()),
                )),
            );
            self.smt.reset();
            match self
                .smt
                .check_sat_with_timeout(&q, std::time::Duration::from_millis(500))
            {
                SmtResult::Sat(_) | SmtResult::Unknown => return false,
                _ => {}
            }
        }
        any
    }
}
