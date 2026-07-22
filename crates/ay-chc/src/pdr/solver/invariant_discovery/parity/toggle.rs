// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl PdrSolver {
    /// Discover relational parity invariants between counters and toggle variables.
    ///
    /// Pattern: variable A increments by 1 (odd increment), variable B toggles
    /// between 0 and 1. When both start at 0, the invariant `(= (mod A 2) B)` holds.
    ///
    /// Handles two representations:
    /// 1. Direct ITE: head_val = ite(body_val=0, 1, 0)
    /// 2. Split clauses: ITE decomposed into separate clauses where head_val
    ///    is a constant 0 or 1 in each clause (common after CHC normalization).
    pub(in crate::pdr::solver) fn discover_toggle_parity_invariants(&mut self) {
        let predicates: Vec<_> = self.problem.predicates().to_vec();

        for pred in &predicates {
            if !self.predicate_has_facts(pred.id) {
                continue;
            }

            let canonical_vars = match self.canonical_vars(pred.id) {
                Some(v) => v.to_vec(),
                None => continue,
            };

            let init_values = self.get_init_values(pred.id);

            // Collect self-loop clauses
            let self_loop_clauses: Vec<_> = self
                .problem
                .clauses_defining(pred.id)
                .filter(|clause| {
                    if clause.body.predicates.len() != 1 {
                        return false;
                    }
                    let (body_pred, body_args) = &clause.body.predicates[0];
                    if *body_pred != pred.id {
                        return false;
                    }
                    let head_args = match &clause.head {
                        crate::ClauseHead::Predicate(_, a) => a,
                        crate::ClauseHead::False => return false,
                    };
                    head_args.len() == canonical_vars.len()
                        && body_args.len() == canonical_vars.len()
                })
                .collect();

            if self_loop_clauses.is_empty() {
                continue;
            }

            if self.config.verbose {
                safe_eprintln!(
                    "PDR: discover_toggle_parity: pred {} has {} self-loop clauses, {} canonical vars",
                    pred.id.index(),
                    self_loop_clauses.len(),
                    canonical_vars.len(),
                );
            }

            let mut toggles: Vec<(usize, i128)> = Vec::new();
            let mut odd_counters: Vec<(usize, i128, i128)> = Vec::new();

            for (idx, var) in canonical_vars.iter().enumerate() {
                if !matches!(var.sort, ChcSort::Int) {
                    continue;
                }

                // Collect (body_val, head_val) pairs across all self-loop clauses
                let mut pairs: Vec<(&ChcExpr, &ChcExpr)> = Vec::new();
                for clause in &self_loop_clauses {
                    let body_args = &clause.body.predicates[0].1;
                    let head_args = match &clause.head {
                        crate::ClauseHead::Predicate(_, a) => a.as_slice(),
                        _ => continue,
                    };
                    pairs.push((&body_args[idx], &head_args[idx]));
                }

                // Check 1: Direct ITE toggle in a single clause
                if pairs.len() == 1 {
                    let (body_val, head_val) = pairs[0];
                    if Self::is_toggle_ite(body_val, head_val) {
                        if let Some(bounds) = init_values.get(&var.name) {
                            if bounds.min == bounds.max {
                                toggles.push((idx, bounds.min));
                            }
                        }
                        continue;
                    }
                    // Also check constraint-defined toggle in single clause
                    if let (ChcExpr::Var(pre_v), ChcExpr::Var(post_v)) = (body_val, head_val) {
                        if let Some(constr) = self_loop_clauses[0].body.constraint.as_ref() {
                            if Self::find_toggle_in_constraint(constr, &pre_v.name, &post_v.name) {
                                if let Some(bounds) = init_values.get(&var.name) {
                                    if bounds.min == bounds.max {
                                        toggles.push((idx, bounds.min));
                                    }
                                }
                                continue;
                            }
                        }
                    }
                }

                // Check 2: Split-clause toggle (#8782).
                // When ITE is decomposed, each clause sets this var to a constant.
                // Detect: all head_vals are constants in {0, 1} and not all the same.
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: discover_toggle_parity: pred {} var {} idx {} pairs.len()={} head_vals={:?}",
                        pred.id.index(),
                        var.name,
                        idx,
                        pairs.len(),
                        pairs.iter().map(|(_, hv)| format!("{}", hv)).collect::<Vec<_>>(),
                    );
                }
                if pairs.len() >= 2 {
                    let all_binary_const = pairs
                        .iter()
                        .all(|(_, hv)| matches!(hv, ChcExpr::Int(0) | ChcExpr::Int(1)));
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: discover_toggle_parity: pred {} var {} all_binary_const={}",
                            pred.id.index(),
                            var.name,
                            all_binary_const,
                        );
                    }
                    if all_binary_const {
                        let head_values: Vec<i128> = pairs
                            .iter()
                            .map(|(_, hv)| match hv {
                                ChcExpr::Int(v) => *v,
                                _ => -1,
                            })
                            .collect();
                        let has_zero = head_values.contains(&0);
                        let has_one = head_values.contains(&1);
                        if has_zero && has_one {
                            // Variable toggles between 0 and 1 across clauses
                            let init_lookup = init_values.get(&var.name);
                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: discover_toggle_parity: pred {} var {} has_zero={} has_one={} init={:?}",
                                    pred.id.index(), var.name, has_zero, has_one, init_lookup,
                                );
                            }
                            if let Some(bounds) = init_lookup {
                                if bounds.min == bounds.max
                                    && (bounds.min == 0 || bounds.min == 1)
                                    && !toggles.iter().any(|(i, _)| *i == idx)
                                {
                                    if self.config.verbose {
                                        safe_eprintln!(
                                            "PDR: Discovered split-clause toggle for pred {}: var {} init={}",
                                            pred.id.index(),
                                            var.name,
                                            bounds.min,
                                        );
                                    }
                                    toggles.push((idx, bounds.min));
                                }
                            }
                            continue;
                        }
                    }
                }

                // Check for odd-increment counter across all clauses
                let mut all_offsets: Vec<i128> = Vec::new();
                let mut offset_ok = true;
                for (ci, clause) in self_loop_clauses.iter().enumerate() {
                    let (body_val, head_val) = pairs[ci];
                    if let Some(offset) = Self::extract_simple_offset(body_val, head_val) {
                        all_offsets.push(offset);
                    } else if let (ChcExpr::Var(pre_v), ChcExpr::Var(post_v)) = (body_val, head_val)
                    {
                        if let Some(constr) = clause.body.constraint.as_ref() {
                            if let Some(offset) =
                                Self::find_offset_in_constraint(constr, &pre_v.name, &post_v.name)
                            {
                                all_offsets.push(offset);
                            } else {
                                offset_ok = false;
                                break;
                            }
                        } else {
                            offset_ok = false;
                            break;
                        }
                    } else {
                        offset_ok = false;
                        break;
                    }
                }

                if offset_ok && !all_offsets.is_empty() {
                    // All clauses must agree on the same offset for this to be a counter
                    let first = all_offsets[0];
                    if all_offsets.iter().all(|o| *o == first) && first.rem_euclid(2) != 0 {
                        if let Some(bounds) = init_values.get(&var.name) {
                            if bounds.min == bounds.max
                                && !odd_counters.iter().any(|(i, _, _)| *i == idx)
                            {
                                odd_counters.push((idx, first, bounds.min));
                            }
                        }
                    }
                }
            }

            // Generate relational invariants: (mod counter 2) = toggle
            let mut candidates: Vec<(PredicateId, ChcExpr)> = Vec::new();
            for &(toggle_idx, toggle_init) in &toggles {
                for &(counter_idx, _increment, counter_init) in &odd_counters {
                    // Check init consistency: counter_init mod 2 == toggle_init
                    if counter_init.rem_euclid(2) != toggle_init {
                        continue;
                    }

                    let counter_var = &canonical_vars[counter_idx];
                    let toggle_var = &canonical_vars[toggle_idx];

                    let invariant = ChcExpr::eq(
                        ChcExpr::mod_op(ChcExpr::var(counter_var.clone()), ChcExpr::Int(2)),
                        ChcExpr::var(toggle_var.clone()),
                    );

                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: Discovered toggle-parity invariant for pred {}: ({} mod 2) = {}",
                            pred.id.index(),
                            counter_var.name,
                            toggle_var.name,
                        );
                    }

                    candidates.push((pred.id, invariant));
                }
            }

            for (pred_id, formula) in candidates {
                self.add_discovered_invariant_algebraic(pred_id, formula, 1);
            }
        }
    }

    /// Discover toggle-conditional equality invariants.
    ///
    /// Pattern: toggle variable C alternates 0/1, variables A and B increment
    /// in opposite toggle phases:
    ///   A' = ite(C=0, A+1, A)   (A increments in phase C=0)
    ///   B' = ite(C=0, B, B+1)   (B increments in phase C=1)
    ///
    /// If initially A=B and C=0, the invariant is:
    ///   (C=0 → A=B) ∧ (C≠0 → A=B+1)
    ///
    /// This solves benchmarks like dillig32 and s_multipl_24 that require
    /// phase-dependent equality between alternating counters.
    pub(in crate::pdr::solver) fn discover_toggle_conditional_equality_invariants(&mut self) {
        let predicates: Vec<_> = self.problem.predicates().to_vec();
        let mut candidates: Vec<(PredicateId, ChcExpr)> = Vec::new();

        for pred in &predicates {
            if !self.predicate_has_facts(pred.id) {
                continue;
            }

            let canonical_vars = match self.canonical_vars(pred.id) {
                Some(v) => v.to_vec(),
                None => continue,
            };

            let init_values = self.get_init_values(pred.id);

            let self_loop_clauses: Vec<_> = self
                .problem
                .clauses_defining(pred.id)
                .filter(|clause| {
                    if clause.body.predicates.len() != 1 {
                        return false;
                    }
                    let (body_pred, _) = &clause.body.predicates[0];
                    if *body_pred != pred.id {
                        return false;
                    }
                    let head_args = match &clause.head {
                        crate::ClauseHead::Predicate(_, a) => a,
                        crate::ClauseHead::False => return false,
                    };
                    head_args.len() == canonical_vars.len()
                })
                .collect();

            // === Case 1: Single clause with ITE ===
            if self_loop_clauses.len() == 1 {
                let clause = &self_loop_clauses[0];
                let body_args = &clause.body.predicates[0].1;
                let head_args = match &clause.head {
                    crate::ClauseHead::Predicate(_, a) => a.as_slice(),
                    _ => continue,
                };
                if body_args.len() != canonical_vars.len() {
                    continue;
                }

                let mut toggle_indices: Vec<usize> = Vec::new();
                for (idx, _) in canonical_vars.iter().enumerate() {
                    if Self::is_toggle_ite(&body_args[idx], &head_args[idx]) {
                        toggle_indices.push(idx);
                    }
                }

                for &toggle_idx in &toggle_indices {
                    let toggle_body = &body_args[toggle_idx];
                    let mut phase0_inc: Vec<usize> = Vec::new();
                    let mut phase1_inc: Vec<usize> = Vec::new();

                    for (idx, var) in canonical_vars.iter().enumerate() {
                        if idx == toggle_idx || !matches!(var.sort, ChcSort::Int) {
                            continue;
                        }
                        match Self::classify_toggle_conditional_increment(
                            toggle_body,
                            &body_args[idx],
                            &head_args[idx],
                        ) {
                            Some(0) => phase0_inc.push(idx),
                            Some(1) => phase1_inc.push(idx),
                            _ => {}
                        }
                    }

                    Self::generate_toggle_eq_candidates(
                        &canonical_vars,
                        &init_values,
                        toggle_idx,
                        &phase0_inc,
                        &phase1_inc,
                        pred.id,
                        self.config.verbose,
                        false,
                        &mut candidates,
                    );
                }
            }

            // === Case 2: Split clauses (ITE decomposed) ===
            // When ITE is split, each clause has constant toggle values.
            // Detect toggle by finding a var index where head values are
            // {0, 1} across clauses, then check for conditional increments.
            if self.config.verbose && self_loop_clauses.len() >= 2 {
                safe_eprintln!(
                    "PDR: toggle_cond_eq Case2: pred {} has {} self-loop clauses, {} canonical vars",
                    pred.id.index(), self_loop_clauses.len(), canonical_vars.len(),
                );
                for (ci, clause) in self_loop_clauses.iter().enumerate() {
                    let head_args = match &clause.head {
                        crate::ClauseHead::Predicate(_, a) => a.as_slice(),
                        _ => continue,
                    };
                    let body_args = &clause.body.predicates[0].1;
                    safe_eprintln!(
                        "PDR:   clause {}: head_args=[{}], body_args=[{}]",
                        ci,
                        head_args
                            .iter()
                            .map(|a| format!("{}", a))
                            .collect::<Vec<_>>()
                            .join(", "),
                        body_args
                            .iter()
                            .map(|a| format!("{}", a))
                            .collect::<Vec<_>>()
                            .join(", "),
                    );
                }
            }
            if self_loop_clauses.len() == 2 {
                for (toggle_idx, toggle_var) in canonical_vars.iter().enumerate() {
                    if !matches!(toggle_var.sort, ChcSort::Int) {
                        continue;
                    }

                    // Check if this var has constant {0, 1} head values across clauses
                    let mut head_consts: Vec<Option<i128>> = Vec::new();
                    for clause in &self_loop_clauses {
                        let head_args = match &clause.head {
                            crate::ClauseHead::Predicate(_, a) => a.as_slice(),
                            _ => break,
                        };
                        match &head_args[toggle_idx] {
                            ChcExpr::Int(v) if *v == 0 || *v == 1 => head_consts.push(Some(*v)),
                            _ => head_consts.push(None),
                        }
                    }

                    if head_consts.len() != 2
                        || head_consts.iter().any(|c| c.is_none())
                        || head_consts[0] == head_consts[1]
                    {
                        continue;
                    }

                    // This is a toggle. Determine which clause corresponds to phase 0.
                    // In clause where toggle_head=1, the toggle was 0 before (phase 0).
                    // In clause where toggle_head=0, the toggle was 1 before (phase 1).
                    let phase0_clause_idx = if head_consts[0] == Some(1) { 0 } else { 1 };
                    let phase1_clause_idx = 1 - phase0_clause_idx;

                    let mut phase0_inc: Vec<usize> = Vec::new();
                    let mut phase1_inc: Vec<usize> = Vec::new();

                    for (idx, var) in canonical_vars.iter().enumerate() {
                        if idx == toggle_idx || !matches!(var.sort, ChcSort::Int) {
                            continue;
                        }

                        // Check offset in each phase
                        let p0_clause = &self_loop_clauses[phase0_clause_idx];
                        let p1_clause = &self_loop_clauses[phase1_clause_idx];

                        let p0_body = &p0_clause.body.predicates[0].1[idx];
                        let p0_head = match &p0_clause.head {
                            crate::ClauseHead::Predicate(_, a) => &a[idx],
                            _ => continue,
                        };
                        let p1_body = &p1_clause.body.predicates[0].1[idx];
                        let p1_head = match &p1_clause.head {
                            crate::ClauseHead::Predicate(_, a) => &a[idx],
                            _ => continue,
                        };

                        let offset_phase0 = Self::extract_simple_offset(p0_body, p0_head)
                            .or_else(|| if p0_head == p0_body { Some(0) } else { None })
                            .or_else(|| {
                                // Resolve through constraint equalities (split-clause head vars are fresh)
                                if let (ChcExpr::Var(pre_v), ChcExpr::Var(post_v)) =
                                    (p0_body, p0_head)
                                {
                                    p0_clause.body.constraint.as_ref().and_then(|c| {
                                        Self::find_offset_in_constraint(
                                            c,
                                            &pre_v.name,
                                            &post_v.name,
                                        )
                                    })
                                } else {
                                    None
                                }
                            });
                        let offset_phase1 = Self::extract_simple_offset(p1_body, p1_head)
                            .or_else(|| if p1_head == p1_body { Some(0) } else { None })
                            .or_else(|| {
                                if let (ChcExpr::Var(pre_v), ChcExpr::Var(post_v)) =
                                    (p1_body, p1_head)
                                {
                                    p1_clause.body.constraint.as_ref().and_then(|c| {
                                        Self::find_offset_in_constraint(
                                            c,
                                            &pre_v.name,
                                            &post_v.name,
                                        )
                                    })
                                } else {
                                    None
                                }
                            });

                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: toggle_cond_eq: toggle_idx={} idx={} offset_phase0={:?} offset_phase1={:?}",
                                toggle_idx, idx, offset_phase0, offset_phase1,
                            );
                        }

                        match (offset_phase0, offset_phase1) {
                            (Some(1), Some(0)) => phase0_inc.push(idx),
                            (Some(0), Some(1)) => phase1_inc.push(idx),
                            _ => {}
                        }
                    }

                    let toggle_bounds = init_values.get(&toggle_var.name);
                    let toggle_init =
                        toggle_bounds.and_then(|b| if b.min == b.max { Some(b.min) } else { None });

                    // Also handle disjunctive toggle: min=0, max=1 means {0, 1}
                    let toggle_disjunctive = toggle_bounds
                        .map(|b| b.min == 0 && b.max == 1)
                        .unwrap_or(false);

                    if toggle_init.is_none() && !toggle_disjunctive {
                        continue;
                    }

                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: toggle_cond_eq: pred {} toggle_idx={} phase0_inc={:?} phase1_inc={:?} toggle_init={:?} disjunctive={} init_keys={:?}",
                            pred.id.index(), toggle_idx, phase0_inc, phase1_inc, toggle_init, toggle_disjunctive,
                            init_values.keys().collect::<Vec<_>>(),
                        );
                    }

                    Self::generate_toggle_eq_candidates(
                        &canonical_vars,
                        &init_values,
                        toggle_idx,
                        &phase0_inc,
                        &phase1_inc,
                        pred.id,
                        self.config.verbose,
                        toggle_disjunctive,
                        &mut candidates,
                    );
                }
            }
        }

        for (pred_id, formula) in candidates {
            self.add_discovered_invariant_algebraic(pred_id, formula, 1);
        }
    }

    /// Generate toggle-conditional equality candidate invariants for a toggle
    /// variable with phase-0 and phase-1 increment variable sets.
    ///
    /// When `toggle_disjunctive` is true, the toggle starts at {0, 1} (unknown).
    /// In that case, we emit candidates for both possible starting values and
    /// let the validation/inductiveness check filter invalid ones.
    fn generate_toggle_eq_candidates(
        canonical_vars: &[ChcVar],
        init_values: &ay_core::kani_compat::DetHashMap<String, crate::pdr::config::InitIntBounds>,
        toggle_idx: usize,
        phase0_inc: &[usize],
        phase1_inc: &[usize],
        pred_id: PredicateId,
        verbose: bool,
        toggle_disjunctive: bool,
        candidates: &mut Vec<(PredicateId, ChcExpr)>,
    ) {
        if phase0_inc.is_empty() || phase1_inc.is_empty() {
            return;
        }

        let toggle_var = &canonical_vars[toggle_idx];
        let toggle_init = init_values.get(&toggle_var.name).and_then(|b| {
            if b.min == b.max {
                Some(b.min)
            } else {
                None
            }
        });

        let make_eq_with_offset = |a: ChcExpr, b: ChcExpr, offset: i128| -> ChcExpr {
            if offset == 0 {
                ChcExpr::eq(a, b)
            } else {
                ChcExpr::eq(a, ChcExpr::add(b, ChcExpr::Int(offset)))
            }
        };

        let build_invariant = |toggle_expr: &ChcExpr,
                               p0_expr: &ChcExpr,
                               p1_expr: &ChcExpr,
                               eq_at_0: i128,
                               eq_at_1: i128|
         -> ChcExpr {
            ChcExpr::and(
                ChcExpr::or(
                    ChcExpr::not(ChcExpr::eq(toggle_expr.clone(), ChcExpr::Int(0))),
                    make_eq_with_offset(p0_expr.clone(), p1_expr.clone(), eq_at_0),
                ),
                ChcExpr::or(
                    ChcExpr::eq(toggle_expr.clone(), ChcExpr::Int(0)),
                    make_eq_with_offset(p0_expr.clone(), p1_expr.clone(), eq_at_1),
                ),
            )
        };

        for &p0_idx in phase0_inc {
            for &p1_idx in phase1_inc {
                let p0_var = &canonical_vars[p0_idx];
                let p1_var = &canonical_vars[p1_idx];

                let p0_init = init_values.get(&p0_var.name).and_then(|b| {
                    if b.min == b.max {
                        Some(b.min)
                    } else {
                        None
                    }
                });
                let p1_init = init_values.get(&p1_var.name).and_then(|b| {
                    if b.min == b.max {
                        Some(b.min)
                    } else {
                        None
                    }
                });

                // Determine init_offset between the two counters.
                // If both have exact init values, use the difference.
                // If neither has init values (common when they're constrained equal),
                // assume init_offset=0 (i.e., they start equal).
                let init_offset = match (p0_init, p1_init) {
                    (Some(p0_v), Some(p1_v)) => p0_v - p1_v,
                    (None, None) => 0, // assume init-equal (validated later)
                    _ => continue,     // one known, one unknown — skip
                };

                let p0_expr = ChcExpr::var(p0_var.clone());
                let p1_expr = ChcExpr::var(p1_var.clone());
                let toggle_expr = ChcExpr::var(toggle_var.clone());

                // Determine toggle-conditional offsets.
                // When toggle=0 at init and p0 increments in phase 0:
                //   eq_at_0 = init_offset, eq_at_1 = init_offset + 1
                // When toggle=1 at init:
                //   eq_at_0 = init_offset - 1, eq_at_1 = init_offset
                if toggle_disjunctive {
                    // Emit candidates for BOTH toggle init values.
                    // The inductiveness check will filter invalid ones.
                    for &ti in &[0i128, 1] {
                        let (eq_at_0, eq_at_1) = if ti == 0 {
                            (init_offset, init_offset + 1)
                        } else {
                            (init_offset - 1, init_offset)
                        };

                        let inv =
                            build_invariant(&toggle_expr, &p0_expr, &p1_expr, eq_at_0, eq_at_1);

                        if verbose {
                            safe_eprintln!(
                                "PDR: Discovered toggle-conditional equality for pred {} (disjunctive ti={}): \
                                 toggle={}, {} vs {} (phase0_offset={}, phase1_offset={})",
                                pred_id.index(), ti, toggle_var.name, p0_var.name, p1_var.name,
                                eq_at_0, eq_at_1,
                            );
                        }

                        candidates.push((pred_id, inv));
                    }
                } else {
                    let (eq_at_0, eq_at_1) = if toggle_init == Some(0) {
                        (init_offset, init_offset + 1)
                    } else if toggle_init == Some(1) {
                        (init_offset - 1, init_offset)
                    } else {
                        (init_offset, init_offset + 1)
                    };

                    let inv = build_invariant(&toggle_expr, &p0_expr, &p1_expr, eq_at_0, eq_at_1);

                    if verbose {
                        safe_eprintln!(
                            "PDR: Discovered toggle-conditional equality for pred {}: \
                             toggle={}, {} vs {} (phase0_offset={}, phase1_offset={})",
                            pred_id.index(),
                            toggle_var.name,
                            p0_var.name,
                            p1_var.name,
                            eq_at_0,
                            eq_at_1,
                        );
                    }

                    candidates.push((pred_id, inv));
                }
            }
        }
    }

    /// Classify a toggle-conditional increment.
    ///
    /// Returns:
    /// - `Some(0)` if `head = ite(toggle=0, body+1, body)` (increments in phase 0)
    /// - `Some(1)` if `head = ite(toggle=0, body, body+1)` (increments in phase 1)
    /// - `None` otherwise
    fn classify_toggle_conditional_increment(
        toggle_body: &ChcExpr,
        body_val: &ChcExpr,
        head_val: &ChcExpr,
    ) -> Option<i128> {
        let ChcExpr::Op(ChcOp::Ite, args) = head_val else {
            return None;
        };
        if args.len() != 3 {
            return None;
        }
        let cond = &args[0];
        let then_br = &args[1];
        let else_br = &args[2];

        // Condition must be toggle=0 or toggle=1
        let (is_eq_zero, is_eq_one) = (
            Self::is_eq_var_const(cond, toggle_body, 0),
            Self::is_eq_var_const(cond, toggle_body, 1),
        );

        if !is_eq_zero && !is_eq_one {
            return None;
        }

        let then_offset = Self::extract_simple_offset(body_val, then_br);
        let else_offset = Self::extract_simple_offset(body_val, else_br);
        let then_is_self = then_br.as_ref() == body_val;
        let else_is_self = else_br.as_ref() == body_val;

        if is_eq_zero {
            // ite(toggle=0, then, else)
            if then_offset == Some(1) && (else_is_self || else_offset == Some(0)) {
                return Some(0); // increments in phase 0
            }
            if (then_is_self || then_offset == Some(0)) && else_offset == Some(1) {
                return Some(1); // increments in phase 1
            }
        } else {
            // ite(toggle=1, then, else)
            if then_offset == Some(1) && (else_is_self || else_offset == Some(0)) {
                return Some(1); // increments in phase 1
            }
            if (then_is_self || then_offset == Some(0)) && else_offset == Some(1) {
                return Some(0); // increments in phase 0
            }
        }

        None
    }

    /// Check if head_val is a toggle of body_val: ite(body_val = 0, 1, 0)
    /// or ite(body_val = 1, 0, 1) — i.e., head = 1 - body when body in {0, 1}.
    fn is_toggle_ite(body_val: &ChcExpr, head_val: &ChcExpr) -> bool {
        if let ChcExpr::Op(ChcOp::Ite, args) = head_val {
            if args.len() != 3 {
                return false;
            }
            let cond = &args[0];
            let then_br = &args[1];
            let else_br = &args[2];

            if Self::is_eq_var_const(cond, body_val, 0)
                && Self::is_int_const(then_br, 1)
                && Self::is_int_const(else_br, 0)
            {
                return true;
            }
            if Self::is_eq_var_const(cond, body_val, 1)
                && Self::is_int_const(then_br, 0)
                && Self::is_int_const(else_br, 1)
            {
                return true;
            }
            if let (ChcExpr::Int(t), ChcExpr::Int(e)) = (then_br.as_ref(), else_br.as_ref()) {
                if (*t == 0 || *t == 1) && (*e == 0 || *e == 1) && *t != *e {
                    if Self::is_eq_var_const(cond, body_val, *e) {
                        return true;
                    }
                }
            }
        }
        false
    }

    fn is_eq_var_const(expr: &ChcExpr, target: &ChcExpr, c: i128) -> bool {
        if let ChcExpr::Op(ChcOp::Eq, args) = expr {
            if args.len() == 2 {
                if args[0].as_ref() == target && Self::is_int_const(&args[1], c) {
                    return true;
                }
                if args[1].as_ref() == target && Self::is_int_const(&args[0], c) {
                    return true;
                }
            }
        }
        false
    }

    fn is_int_const(expr: &ChcExpr, c: i128) -> bool {
        matches!(expr, ChcExpr::Int(n) if *n == c)
    }

    /// Extract simple offset: if head = body + c, return Some(c).
    pub(in crate::pdr::solver) fn extract_simple_offset(
        body_val: &ChcExpr,
        head_val: &ChcExpr,
    ) -> Option<i128> {
        if let ChcExpr::Op(ChcOp::Add, args) = head_val {
            if args.len() == 2 {
                if args[0].as_ref() == body_val {
                    if let ChcExpr::Int(c) = args[1].as_ref() {
                        return Some(*c);
                    }
                }
                if args[1].as_ref() == body_val {
                    if let ChcExpr::Int(c) = args[0].as_ref() {
                        return Some(*c);
                    }
                }
            }
        }
        None
    }

    fn find_toggle_in_constraint(constraint: &ChcExpr, pre_var: &str, post_var: &str) -> bool {
        match constraint {
            ChcExpr::Op(ChcOp::And, args) => args
                .iter()
                .any(|a| Self::find_toggle_in_constraint(a, pre_var, post_var)),
            ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
                let (lhs, rhs) = (&args[0], &args[1]);
                (Self::is_var_named(lhs, post_var) && Self::is_toggle_ite_named(rhs, pre_var))
                    || (Self::is_var_named(rhs, post_var)
                        && Self::is_toggle_ite_named(lhs, pre_var))
            }
            _ => false,
        }
    }

    fn is_var_named(expr: &ChcExpr, name: &str) -> bool {
        matches!(expr, ChcExpr::Var(v) if v.name == name)
    }

    fn is_toggle_ite_named(expr: &ChcExpr, var_name: &str) -> bool {
        let ChcExpr::Op(ChcOp::Ite, args) = expr else {
            return false;
        };
        if args.len() != 3 {
            return false;
        }
        let ChcExpr::Op(ChcOp::Eq, eq_args) = args[0].as_ref() else {
            return false;
        };
        if eq_args.len() != 2 {
            return false;
        }
        let has_var =
            Self::is_var_named(&eq_args[0], var_name) || Self::is_var_named(&eq_args[1], var_name);
        if !has_var {
            return false;
        }
        let cond_const = if Self::is_var_named(&eq_args[0], var_name) {
            eq_args[1].as_ref()
        } else {
            eq_args[0].as_ref()
        };
        if let (ChcExpr::Int(c), ChcExpr::Int(t), ChcExpr::Int(e)) =
            (cond_const, args[1].as_ref(), args[2].as_ref())
        {
            (*t == 0 || *t == 1) && (*e == 0 || *e == 1) && *t != *e && *c == *e
        } else {
            false
        }
    }
}
