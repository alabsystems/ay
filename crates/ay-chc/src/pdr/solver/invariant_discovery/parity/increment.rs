// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl PdrSolver {
    /// Discover modular invariants from constant-increment self-loop transitions. (#1362)
    ///
    /// If variable v has transition v' = v + c (constant increment, |c| >= 2) and
    /// init value v0, then `(mod v |c|) = (v0 mod |c|)` is always preserved —
    /// BUT only if ALL self-loop transitions for the predicate also preserve the
    /// same modular invariant.
    ///
    /// Captures: inner loop counters like "C starts at 0, increments by 2"
    /// → (mod C 2) = 0. Complements toggle-parity (which handles |c|=odd only).
    ///
    /// SOUNDNESS FIX: Previously examined each clause in isolation. A predicate
    /// with two self-loops (e.g., x'=x+1 when x<5, x'=x+10 when x>=5) would
    /// generate (mod x 10)=0 from the second clause alone, ignoring that the
    /// first clause increments by 1 and breaks the invariant.
    pub(in crate::pdr::solver) fn discover_increment_divisibility_invariants(&mut self) {
        let predicates: Vec<_> = self.problem.predicates().to_vec();
        let mut candidates: Vec<(PredicateId, ChcExpr)> = Vec::new();

        for pred in &predicates {
            let canonical_vars = match self.canonical_vars(pred.id) {
                Some(v) => v.to_vec(),
                None => continue,
            };

            let init_values = self.get_init_values(pred.id);

            // Phase 1: Collect all self-loop increments per variable.
            // Key: (var_idx) -> Vec<increment>
            let mut var_increments: ay_core::kani_compat::DetHashMap<usize, Vec<i128>> =
                Default::default();

            for clause in self.problem.clauses_defining(pred.id) {
                // Only self-loop transitions
                if clause.body.predicates.len() != 1 {
                    continue;
                }
                let (body_pred, body_args) = &clause.body.predicates[0];
                if *body_pred != pred.id {
                    continue;
                }
                let head_args = match &clause.head {
                    crate::ClauseHead::Predicate(_, a) => a.as_slice(),
                    crate::ClauseHead::False => continue,
                };
                if head_args.len() != canonical_vars.len()
                    || body_args.len() != canonical_vars.len()
                {
                    continue;
                }

                for (idx, var) in canonical_vars.iter().enumerate() {
                    if !matches!(var.sort, ChcSort::Int) {
                        continue;
                    }

                    let body_val = &body_args[idx];
                    let head_val = &head_args[idx];

                    // Extract the constant increment for this transition
                    let increment = match Self::extract_simple_offset(body_val, head_val) {
                        Some(c) => c,
                        None => {
                            // Fallback: resolve through constraint
                            if let (ChcExpr::Var(body_v), ChcExpr::Var(head_v)) =
                                (body_val, head_val)
                            {
                                if head_v.name == body_v.name {
                                    // Identity: increment 0
                                    var_increments.entry(idx).or_default().push(0);
                                    continue;
                                }
                                match clause
                                    .body
                                    .constraint
                                    .as_ref()
                                    .and_then(|c| Self::find_equality_rhs(c, &head_v.name))
                                    .and_then(|rhs| {
                                        Self::extract_addition_offset(&rhs, &body_v.name)
                                    }) {
                                    Some(c) => c,
                                    None => continue, // Can't extract increment; skip
                                }
                            } else {
                                continue;
                            }
                        }
                    };

                    var_increments.entry(idx).or_default().push(increment);
                }
            }

            // Phase 2: For each variable with at least one |increment| >= 2,
            // compute the GCD of all increments. The modular invariant
            // (var mod gcd = init mod gcd) is valid only if EVERY self-loop
            // increment is divisible by gcd.
            for (idx, increments) in &var_increments {
                if increments.is_empty() {
                    continue;
                }

                // Compute GCD of all absolute increments (including 0, which
                // is divisible by everything).
                let mut g: i128 = 0;
                let mut abs_overflow = false;
                for &inc in increments {
                    // checked_abs: i128::MIN has no absolute value; skip the
                    // variable rather than wrapping.
                    let Some(abs_inc) = inc.checked_abs() else {
                        abs_overflow = true;
                        break;
                    };
                    g = Self::gcd_i128(g, abs_inc);
                }

                // Need GCD >= 2 for a non-trivial modular invariant
                if abs_overflow || g < 2 {
                    continue;
                }

                let var = &canonical_vars[*idx];

                // Get init value for this variable
                let init_val = match init_values.get(&var.name) {
                    Some(bounds) if bounds.min == bounds.max => bounds.min,
                    _ => continue,
                };

                let remainder = ((init_val % g) + g) % g;

                let invariant = ChcExpr::eq(
                    ChcExpr::mod_op(ChcExpr::var(var.clone()), ChcExpr::Int(g)),
                    ChcExpr::Int(remainder),
                );

                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: Discovered increment-divisibility invariant for pred {}: \
                         ({} mod {}) = {} (increments={:?}, init={})",
                        pred.id.index(),
                        var.name,
                        g,
                        remainder,
                        increments,
                        init_val,
                    );
                }

                candidates.push((pred.id, invariant));
            }
        }

        for (pred_id, formula) in candidates {
            self.add_discovered_invariant_algebraic(pred_id, formula, 1);
        }
    }

    /// Compute GCD of two non-negative integers.
    fn gcd_i128(a: i128, b: i128) -> i128 {
        debug_assert!(a >= 0 && b >= 0, "gcd_i128 requires non-negative inputs");
        let (mut a, mut b) = (a, b);
        while b != 0 {
            let t = b;
            b = a % b;
            a = t;
        }
        a
    }

    /// Discover parity invariants from nondeterministic disjunctive transitions
    /// where every branch preserves an arithmetic parity structure. (#1362)
    ///
    /// Pattern: A self-loop transition has a disjunctive constraint
    /// `(branch_1 OR branch_2 OR ...)` where each branch changes the SAME set of
    /// K variables by the same magnitude ±c. Then the sum of those K variables
    /// changes by ±(K*c) per step. If K*c is even, the sum's parity is preserved.
    ///
    /// For accumulators defined as `F = C + expr(post_vars)`, if the post-value
    /// sum has preserved parity, then C's parity is also preserved.
    ///
    /// Example: s_mutants_22 has `(or (and D=A+1 E=B+1) (and D=A-1 E=B-1))` with
    /// `F=C+D+E`. K=2 vars (A,B) change by ±1, K*c=2 (even), so A+B parity is
    /// preserved. Since F-C = D+E = (A±1)+(B±1) = A+B±2, and A+B is even,
    /// F-C is even, so C's parity (starting from 2*A, even) is preserved.
    pub(in crate::pdr::solver) fn discover_branch_accumulator_parity_invariants(&mut self) {
        let predicates: Vec<_> = self.problem.predicates().to_vec();
        let mut candidates: Vec<(PredicateId, ChcExpr)> = Vec::new();

        for pred in &predicates {
            let canonical_vars = match self.canonical_vars(pred.id) {
                Some(v) => v.to_vec(),
                None => continue,
            };

            let init_values = self.get_init_values(pred.id);

            for clause in self.problem.clauses_defining(pred.id) {
                // Only self-loop transitions with exactly one body predicate
                if clause.body.predicates.len() != 1 {
                    continue;
                }
                let (body_pred, body_args) = &clause.body.predicates[0];
                if *body_pred != pred.id {
                    continue;
                }
                let head_args = match &clause.head {
                    crate::ClauseHead::Predicate(_, a) => a.as_slice(),
                    crate::ClauseHead::False => continue,
                };
                if head_args.len() != canonical_vars.len()
                    || body_args.len() != canonical_vars.len()
                {
                    continue;
                }

                let Some(constraint) = clause.body.constraint.as_ref() else {
                    continue;
                };

                // Decompose constraint into conjuncts and find the Or
                let mut conjuncts = Vec::new();
                constraint.collect_conjuncts_into(&mut conjuncts);

                let mut or_branches: Option<Vec<ChcExpr>> = None;
                let mut non_or_conjuncts: Vec<ChcExpr> = Vec::new();

                for conj in &conjuncts {
                    if let ChcExpr::Op(ChcOp::Or, args) = conj {
                        if or_branches.is_none() {
                            let mut branches = Vec::new();
                            for a in args {
                                match a.as_ref() {
                                    ChcExpr::Op(ChcOp::Or, nested) => {
                                        for n in nested {
                                            branches.push(n.as_ref().clone());
                                        }
                                    }
                                    other => branches.push(other.clone()),
                                }
                            }
                            or_branches = Some(branches);
                        }
                    } else {
                        non_or_conjuncts.push(conj.clone());
                    }
                }

                let Some(branches) = or_branches else {
                    continue; // No disjunction found
                };
                if branches.len() < 2 {
                    continue;
                }

                // For each branch, extract variable assignments: var_name -> expression
                let mut branch_assignments: Vec<ay_core::kani_compat::DetHashMap<String, ChcExpr>> =
                    Vec::new();
                let mut valid = true;

                for branch in &branches {
                    let mut assigns: ay_core::kani_compat::DetHashMap<String, ChcExpr> =
                        Default::default();
                    let mut branch_conjuncts = Vec::new();
                    branch.collect_conjuncts_into(&mut branch_conjuncts);

                    for bc in &branch_conjuncts {
                        if let ChcExpr::Op(ChcOp::Eq, args) = bc {
                            if args.len() == 2 {
                                if let ChcExpr::Var(v) = args[0].as_ref() {
                                    assigns.insert(v.name.clone(), args[1].as_ref().clone());
                                } else if let ChcExpr::Var(v) = args[1].as_ref() {
                                    assigns.insert(v.name.clone(), args[0].as_ref().clone());
                                }
                            }
                        }
                    }
                    if assigns.is_empty() {
                        valid = false;
                        break;
                    }
                    branch_assignments.push(assigns);
                }
                if !valid {
                    continue;
                }

                // For each head arg, determine which body arg it maps to, and compute
                // the per-branch offset. We need to resolve head args through the
                // branch assignments and non-or conjuncts.
                //
                // Build a map: head_var_name -> expression from non-or conjuncts
                let mut non_or_equalities: ay_core::kani_compat::DetHashMap<String, ChcExpr> =
                    Default::default();
                for conj in &non_or_conjuncts {
                    if let ChcExpr::Op(ChcOp::Eq, args) = conj {
                        if args.len() == 2 {
                            if let ChcExpr::Var(v) = args[0].as_ref() {
                                non_or_equalities.insert(v.name.clone(), args[1].as_ref().clone());
                            }
                            if let ChcExpr::Var(v) = args[1].as_ref() {
                                non_or_equalities.insert(v.name.clone(), args[0].as_ref().clone());
                            }
                        }
                    }
                }

                // Identify which canonical var indices have symmetric-increment
                // patterns across all branches. For each head arg that is a variable
                // defined in the branches (like D, E), find the body arg it's
                // offsetting and compute the magnitude.
                //
                // We look for head args mapped to body args with ±c offsets.
                // Track: for each (body_var_idx, magnitude), which canonical var indices
                let mut var_offsets: Vec<Option<(usize, i128)>> = vec![None; canonical_vars.len()];

                for (idx, (head_arg, body_arg)) in
                    head_args.iter().zip(body_args.iter()).enumerate()
                {
                    if !matches!(canonical_vars[idx].sort, ChcSort::Int) {
                        continue;
                    }

                    let head_var_name = match head_arg {
                        ChcExpr::Var(v) => &v.name,
                        _ => continue,
                    };
                    let body_var_name = match body_arg {
                        ChcExpr::Var(v) => &v.name,
                        _ => continue,
                    };

                    // Check if this head var is defined in the branch assignments
                    // with a constant offset from the body var
                    let mut magnitude: Option<i128> = None;
                    let mut all_same_magnitude = true;

                    for assigns in &branch_assignments {
                        let expr = match assigns.get(head_var_name) {
                            Some(e) => e,
                            None => {
                                all_same_magnitude = false;
                                break;
                            }
                        };

                        let offset = Self::extract_addition_offset(expr, body_var_name);
                        match offset {
                            Some(c) => {
                                // checked_abs: i128::MIN has no absolute value;
                                // treat it as a non-uniform increment.
                                let Some(mag) = c.checked_abs() else {
                                    all_same_magnitude = false;
                                    break;
                                };
                                match magnitude {
                                    None => magnitude = Some(mag),
                                    Some(m) if m == mag => {}
                                    _ => {
                                        all_same_magnitude = false;
                                        break;
                                    }
                                }
                            }
                            None => {
                                all_same_magnitude = false;
                                break;
                            }
                        }
                    }

                    if all_same_magnitude {
                        if let Some(mag) = magnitude {
                            if mag > 0 {
                                var_offsets[idx] = Some((idx, mag));
                            }
                        }
                    }
                }

                // Group variables with the same magnitude
                let mut mag_groups: ay_core::kani_compat::DetHashMap<i128, Vec<usize>> =
                    Default::default();
                for (idx, offset) in var_offsets.iter().enumerate() {
                    if let Some((_, mag)) = offset {
                        mag_groups.entry(*mag).or_default().push(idx);
                    }
                }

                for (mag, var_indices) in &mag_groups {
                    let k = var_indices.len() as i128;
                    // Overflow-checked: skip the group instead of wrapping.
                    let Some(total_change) = k.checked_mul(*mag) else {
                        continue;
                    };

                    // If total_change is even, sum parity is preserved
                    if total_change % 2 != 0 {
                        continue;
                    }

                    // Check if we can compute the initial parity of the sum
                    let mut sum_init_parity: Option<i128> = None;
                    for &vi in var_indices {
                        let var = &canonical_vars[vi];
                        let init_p = init_values
                            .get(&var.name)
                            .filter(|b| b.min == b.max)
                            .map(|b| b.min.rem_euclid(2))
                            .or_else(|| {
                                self.get_init_expression_for_var(pred.id, vi)
                                    .and_then(|e| Self::compute_static_init_parity(&e, 2))
                            });
                        match init_p {
                            Some(p) => {
                                sum_init_parity =
                                    Some((sum_init_parity.unwrap_or(0) + p).rem_euclid(2));
                            }
                            None => {
                                sum_init_parity = None;
                                break;
                            }
                        }
                    }

                    // Now check for accumulator variables: head args defined in
                    // non_or_equalities as C + sum_of_branch_defined_vars
                    for (acc_idx, head_arg) in head_args.iter().enumerate() {
                        if !matches!(canonical_vars[acc_idx].sort, ChcSort::Int) {
                            continue;
                        }
                        // Skip variables that are part of the symmetric group
                        if var_indices.contains(&acc_idx) {
                            continue;
                        }

                        let head_var_name = match head_arg {
                            ChcExpr::Var(v) => &v.name,
                            _ => continue,
                        };

                        // Check if this head var is defined as body_var + sum_of_others
                        // in non_or_equalities, e.g. F = C + D + E
                        let acc_expr = match non_or_equalities.get(head_var_name) {
                            Some(e) => e,
                            None => continue,
                        };

                        let body_var_name = match &body_args[acc_idx] {
                            ChcExpr::Var(v) => &v.name,
                            _ => continue,
                        };

                        // Check if acc_expr is body_var + sum_of_branch_vars
                        // i.e., F = C + D + E where C is the body accumulator var,
                        // D and E are the branch-defined head vars
                        if let Some(increment_vars) =
                            Self::extract_additive_increment(acc_expr, body_var_name)
                        {
                            // Check that all increment vars are head vars corresponding
                            // to the symmetric group
                            let branch_head_var_names: Vec<&str> = var_indices
                                .iter()
                                .filter_map(|&vi| match &head_args[vi] {
                                    ChcExpr::Var(v) => Some(v.name.as_str()),
                                    _ => None,
                                })
                                .collect();

                            let all_match = increment_vars.len() == branch_head_var_names.len()
                                && increment_vars
                                    .iter()
                                    .all(|v| branch_head_var_names.contains(&v.as_str()));

                            if !all_match {
                                continue;
                            }

                            // The accumulator increment is the sum of the branch head
                            // vars. Since those vars = body_vars ± c, the increment
                            // is sum(body_vars) ± K*c. If K*c is even AND
                            // sum(body_vars) parity is preserved, then the accumulator
                            // increment parity is preserved.

                            // Compute accumulator init parity
                            let acc_init_p = init_values
                                .get(&canonical_vars[acc_idx].name)
                                .filter(|b| b.min == b.max)
                                .map(|b| b.min.rem_euclid(2))
                                .or_else(|| {
                                    self.get_init_expression_for_var(pred.id, acc_idx)
                                        .and_then(|e| Self::compute_static_init_parity(&e, 2))
                                });

                            let Some(acc_init) = acc_init_p else {
                                continue;
                            };

                            // The accumulator's parity is preserved because:
                            // F = C + D + E, where D+E has the same parity each step
                            // (since D+E = (A±c) + (B±c) = A+B ± 2c, and 2c is even)
                            // So F mod 2 = (C + D + E) mod 2. Since D+E parity is
                            // preserved (= A+B parity = even), and C starts even,
                            // F is always even.
                            //
                            // More precisely: the increment F-C = D+E. We need D+E
                            // to always have even parity. D = A±c, E = B±c, so
                            // D+E = A+B ± 2c. Since sum_init_parity tells us A+B's
                            // parity, and 2c is even, D+E parity = A+B parity.
                            // If A+B parity is known and even (0), then D+E is even,
                            // so the accumulator parity is preserved.
                            let Some(si_parity) = sum_init_parity else {
                                continue;
                            };

                            // D+E parity = (sum of body vars) parity = si_parity
                            // (since each branch adds ±c to each var, and K*c is even,
                            // the sum parity is invariant)
                            //
                            // F = C + (increment with parity si_parity)
                            // F mod 2 = (acc_init + si_parity) mod 2 ... but this
                            // is not right. F's parity depends on C's current parity
                            // plus the increment's parity.
                            //
                            // Actually: if the increment (D+E) always has parity
                            // si_parity, then F mod 2 = C mod 2 + si_parity (mod 2).
                            // For parity to be preserved: we need si_parity = 0
                            // (even), so F mod 2 = C mod 2.
                            if si_parity != 0 {
                                continue; // Increment parity is odd; C's parity flips each step
                            }

                            let acc_var = &canonical_vars[acc_idx];
                            let invariant = ChcExpr::eq(
                                ChcExpr::mod_op(ChcExpr::var(acc_var.clone()), ChcExpr::Int(2)),
                                ChcExpr::Int(acc_init),
                            );

                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: Discovered branch-accumulator parity invariant for pred {}: \
                                     {} mod 2 = {} (symmetric group of {} vars with magnitude {})",
                                    pred.id.index(),
                                    acc_var.name,
                                    acc_init,
                                    k,
                                    mag,
                                );
                            }

                            candidates.push((pred.id, invariant));
                        }
                    }

                    // Also emit the sum-parity invariant for the symmetric group itself
                    if let Some(si_parity) = sum_init_parity {
                        if var_indices.len() >= 2 {
                            // Build sum expression: var0 + var1 + ...
                            let sum_expr = var_indices.iter().fold(None, |acc, &vi| {
                                let var_expr = ChcExpr::var(canonical_vars[vi].clone());
                                match acc {
                                    None => Some(var_expr),
                                    Some(prev) => Some(ChcExpr::add(prev, var_expr)),
                                }
                            });
                            if let Some(sum) = sum_expr {
                                let invariant = ChcExpr::eq(
                                    ChcExpr::mod_op(sum, ChcExpr::Int(2)),
                                    ChcExpr::Int(si_parity),
                                );

                                if self.config.verbose {
                                    let var_names: Vec<&str> = var_indices
                                        .iter()
                                        .map(|&vi| canonical_vars[vi].name.as_str())
                                        .collect();
                                    safe_eprintln!(
                                        "PDR: Discovered symmetric-group sum parity for pred {}: \
                                         ({}) mod 2 = {}",
                                        pred.id.index(),
                                        var_names.join(" + "),
                                        si_parity,
                                    );
                                }

                                candidates.push((pred.id, invariant));
                            }
                        }
                    }
                }
            }
        }

        for (pred_id, formula) in candidates {
            self.add_discovered_invariant_algebraic(pred_id, formula, 1);
        }
    }

    /// Extract additive increment variables from an expression of the form
    /// `base_var + v1 + v2 + ...`. Returns the list of non-base variable names.
    ///
    /// For `(+ C (+ D E))` with base_var="C", returns `Some(["D", "E"])`.
    /// For `(+ C D E)` with base_var="C", returns `Some(["D", "E"])`.
    fn extract_additive_increment(expr: &ChcExpr, base_var_name: &str) -> Option<Vec<String>> {
        // Flatten the addition
        let mut terms = Vec::new();
        Self::flatten_addition(expr, &mut terms);

        // Find and remove the base variable
        let mut found_base = false;
        let mut other_vars = Vec::new();
        for term in &terms {
            if let ChcExpr::Var(v) = term {
                if !found_base && v.name == base_var_name {
                    found_base = true;
                } else {
                    other_vars.push(v.name.clone());
                }
            } else {
                return None; // Non-variable term in addition
            }
        }

        if found_base && !other_vars.is_empty() {
            Some(other_vars)
        } else {
            None
        }
    }

    /// Flatten a nested addition into its leaf terms.
    fn flatten_addition(expr: &ChcExpr, out: &mut Vec<ChcExpr>) {
        match expr {
            ChcExpr::Op(ChcOp::Add, args) => {
                for arg in args {
                    Self::flatten_addition(arg.as_ref(), out);
                }
            }
            other => out.push(other.clone()),
        }
    }

    /// Discover modular invariants for accumulator variables whose increment is
    /// provably zero given sum equalities already in frame[1]. (#8782)
    ///
    /// Pattern: A self-loop has `F = C + D + E` (accumulator), and the sum
    /// equality `A + B = 0` is already in frame[1]. If D and E correspond to
    /// head args at positions where those positions' body args sum to zero
    /// (i.e., `D + E = A + B = 0` after substitution), then C is constant
    /// across the transition. From the init expression (e.g., `C = 10*A`),
    /// we derive `C mod 10 = 0`.
    ///
    /// This is stronger than parity (mod 2) and captures the invariant needed
    /// for benchmarks like s_mutants_21 where C != 78 requires C mod 10 = 0.
    pub(in crate::pdr::solver) fn discover_constant_accumulator_modular_invariants(&mut self) {
        let predicates: Vec<_> = self.problem.predicates().to_vec();
        let mut candidates: Vec<(PredicateId, ChcExpr)> = Vec::new();

        for pred in &predicates {
            let canonical_vars = match self.canonical_vars(pred.id) {
                Some(v) => v.to_vec(),
                None => continue,
            };

            // Collect sum-equality pairs from frame[1] lemmas.
            let mut sum_eq_pairs: Vec<(usize, usize, i128)> = Vec::new();
            if let Some(frame1) = self.frames.get(1) {
                for lemma in &frame1.lemmas {
                    if lemma.predicate != pred.id {
                        continue;
                    }
                    if let Some((i, j, c)) =
                        Self::extract_sum_equality_from_lemma(&lemma.formula, &canonical_vars)
                    {
                        sum_eq_pairs.push((i, j, c));
                    }
                }
            }

            if sum_eq_pairs.is_empty() {
                continue;
            }

            for clause in self.problem.clauses_defining(pred.id) {
                if clause.body.predicates.len() != 1 {
                    continue;
                }
                let (body_pred, body_args) = &clause.body.predicates[0];
                if *body_pred != pred.id {
                    continue;
                }
                let head_args = match &clause.head {
                    crate::ClauseHead::Predicate(_, a) => a.as_slice(),
                    crate::ClauseHead::False => continue,
                };
                if head_args.len() != canonical_vars.len()
                    || body_args.len() != canonical_vars.len()
                {
                    continue;
                }

                let Some(constraint) = clause.body.constraint.as_ref() else {
                    continue;
                };

                let mut conjuncts = Vec::new();
                constraint.collect_conjuncts_into(&mut conjuncts);

                let mut top_equalities: ay_core::kani_compat::DetHashMap<String, ChcExpr> =
                    Default::default();
                for conj in &conjuncts {
                    if let ChcExpr::Op(ChcOp::Eq, args) = conj {
                        if args.len() == 2 {
                            if let ChcExpr::Var(v) = args[0].as_ref() {
                                top_equalities.insert(v.name.clone(), args[1].as_ref().clone());
                            }
                            if let ChcExpr::Var(v) = args[1].as_ref() {
                                top_equalities.insert(v.name.clone(), args[0].as_ref().clone());
                            }
                        }
                    }
                }

                for (acc_idx, head_arg) in head_args.iter().enumerate() {
                    if !matches!(canonical_vars[acc_idx].sort, ChcSort::Int) {
                        continue;
                    }

                    let head_var_name = match head_arg {
                        ChcExpr::Var(v) => &v.name,
                        _ => continue,
                    };

                    let body_var_name = match &body_args[acc_idx] {
                        ChcExpr::Var(v) => &v.name,
                        _ => continue,
                    };

                    let acc_expr = match top_equalities.get(head_var_name) {
                        Some(e) => e,
                        None => continue,
                    };

                    let Some(increment_vars) =
                        Self::extract_additive_increment(acc_expr, body_var_name)
                    else {
                        continue;
                    };

                    let inc_indices: Vec<usize> = increment_vars
                        .iter()
                        .filter_map(|vn| {
                            head_args.iter().position(|ha| match ha {
                                ChcExpr::Var(v) => v.name == *vn,
                                _ => false,
                            })
                        })
                        .collect();

                    if inc_indices.len() != increment_vars.len() || inc_indices.len() != 2 {
                        continue;
                    }

                    let (i0, i1) = (inc_indices[0], inc_indices[1]);

                    let increment_sums_to_zero = sum_eq_pairs.iter().any(|&(si, sj, c)| {
                        c == 0 && ((si == i0 && sj == i1) || (si == i1 && sj == i0))
                    });

                    if !increment_sums_to_zero {
                        continue;
                    }

                    let init_expr = self.get_init_expression_for_var(pred.id, acc_idx);
                    let modulus = init_expr
                        .as_ref()
                        .and_then(|e| Self::extract_modulus_from_init_expr(e));

                    if let Some(k) = modulus {
                        if k >= 2 {
                            let invariant = ChcExpr::eq(
                                ChcExpr::mod_op(
                                    ChcExpr::var(canonical_vars[acc_idx].clone()),
                                    ChcExpr::Int(k),
                                ),
                                ChcExpr::Int(0),
                            );

                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: Discovered constant-accumulator modular invariant \
                                     for pred {}: {} mod {} = 0 (increment vars {:?} sum to \
                                     0 via sum equality)",
                                    pred.id.index(),
                                    canonical_vars[acc_idx].name,
                                    k,
                                    increment_vars,
                                );
                            }

                            candidates.push((pred.id, invariant));
                        }
                    }
                }
            }
        }

        candidates.dedup_by(|a, b| a.0 == b.0 && a.1 == b.1);
        for (pred_id, formula) in candidates {
            self.add_discovered_invariant_algebraic(pred_id, formula, 1);
        }
    }

    /// Extract a sum equality `canonical_vars[i] + canonical_vars[j] = c` from a lemma.
    fn extract_sum_equality_from_lemma(
        formula: &ChcExpr,
        canonical_vars: &[ChcVar],
    ) -> Option<(usize, usize, i128)> {
        if let ChcExpr::Op(ChcOp::Eq, args) = formula {
            if args.len() == 2 {
                return Self::try_match_sum_eq(&args[0], &args[1], canonical_vars)
                    .or_else(|| Self::try_match_sum_eq(&args[1], &args[0], canonical_vars));
            }
        }
        let mut conjuncts = Vec::new();
        formula.collect_conjuncts_into(&mut conjuncts);
        if conjuncts.len() == 2 {
            let mut le_pair: Option<(usize, usize, i128)> = None;
            let mut ge_pair: Option<(usize, usize, i128)> = None;
            for conj in &conjuncts {
                if let ChcExpr::Op(ChcOp::Le, args) = conj {
                    if args.len() == 2 {
                        if let Some((i, j)) = Self::try_match_sum_expr(&args[0], canonical_vars) {
                            if let ChcExpr::Int(c) = args[1].as_ref() {
                                le_pair = Some((i, j, *c));
                            }
                        }
                    }
                }
                if let ChcExpr::Op(ChcOp::Ge, args) = conj {
                    if args.len() == 2 {
                        if let Some((i, j)) = Self::try_match_sum_expr(&args[0], canonical_vars) {
                            if let ChcExpr::Int(c) = args[1].as_ref() {
                                ge_pair = Some((i, j, *c));
                            }
                        }
                    }
                }
            }
            if let (Some((li, lj, lc)), Some((gi, gj, gc))) = (le_pair, ge_pair) {
                if li == gi && lj == gj && lc == gc {
                    return Some((li, lj, lc));
                }
            }
        }
        None
    }

    fn try_match_sum_expr(expr: &ChcExpr, canonical_vars: &[ChcVar]) -> Option<(usize, usize)> {
        if let ChcExpr::Op(ChcOp::Add, args) = expr {
            if args.len() == 2 {
                if let (ChcExpr::Var(v1), ChcExpr::Var(v2)) = (args[0].as_ref(), args[1].as_ref()) {
                    let i = canonical_vars.iter().position(|cv| cv.name == v1.name)?;
                    let j = canonical_vars.iter().position(|cv| cv.name == v2.name)?;
                    return Some((i, j));
                }
            }
        }
        None
    }

    fn try_match_sum_eq(
        lhs: &ChcExpr,
        rhs: &ChcExpr,
        canonical_vars: &[ChcVar],
    ) -> Option<(usize, usize, i128)> {
        if let ChcExpr::Int(c) = rhs {
            if let Some((i, j)) = Self::try_match_sum_expr(lhs, canonical_vars) {
                return Some((i, j, *c));
            }
        }
        None
    }

    /// Extract a modulus from an init expression of the form `k * var`.
    fn extract_modulus_from_init_expr(expr: &ChcExpr) -> Option<i128> {
        match expr {
            ChcExpr::Op(ChcOp::Mul, args) if args.len() == 2 => {
                if let ChcExpr::Int(k) = args[0].as_ref() {
                    if k.abs() >= 2 {
                        return Some(k.abs());
                    }
                }
                if let ChcExpr::Int(k) = args[1].as_ref() {
                    if k.abs() >= 2 {
                        return Some(k.abs());
                    }
                }
                None
            }
            _ => None,
        }
    }
}
