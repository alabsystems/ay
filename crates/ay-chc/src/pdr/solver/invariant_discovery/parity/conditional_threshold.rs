// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl PdrSolver {
    /// Discover conditional parity invariants from threshold-based ITE patterns.
    ///
    /// This captures patterns like:
    /// - B = ite(A >= threshold, A + k, A + 1)
    /// - When A >= threshold, increment preserves A mod k
    /// - At threshold boundary, A mod k has a specific value
    /// - Result: (A >= threshold) => (A mod k = boundary_parity)
    ///
    /// Example: s_split_10 has B = ite(div(A,5) >= 200, A+5, A+1)
    /// - Threshold: A >= 1000 (since div(A,5) >= 200)
    /// - Above threshold: increment is 5, preserves A mod 5
    /// - At threshold: 1000 mod 5 = 0
    /// - Invariant: (A >= 1000) => (A mod 5 = 0)
    pub(in crate::pdr::solver) fn discover_conditional_parity_invariants(&mut self) {
        let predicates: Vec<_> = self.problem.predicates().to_vec();

        for pred in &predicates {
            if !self.predicate_has_facts(pred.id) {
                continue;
            }

            let canonical_vars = match self.canonical_vars(pred.id) {
                Some(v) => v.to_vec(),
                None => continue,
            };

            // Find transition clauses that define this predicate
            // Collect candidates first to avoid borrow conflicts with add_discovered_invariant
            let mut candidates: Vec<(PredicateId, ChcExpr)> = Vec::new();
            for clause in self.problem.clauses_defining(pred.id) {
                // Skip fact clauses
                if clause.body.predicates.is_empty() {
                    continue;
                }

                let head_args = match &clause.head {
                    crate::ClauseHead::Predicate(_, args) => args,
                    crate::ClauseHead::False => continue,
                };

                // Look for ITE patterns in head arguments
                for (arg_idx, head_arg) in head_args.iter().enumerate() {
                    if arg_idx >= canonical_vars.len() {
                        continue;
                    }
                    if !matches!(canonical_vars[arg_idx].sort, ChcSort::Int) {
                        continue;
                    }

                    // Check for ite(cond, then_branch, else_branch) pattern
                    if let ChcExpr::Op(ChcOp::Ite, args) = head_arg {
                        if args.len() != 3 {
                            continue;
                        }

                        let cond = &args[0];
                        let then_branch = &args[1];
                        let _else_branch = &args[2];

                        // Try to extract threshold from div-based condition
                        // Pattern: (<= threshold (div var k)) means var >= threshold * k
                        if let Some((var_name, divisor, threshold)) =
                            Self::extract_div_threshold_condition(cond)
                        {
                            // Check if then_branch is var + k (preserves mod k)
                            // and else_branch is var + 1 (does not preserve mod k)
                            if let Some((then_var, then_inc)) =
                                Self::extract_var_plus_const(then_branch)
                            {
                                if then_var == var_name && then_inc == divisor {
                                    // Increment in then-branch preserves parity
                                    let boundary_value = match threshold.checked_mul(divisor) {
                                        Some(v) => v,
                                        None => continue, // overflow
                                    };
                                    let boundary_parity = boundary_value.rem_euclid(divisor);

                                    // Create the conditional invariant:
                                    // (var >= boundary) => (var mod divisor = boundary_parity)
                                    let canon_var = &canonical_vars[arg_idx];
                                    let condition = ChcExpr::ge(
                                        ChcExpr::var(canon_var.clone()),
                                        ChcExpr::Int(boundary_value),
                                    );
                                    let mod_expr = ChcExpr::mod_op(
                                        ChcExpr::var(canon_var.clone()),
                                        ChcExpr::Int(divisor),
                                    );
                                    let parity_eq =
                                        ChcExpr::eq(mod_expr, ChcExpr::Int(boundary_parity));
                                    // (cond => concl) = (NOT cond) OR concl
                                    let conditional_invariant = ChcExpr::or(
                                        ChcExpr::not(condition.clone()),
                                        parity_eq.clone(),
                                    );

                                    if self.config.verbose {
                                        safe_eprintln!(
                                            "PDR: Discovered conditional parity invariant for pred {}: ({} >= {}) => ({} mod {} = {})",
                                            pred.id.index(),
                                            canon_var.name,
                                            boundary_value,
                                            canon_var.name,
                                            divisor,
                                            boundary_parity
                                        );
                                    }

                                    candidates.push((pred.id, conditional_invariant));
                                }
                            }
                        }
                    }
                }
            }

            // Add candidates outside the borrow
            for (pred_id, formula) in candidates {
                self.add_discovered_invariant(pred_id, formula, 1);
            }
        }
    }

    /// Extract div-based threshold condition from an expression.
    /// Pattern: (<= threshold (div var k)) means var/k >= threshold, i.e., var >= threshold*k
    /// Returns: (var_name, divisor k, threshold value)
    pub(in crate::pdr::solver) fn extract_div_threshold_condition(
        expr: &ChcExpr,
    ) -> Option<(String, i128, i128)> {
        // Pattern: (<= const (div var k)) means div(var, k) >= const
        if let ChcExpr::Op(ChcOp::Le, args) = expr {
            if args.len() != 2 {
                return None;
            }
            // Check for (<= threshold (div var divisor))
            if let (ChcExpr::Int(threshold), ChcExpr::Op(ChcOp::Div, div_args)) =
                (args[0].as_ref(), args[1].as_ref())
            {
                if div_args.len() != 2 {
                    return None;
                }
                if let (ChcExpr::Var(var), ChcExpr::Int(divisor)) =
                    (div_args[0].as_ref(), div_args[1].as_ref())
                {
                    if *divisor > 0 {
                        return Some((var.name.clone(), *divisor, *threshold));
                    }
                }
            }
        }

        // Pattern: (>= (div var k) const) means div(var, k) >= const
        if let ChcExpr::Op(ChcOp::Ge, args) = expr {
            if args.len() != 2 {
                return None;
            }
            if let (ChcExpr::Op(ChcOp::Div, div_args), ChcExpr::Int(threshold)) =
                (args[0].as_ref(), args[1].as_ref())
            {
                if div_args.len() != 2 {
                    return None;
                }
                if let (ChcExpr::Var(var), ChcExpr::Int(divisor)) =
                    (div_args[0].as_ref(), div_args[1].as_ref())
                {
                    if *divisor > 0 {
                        return Some((var.name.clone(), *divisor, *threshold));
                    }
                }
            }
        }

        None
    }

    /// Extract (var + const) pattern from an expression.
    /// Returns (var_name, constant) if pattern matches.
    pub(in crate::pdr::solver) fn extract_var_plus_const(expr: &ChcExpr) -> Option<(String, i128)> {
        // Pattern: (+ var const) or (+ const var)
        if let ChcExpr::Op(ChcOp::Add, args) = expr {
            if args.len() == 2 {
                // Try (+ var const)
                if let (ChcExpr::Var(var), ChcExpr::Int(c)) = (args[0].as_ref(), args[1].as_ref()) {
                    return Some((var.name.clone(), *c));
                }
                // Try (+ const var)
                if let (ChcExpr::Int(c), ChcExpr::Var(var)) = (args[0].as_ref(), args[1].as_ref()) {
                    return Some((var.name.clone(), *c));
                }
            }
        }
        None
    }

    /// Tighten upper bounds using parity invariants.
    ///
    /// When we have both a parity invariant (var % k = c) and an upper bound (var <= n),
    /// we can compute a tighter bound: var <= n - ((n - c) % k)
    ///
    /// For example:
    /// - A % 16 = 0 AND A <= 255 => A <= 240 (since 240 is the largest multiple of 16 <= 255)
    /// - A % 2 = 1 AND A <= 100 => A <= 99 (since 99 is the largest odd number <= 100)
    pub(in crate::pdr::solver) fn tighten_bounds_with_parity(&mut self) {
        if self.frames.len() <= 1 {
            return;
        }

        // Collect current parity invariants and upper bounds from frame 1
        let predicates: Vec<_> = self.problem.predicates().to_vec();
        let mut tightenings: Vec<(PredicateId, ChcVar, i128)> = Vec::new();

        for pred in &predicates {
            let canonical_vars = match self.canonical_vars(pred.id) {
                Some(v) => v.to_vec(),
                None => continue,
            };

            // For each variable, find parity invariants and upper bounds
            for var in &canonical_vars {
                if !matches!(var.sort, ChcSort::Int) {
                    continue;
                }

                // Look for parity invariants: (= (mod var k) c)
                let mut parities: Vec<(i128, i128)> = Vec::new(); // (modulus, remainder)
                for lemma in &self.frames[1].lemmas {
                    if lemma.predicate != pred.id {
                        continue;
                    }

                    // Pattern: (= (mod var k) c)
                    if let ChcExpr::Op(ChcOp::Eq, args) = &lemma.formula {
                        if args.len() == 2 {
                            // Try both orderings: (= (mod var k) c) or (= c (mod var k))
                            let (mod_expr, const_expr) =
                                if matches!(args[0].as_ref(), ChcExpr::Op(ChcOp::Mod, _)) {
                                    (args[0].as_ref(), args[1].as_ref())
                                } else if matches!(args[1].as_ref(), ChcExpr::Op(ChcOp::Mod, _)) {
                                    (args[1].as_ref(), args[0].as_ref())
                                } else {
                                    continue;
                                };

                            if let ChcExpr::Op(ChcOp::Mod, mod_args) = mod_expr {
                                if mod_args.len() == 2 {
                                    if let (ChcExpr::Var(v), ChcExpr::Int(k)) =
                                        (mod_args[0].as_ref(), mod_args[1].as_ref())
                                    {
                                        if v.name == var.name {
                                            if let ChcExpr::Int(c) = const_expr {
                                                parities.push((*k, *c));
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }

                if parities.is_empty() {
                    continue;
                }

                // Look for upper bounds: (le var n) or (<= var n)
                for lemma in &self.frames[1].lemmas {
                    if lemma.predicate != pred.id {
                        continue;
                    }

                    // Pattern: (<= var n) or (le var n)
                    if let ChcExpr::Op(ChcOp::Le, args) = &lemma.formula {
                        if args.len() == 2 {
                            if let (ChcExpr::Var(v), ChcExpr::Int(n)) =
                                (args[0].as_ref(), args[1].as_ref())
                            {
                                if v.name == var.name {
                                    // Try to tighten using each parity constraint
                                    for (k, c) in &parities {
                                        // Tightened bound: n - ((n - c) % k)
                                        // This gives the largest value <= n that satisfies var % k = c
                                        let slack = ((*n - *c) % *k + *k) % *k; // Handle negative remainders
                                        let tightened = *n - slack;
                                        if tightened < *n && tightened >= 0 {
                                            tightenings.push((pred.id, var.clone(), tightened));
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }

        // Add tightened bounds as new lemmas
        for (pred_id, var, tightened_bound) in tightenings {
            let tightened_invariant =
                ChcExpr::le(ChcExpr::var(var.clone()), ChcExpr::Int(tightened_bound));

            // Check if already known
            let already_known = self.frames[1]
                .lemmas
                .iter()
                .any(|l| l.predicate == pred_id && l.formula == tightened_invariant);

            if !already_known {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: Tightened upper bound with parity for pred {}: {} <= {}",
                        pred_id.index(),
                        var.name,
                        tightened_bound
                    );
                }

                self.add_discovered_invariant(pred_id, tightened_invariant, 1);
            }
        }
    }
}
