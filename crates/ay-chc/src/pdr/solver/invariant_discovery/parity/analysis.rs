// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl PdrSolver {
    /// Infer parity for a variable index from incoming cross-predicate transitions.
    /// Returns Some(parity) if all incoming transitions agree on the parity.
    pub(in crate::pdr::solver) fn infer_parity_from_incoming_transitions(
        &self,
        target_pred: PredicateId,
        var_idx: usize,
        k: i128,
        known_parities: &ay_core::kani_compat::DetHashMap<(usize, usize, i128), i128>,
    ) -> Option<i128> {
        let canonical_vars = self.canonical_vars(target_pred)?;
        if var_idx >= canonical_vars.len() {
            return None;
        }

        let mut inferred_parity: Option<i128> = None;
        let mut has_incoming = false;

        // Check all clauses that define target_pred from OTHER predicates
        for clause in self.problem.clauses_defining(target_pred) {
            // Skip fact clauses
            if clause.body.predicates.is_empty() {
                continue;
            }

            let head_args = match &clause.head {
                crate::ClauseHead::Predicate(_, a) => a.as_slice(),
                crate::ClauseHead::False => continue,
            };

            if var_idx >= head_args.len() {
                return None;
            }

            // Get the expression that flows into this variable position
            let head_expr = &head_args[var_idx];

            // Check each body predicate (for cross-predicate transitions)
            for (body_pred, body_args) in &clause.body.predicates {
                if *body_pred == target_pred {
                    continue; // Self-transition, handled elsewhere
                }

                has_incoming = true;

                // Try to determine the parity of head_expr based on body predicate's known parities
                if let Some(parity) =
                    Self::compute_expr_parity(head_expr, body_args, *body_pred, k, known_parities)
                {
                    match inferred_parity {
                        None => inferred_parity = Some(parity),
                        Some(p) if p != parity => return None, // Conflict
                        _ => {}
                    }
                } else if let Some(parity) =
                    Self::compute_static_expr_parity(head_expr, &clause.body.constraint, k)
                {
                    // Fallback: resolve head expression through clause constraint.
                    // Handles cases like head_expr = C where constraint says C = 0.
                    match inferred_parity {
                        None => inferred_parity = Some(parity),
                        Some(p) if p != parity => return None,
                        _ => {}
                    }
                } else {
                    return None; // Can't determine parity
                }
            }
        }

        if has_incoming {
            inferred_parity
        } else {
            None
        }
    }

    /// Compute the parity of an expression given known parities of body predicate variables.
    pub(in crate::pdr::solver) fn compute_expr_parity(
        expr: &ChcExpr,
        body_args: &[ChcExpr],
        body_pred: PredicateId,
        k: i128,
        known_parities: &ay_core::kani_compat::DetHashMap<(usize, usize, i128), i128>,
    ) -> Option<i128> {
        match expr {
            ChcExpr::Int(n) => Some(n.rem_euclid(k)),
            ChcExpr::Var(v) => {
                // Find this variable in body_args
                // #2492: Also search inside expression body args
                for (idx, body_arg) in body_args.iter().enumerate() {
                    let matches = match body_arg {
                        ChcExpr::Var(bv) => bv.name == v.name,
                        expr => expr.vars().iter().any(|bv| bv.name == v.name),
                    };
                    if matches {
                        return known_parities.get(&(body_pred.index(), idx, k)).copied();
                    }
                }
                None
            }
            ChcExpr::Op(op, args) => {
                match op {
                    ChcOp::Add => {
                        // Parity of sum is sum of parities mod k
                        let mut total = 0i128;
                        for arg in args {
                            let p = Self::compute_expr_parity(
                                arg,
                                body_args,
                                body_pred,
                                k,
                                known_parities,
                            )?;
                            total = (total + p).rem_euclid(k);
                        }
                        Some(total)
                    }
                    ChcOp::Mul => {
                        // Parity of product is product of parities mod k (for small k)
                        let mut total = 1i128;
                        for arg in args {
                            let p = Self::compute_expr_parity(
                                arg,
                                body_args,
                                body_pred,
                                k,
                                known_parities,
                            )?;
                            total = (total * p).rem_euclid(k);
                        }
                        Some(total)
                    }
                    ChcOp::Sub if args.len() == 2 => {
                        let p1 = Self::compute_expr_parity(
                            &args[0],
                            body_args,
                            body_pred,
                            k,
                            known_parities,
                        )?;
                        let p2 = Self::compute_expr_parity(
                            &args[1],
                            body_args,
                            body_pred,
                            k,
                            known_parities,
                        )?;
                        Some((p1 - p2).rem_euclid(k))
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// Compute the static parity of a head expression in a cross-predicate transition.
    /// This uses the transition constraint to find equalities and compute fixed parities.
    ///
    /// Returns Some(parity) if the expression has a fixed parity given the constraint.
    pub(in crate::pdr::solver) fn compute_static_expr_parity(
        expr: &ChcExpr,
        constraint: &Option<ChcExpr>,
        k: i128,
    ) -> Option<i128> {
        // First, try to compute static parity directly (no constraint needed)
        if let Some(p) = Self::compute_static_init_parity(expr, k) {
            return Some(p);
        }

        // If the expression contains variables, try to find their values from the constraint
        // For example, if constraint has (= A 16) and expr is A, return 16 mod k
        if let ChcExpr::Var(v) = expr {
            if let Some(c) = constraint {
                if let Some(val) = Self::find_constant_value_in_constraint(c, &v.name) {
                    return Some(val.rem_euclid(k));
                }
            }
        }

        // For additions with some computable parts, we can't determine the total parity
        // unless all parts have known parity
        None
    }

    /// Check if a constraint contains a modulo equality of the form `(= (mod expr k) c)`
    /// This helps determine if we can trust an SMT SAT result for parity checking.
    pub(in crate::pdr::solver) fn constraint_has_mod_equality(
        constraint: &ChcExpr,
        k: i128,
    ) -> bool {
        match constraint {
            ChcExpr::Op(ChcOp::And, args) => {
                args.iter().any(|a| Self::constraint_has_mod_equality(a, k))
            }
            ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
                // Check for (= (mod expr k) c) or (= c (mod expr k))
                let has_mod_k = |e: &ChcExpr| -> bool {
                    if let ChcExpr::Op(ChcOp::Mod, mod_args) = e {
                        if mod_args.len() == 2 {
                            if let ChcExpr::Int(modulus) = mod_args[1].as_ref() {
                                // Check if this modulus is related to k (divisor or multiple)
                                return *modulus == k || k % modulus == 0 || *modulus % k == 0;
                            }
                        }
                    }
                    false
                };
                has_mod_k(&args[0]) || has_mod_k(&args[1])
            }
            _ => false,
        }
    }

    /// Find a constant value for a variable from a constraint like `(= var N)` or `(and (= var N) ...)`
    pub(in crate::pdr::solver) fn find_constant_value_in_constraint(
        constraint: &ChcExpr,
        var_name: &str,
    ) -> Option<i128> {
        match constraint {
            ChcExpr::Op(ChcOp::And, args) => {
                for arg in args {
                    if let Some(val) = Self::find_constant_value_in_constraint(arg, var_name) {
                        return Some(val);
                    }
                }
                None
            }
            ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
                // Check (= var N) or (= N var)
                if let ChcExpr::Var(v) = args[0].as_ref() {
                    if v.name == var_name {
                        if let ChcExpr::Int(n) = args[1].as_ref() {
                            return Some(*n);
                        }
                    }
                }
                if let ChcExpr::Var(v) = args[1].as_ref() {
                    if v.name == var_name {
                        if let ChcExpr::Int(n) = args[0].as_ref() {
                            return Some(*n);
                        }
                    }
                }
                None
            }
            _ => None,
        }
    }

    /// Compute the static parity of an init expression.
    /// For expressions like `2*A` where A is a free variable, this can determine
    /// that the parity is 0 (mod 2) because any integer multiplied by 2 is even.
    ///
    /// Returns Some(parity) if the expression has a fixed parity regardless of
    /// the values of any free variables.
    pub(in crate::pdr::solver) fn compute_static_init_parity(
        expr: &ChcExpr,
        k: i128,
    ) -> Option<i128> {
        match expr {
            ChcExpr::Int(n) => Some(n.rem_euclid(k)),
            ChcExpr::Var(_) => None, // Free variables have unknown parity
            ChcExpr::Op(op, args) => match op {
                ChcOp::Add => {
                    // For add, all terms must have known parity
                    let mut total = 0i128;
                    for arg in args {
                        let p = Self::compute_static_init_parity(arg, k)?;
                        total = (total + p).rem_euclid(k);
                    }
                    Some(total)
                }
                ChcOp::Sub if args.len() == 2 => {
                    let p1 = Self::compute_static_init_parity(&args[0], k)?;
                    let p2 = Self::compute_static_init_parity(&args[1], k)?;
                    Some((p1 - p2).rem_euclid(k))
                }
                ChcOp::Mul => {
                    // For multiplication: if ANY factor is 0 mod k, result is 0 mod k
                    // This handles cases like 2*A where A is unknown but 2 mod 2 = 0
                    let mut has_zero = false;
                    let mut total = 1i128;
                    let mut all_known = true;
                    for arg in args {
                        match Self::compute_static_init_parity(arg, k) {
                            Some(0) => has_zero = true,
                            Some(p) => total = (total * p).rem_euclid(k),
                            None => all_known = false,
                        }
                    }
                    if has_zero {
                        Some(0)
                    } else if all_known {
                        Some(total)
                    } else {
                        None
                    }
                }
                _ => None,
            },
            _ => None,
        }
    }

    /// Get the init expression for a predicate variable from fact clauses.
    /// For `(= D (* 2 A))` where D maps to canonical var, returns `(* 2 A)`.
    pub(in crate::pdr::solver) fn get_init_expression_for_var(
        &self,
        predicate: PredicateId,
        var_idx: usize,
    ) -> Option<ChcExpr> {
        let canonical_vars = self.canonical_vars(predicate)?;
        if var_idx >= canonical_vars.len() {
            return None;
        }

        let mut fallback: Option<ChcExpr> = None;
        for fact in self
            .problem
            .facts()
            .filter(|f| f.head.predicate_id() == Some(predicate))
        {
            let head_args = match &fact.head {
                crate::ClauseHead::Predicate(_, a) => a.as_slice(),
                crate::ClauseHead::False => continue,
            };

            if head_args.len() != canonical_vars.len() {
                continue;
            }

            let head_expr = head_args[var_idx].clone();
            if !matches!(head_expr, ChcExpr::Var(_)) {
                // Direct expression head arg (e.g., (+ x 1)).
                return Some(head_expr);
            }
            if fallback.is_none() {
                fallback = Some(head_expr.clone());
            }

            let Some(constraint) = fact.body.constraint.clone() else {
                continue;
            };
            let fact_var_name = match head_expr {
                ChcExpr::Var(ref v) => v.name.clone(),
                _ => continue,
            };

            // Find equality constraint for this variable
            if let Some(expr) = Self::find_equality_rhs(&constraint, &fact_var_name) {
                return Some(expr);
            }
        }
        fallback
    }

    /// Extract the GCD of all constant increments for a variable across self-transitions.
    ///
    /// For a predicate with self-transitions like `inv(A) ∧ B = A + 23468 → inv(B)`,
    /// this returns `Some(23468)`. If multiple transitions have increments 6 and 10,
    /// returns `Some(gcd(6,10)) = Some(2)`.
    ///
    /// Returns `None` if any self-transition can't be reduced to a constant increment,
    /// or if the GCD is 1 (no useful modulus).
    pub(in crate::pdr::solver) fn extract_transition_increment_gcd(
        &self,
        pred_id: PredicateId,
        var_idx: usize,
    ) -> Option<i128> {
        let mut gcd_val: Option<i128> = None;
        let mut has_self_transitions = false;

        for clause in self.problem.clauses_defining(pred_id) {
            if clause.body.predicates.is_empty() {
                continue;
            }

            let head_args = match &clause.head {
                crate::ClauseHead::Predicate(_, args) => args,
                crate::ClauseHead::False => continue,
            };

            if var_idx >= head_args.len() {
                return None;
            }

            for (body_pred, body_args) in &clause.body.predicates {
                if *body_pred != pred_id {
                    continue; // Only self-transitions
                }
                if var_idx >= body_args.len() {
                    return None;
                }

                has_self_transitions = true;

                let body_var_name = match &body_args[var_idx] {
                    ChcExpr::Var(v) => &v.name,
                    _ => return None,
                };

                // Resolve head expression: if it's a variable, look up its definition
                // in the constraint (e.g., B = A + 23468)
                let head_expr = match &head_args[var_idx] {
                    ChcExpr::Var(v) if v.name == *body_var_name => {
                        continue; // Identity transition, offset = 0
                    }
                    ChcExpr::Var(v) => {
                        if let Some(constraint) = &clause.body.constraint {
                            Self::find_equality_rhs(constraint, &v.name)?
                        } else {
                            return None;
                        }
                    }
                    expr => (*expr).clone(),
                };

                let offset = match Self::extract_addition_offset(&head_expr, body_var_name)
                    .and_then(i128::checked_abs)
                {
                    Some(o) => o,
                    None => return None,
                };

                if offset == 0 {
                    continue;
                }

                gcd_val = Some(match gcd_val {
                    // Both values are non-negative here, so i128 gcd cannot overflow.
                    Some(g) => num_integer::gcd(g, offset),
                    None => offset,
                });
            }
        }

        if has_self_transitions {
            gcd_val.filter(|&g| g > 1)
        } else {
            None
        }
    }

    /// Find the RHS of an equality constraint `var = expr` in a formula.
    pub(in crate::pdr::solver) fn find_equality_rhs(
        formula: &ChcExpr,
        var_name: &str,
    ) -> Option<ChcExpr> {
        match formula {
            ChcExpr::Op(ChcOp::And, args) => {
                for arg in args {
                    if let Some(rhs) = Self::find_equality_rhs(arg, var_name) {
                        return Some(rhs);
                    }
                }
                None
            }
            ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
                if let ChcExpr::Var(v) = args[0].as_ref() {
                    if v.name == var_name {
                        return Some((*args[1]).clone());
                    }
                }
                if let ChcExpr::Var(v) = args[1].as_ref() {
                    if v.name == var_name {
                        return Some((*args[0]).clone());
                    }
                }
                None
            }
            _ => None,
        }
    }
}
