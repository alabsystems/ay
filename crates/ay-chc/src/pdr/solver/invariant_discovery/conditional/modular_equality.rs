// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl PdrSolver {
    /// Discover modular equality invariants proactively before the PDR loop starts.
    ///
    /// For each predicate with fact clauses, finds pairs of integer variables (vi, vj) where:
    /// 1. (vi mod k) = vj at init (where vj is in range [0, k-1])
    /// 2. The modular equality is preserved by all self-transitions
    ///
    /// This captures patterns like: (counter mod 2) = toggle_flag
    /// where counter increments by 1 and toggle_flag alternates between 0 and 1.
    pub(in crate::pdr::solver) fn discover_modular_equality_invariants(&mut self) {
        if self.config.verbose {
            safe_eprintln!("PDR: Searching for modular equality invariants");
        }

        // Wall-clock budget for modular equality discovery (#3121).
        // Each SMT call can take up to 500ms; with O(n^2) variable pairs this
        // can consume multiple seconds. Cap total time to leave budget for the
        // main blocking loop and verify_model.
        const MODULAR_EQ_BUDGET: std::time::Duration = std::time::Duration::from_millis(500);
        let mod_eq_start = ay_core::time::Instant::now();

        let predicates: Vec<_> = self.problem.predicates().to_vec();
        // Only check small moduli - larger ones are unlikely to be useful
        let moduli = [2i128];

        for pred in &predicates {
            // Skip predicates without fact clauses (no initial state)
            if !self.predicate_has_facts(pred.id) {
                continue;
            }

            let canonical_vars = match self.canonical_vars(pred.id) {
                Some(v) => v.to_vec(),
                None => continue,
            };

            // Get initial values for this predicate
            let init_values = self.get_init_values(pred.id);

            // Find pairs where (var_i mod k) = var_j at init
            for i in 0..canonical_vars.len() {
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
                    let init_i = match init_values.get(&var_i.name) {
                        Some(bounds) if bounds.min == bounds.max => bounds.min,
                        _ => continue,
                    };
                    let init_j = match init_values.get(&var_j.name) {
                        Some(bounds) if bounds.min == bounds.max => bounds.min,
                        _ => continue,
                    };

                    for &k in &moduli {
                        // Check if (init_i mod k) = init_j
                        // Also require init_j to be in valid range [0, k-1]
                        if init_j < 0 || init_j >= k {
                            continue;
                        }
                        if init_i.rem_euclid(k) != init_j {
                            continue;
                        }

                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: Testing modular equality ({} mod {}) = {} (init: {} mod {} = {})",
                                var_i.name, k, var_j.name, init_i, k, init_j
                            );
                        }

                        // Budget + cancellation check before expensive SMT (#3121)
                        if self.is_cancelled() || mod_eq_start.elapsed() >= MODULAR_EQ_BUDGET {
                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: modular equality budget exceeded ({:?}), stopping",
                                    mod_eq_start.elapsed()
                                );
                            }
                            return;
                        }

                        // Check if the modular equality is preserved by all transitions
                        if !self.is_modular_equality_preserved_by_transitions(pred.id, i, j, k) {
                            continue;
                        }

                        // Found a valid modular equality invariant! Add it as a lemma.
                        let mod_expr =
                            ChcExpr::mod_op(ChcExpr::var(var_i.clone()), ChcExpr::Int(k));
                        let mod_eq_invariant = ChcExpr::eq(mod_expr, ChcExpr::var(var_j.clone()));

                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: Discovered modular equality invariant for pred {}: ({} mod {}) = {}",
                                pred.id.index(),
                                var_i.name,
                                k,
                                var_j.name
                            );
                        }

                        // Add to frame 1 (not 0, since 0 is for initial constraints).
                        // Use algebraic path since is_modular_equality_preserved_by_transitions
                        // already verified transition preservation. This bypasses the SMT-based
                        // self-inductiveness check which can hang on mod expressions. (#3211)
                        self.add_discovered_invariant_algebraic(pred.id, mod_eq_invariant, 1);
                    }
                }
            }
        }
    }

    /// Check if (var_i mod k) = var_j is preserved by all transitions for a predicate.
    ///
    /// Uses SMT to check that for each transition clause:
    ///   If (body_i mod k) = body_j in pre-state,
    ///   then (head_i mod k) = head_j in post-state.
    pub(in crate::pdr::solver) fn is_modular_equality_preserved_by_transitions(
        &mut self,
        predicate: PredicateId,
        idx_i: usize,
        idx_j: usize,
        k: i128,
    ) -> bool {
        let canonical_vars = match self.canonical_vars(predicate) {
            Some(v) => v.to_vec(),
            None => return false,
        };

        // Track whether we checked at least one self-loop clause (#1388).
        let mut checked_any_self_loop = false;

        // Check all transition clauses that define this predicate
        for clause in self.problem.clauses_defining(predicate) {
            // Skip fact clauses (no body predicates)
            if clause.body.predicates.is_empty() {
                continue;
            }

            let head_args = match &clause.head {
                crate::ClauseHead::Predicate(_, a) => a.as_slice(),
                crate::ClauseHead::False => continue,
            };

            if head_args.len() != canonical_vars.len() {
                return false;
            }

            // Get the head expressions for var_i and var_j (post-state values)
            let head_i_raw = &head_args[idx_i];
            let head_j_raw = &head_args[idx_j];

            // For single-predicate body self-transitions
            if clause.body.predicates.len() != 1 {
                // Hyperedge - be conservative
                return false;
            }

            let (body_pred, body_args) = &clause.body.predicates[0];
            if *body_pred != predicate {
                // Inter-predicate transition: skip, only check self-loops for preservation.
                // If zero self-loops exist, we'll return false at the end (#1388).
                continue;
            }
            if body_args.len() != canonical_vars.len() {
                return false;
            }

            // This is a self-loop clause - mark that we're checking at least one
            checked_any_self_loop = true;

            let body_i = &body_args[idx_i];
            let body_j = &body_args[idx_j];

            // Check: IF (body_i mod k) = body_j THEN (head_i mod k) = head_j
            // Equivalently: (body_i mod k) = body_j AND (head_i mod k) != head_j is UNSAT
            let clause_constraint = clause
                .body
                .constraint
                .clone()
                .unwrap_or(ChcExpr::Bool(true));

            // Substitute head variable definitions from clause constraint (#3211).
            // For clauses like `C = A+1 ∧ D = ite(B=0,1,0) → inv(C,D)`, this
            // replaces Var(C) → A+1 and Var(D) → ite(...), enabling algebraic
            // mod resolution on body variables instead of head variables.
            let (head_i, head_j) = {
                let head_var_names: Vec<&str> = head_args
                    .iter()
                    .filter_map(|a| {
                        if let ChcExpr::Var(v) = a {
                            Some(v.name.as_str())
                        } else {
                            None
                        }
                    })
                    .collect();
                if head_var_names.is_empty() {
                    (head_i_raw.clone(), head_j_raw.clone())
                } else {
                    let mut subst = Vec::new();
                    for conj in clause_constraint.collect_conjuncts() {
                        if let ChcExpr::Op(ChcOp::Eq, ref args) = conj {
                            if args.len() == 2 {
                                if let ChcExpr::Var(v) = args[0].as_ref() {
                                    if head_var_names.contains(&v.name.as_str()) {
                                        subst.push((v.clone(), args[1].as_ref().clone()));
                                    }
                                } else if let ChcExpr::Var(v) = args[1].as_ref() {
                                    if head_var_names.contains(&v.name.as_str()) {
                                        subst.push((v.clone(), args[0].as_ref().clone()));
                                    }
                                }
                            }
                        }
                    }
                    if subst.is_empty() {
                        (head_i_raw.clone(), head_j_raw.clone())
                    } else {
                        (head_i_raw.substitute(&subst), head_j_raw.substitute(&subst))
                    }
                }
            };

            // Case-split on possible remainder values to avoid mod+LIA
            // incompleteness (#3211). The LIA solver can return Unknown on
            // formulas with mod-elimination auxiliary variables (euclidean
            // decomposition creates unbounded quotient variables that cause
            // branch-and-bound to spiral). By grounding body_j to each
            // possible remainder value c ∈ {0, ..., k-1} and propagating
            // constants before check_sat, the formula simplifies enough
            // that the SMT solver handles it directly.
            let mut clause_preserved = true;
            for c in 0..k {
                let post_mod_ne = ChcExpr::ne(
                    ChcExpr::mod_op(head_i.clone(), ChcExpr::Int(k)),
                    head_j.clone(),
                );
                let query = ChcExpr::and_vec(vec![
                    clause_constraint.clone(),
                    ChcExpr::eq(body_j.clone(), ChcExpr::Int(c)),
                    ChcExpr::eq(
                        ChcExpr::mod_op(body_i.clone(), ChcExpr::Int(k)),
                        ChcExpr::Int(c),
                    ),
                    post_mod_ne,
                ]);

                // Propagate constants before check_sat. This resolves
                // body_j = c throughout (including in head_j via clause
                // constraint), and simplifies mod expressions with known
                // operands (e.g., (0 mod 2) = 0 folds to true).
                let query_simplified = query.propagate_constants();

                // Algebraic mod resolution (#1362): after constant propagation,
                // the formula may still contain (var mod k) expressions where
                // we know the residue. For example, if body_i is Var(A) and
                // the formula asserts (A mod 2) = 1, then ((A + 1) mod 2) can
                // be algebraically resolved to (1 + 1) % 2 = 0. The LIA solver
                // often returns Unknown on formulas with multiple mod operations,
                // so resolving them here is critical.
                let query_resolved = if let ChcExpr::Var(bi_var) = body_i {
                    Self::resolve_mod_with_known_residue(&query_simplified, &bi_var.name, k, c)
                        .simplify_constants()
                } else {
                    query_simplified.clone()
                };

                // Early exit: if constant propagation resolved to false,
                // this case is trivially UNSAT (e.g., body_j=1 contradicts
                // clause constraint B=0).
                if matches!(query_resolved, ChcExpr::Bool(false)) {
                    continue;
                }

                self.smt.reset();
                match self
                    .smt
                    .check_sat_with_timeout(&query_resolved, std::time::Duration::from_millis(500))
                {
                    SmtResult::Sat(_) => {
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: Modular equality ({} mod {}) = {} NOT preserved (case c={})",
                                canonical_vars[idx_i].name,
                                k,
                                canonical_vars[idx_j].name,
                                c
                            );
                        }
                        clause_preserved = false;
                        break;
                    }
                    SmtResult::Unsat
                    | SmtResult::UnsatWithCore(_)
                    | SmtResult::UnsatWithFarkas(_) => {
                        // This case is UNSAT - preservation holds for remainder=c
                    }
                    SmtResult::Unknown => {
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: Modular equality ({} mod {}) = {} Unknown (case c={})",
                                canonical_vars[idx_i].name,
                                k,
                                canonical_vars[idx_j].name,
                                c
                            );
                        }
                        clause_preserved = false;
                        break;
                    }
                }
            }
            if !clause_preserved {
                return false;
            }
        }

        // All self-loop transitions preserve the modular equality.
        // But if zero self-loops were checked, cannot claim preservation vacuously (#1388).
        if !checked_any_self_loop {
            return false;
        }
        if self.config.verbose {
            safe_eprintln!(
                "PDR: Modular equality ({} mod {}) = {} is preserved by all transitions",
                canonical_vars[idx_i].name,
                k,
                canonical_vars[idx_j].name
            );
        }
        true
    }

    /// Resolve `(expr mod k)` subexpressions using a known modular residue (#1362).
    ///
    /// Given that `var_name mod k = known_residue`, replaces all occurrences of
    /// `((var_name + offset) mod k)` with the algebraically computed value
    /// `(known_residue + offset) rem_euclid k`. This avoids sending multiple mod
    /// operations to the LIA solver, which often returns Unknown on such formulas.
    ///
    /// Handles patterns:
    /// - `(var mod k)` → `known_residue`
    /// - `((var + offset) mod k)` → `(known_residue + offset) rem_euclid k`
    /// - `(((offset + var) mod k)` → same as above (commutative)
    fn resolve_mod_with_known_residue(
        expr: &ChcExpr,
        var_name: &str,
        k: i128,
        known_residue: i128,
    ) -> ChcExpr {
        Self::resolve_mod_inner(expr, var_name, k, known_residue, 0)
    }

    fn resolve_mod_inner(
        expr: &ChcExpr,
        var_name: &str,
        k: i128,
        known_residue: i128,
        depth: usize,
    ) -> ChcExpr {
        if depth >= 200 {
            return expr.clone();
        }
        match expr {
            ChcExpr::Op(ChcOp::Mod, args) if args.len() == 2 => {
                // Check if this is (something mod k)
                if let ChcExpr::Int(modulus) = args[1].as_ref() {
                    if *modulus == k {
                        // Try to extract the dividend as var_name + offset
                        if let Some(offset) = Self::extract_var_offset(args[0].as_ref(), var_name) {
                            // Algebraically compute the result
                            let result = (known_residue + offset).rem_euclid(k);
                            return ChcExpr::Int(result);
                        }
                    }
                }
                // Can't resolve — recurse into children
                let new_args: Vec<Arc<ChcExpr>> = args
                    .iter()
                    .map(|a| {
                        Arc::new(Self::resolve_mod_inner(
                            a,
                            var_name,
                            k,
                            known_residue,
                            depth + 1,
                        ))
                    })
                    .collect();
                ChcExpr::Op(ChcOp::Mod, new_args)
            }
            ChcExpr::Op(op, args) => {
                let new_args: Vec<Arc<ChcExpr>> = args
                    .iter()
                    .map(|a| {
                        Arc::new(Self::resolve_mod_inner(
                            a,
                            var_name,
                            k,
                            known_residue,
                            depth + 1,
                        ))
                    })
                    .collect();
                ChcExpr::Op(*op, new_args)
            }
            _ => expr.clone(),
        }
    }

    /// Extract the offset from an expression of the form `var + offset` or just `var`.
    ///
    /// Returns `Some(offset)` if `expr` is:
    /// - `Var(var_name)` → offset = 0
    /// - `Add(Var(var_name), Int(offset))` → offset
    /// - `Add(Int(offset), Var(var_name))` → offset
    /// - `Sub(Var(var_name), Int(offset))` → -offset
    /// - `Add(Var(var_name), Neg(Int(offset)))` → -offset
    fn extract_var_offset(expr: &ChcExpr, var_name: &str) -> Option<i128> {
        match expr {
            ChcExpr::Var(v) if v.name == var_name => Some(0),
            ChcExpr::Op(ChcOp::Add, args) if args.len() == 2 => {
                // (var + offset) or (offset + var)
                // Handles Op(Neg,[Int(n)]) via as_i128()
                if let ChcExpr::Var(v) = args[0].as_ref() {
                    if v.name == var_name {
                        return args[1].as_i128();
                    }
                }
                if let ChcExpr::Var(v) = args[1].as_ref() {
                    if v.name == var_name {
                        return args[0].as_i128();
                    }
                }
                None
            }
            ChcExpr::Op(ChcOp::Sub, args) if args.len() == 2 => {
                // (var - offset)
                if let ChcExpr::Var(v) = args[0].as_ref() {
                    if v.name == var_name {
                        return args[1].as_i128().and_then(i128::checked_neg);
                    }
                }
                None
            }
            _ => None,
        }
    }
}
