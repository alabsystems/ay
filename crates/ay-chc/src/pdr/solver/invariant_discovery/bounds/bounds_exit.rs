// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Loop exit bound invariant discovery: exit bounds from self-loop guards,
//! scaled loop exit bounds, and head-argument offset extraction.

use super::*;

impl PdrSolver {
    /// Discover loop exit bounds from self-loop guards.
    ///
    /// For self-loops with guards like `(not (<= K var))` (meaning var < K),
    /// we add `var <= K` as an invariant. This differs from in-loop bounds:
    /// the guard ensures var < K *during* the loop, but after the last iteration
    /// when var increments to K, the loop exits. So the exit bound is var <= K.
    ///
    /// This correctly handles patterns like:
    /// - guard: var < K, increment: var' = var + 1
    /// - exit bound: var <= K (because var can equal K on exit)
    ///
    /// Also handles BV equivalents (#8739): `(bvult var K_bv)` → `(bvule var K_bv)`,
    /// `(bvslt var K_bv)` → `(bvsle var K_bv)`, and their negated forms. This is
    /// essential for PDR to prove BV32/BV64 array-indexed benchmarks whose per-
    /// lemma self-inductiveness requires bounding the loop counter to rule out
    /// BV wraparound.
    pub(in crate::pdr::solver) fn discover_loop_exit_bounds(&mut self) {
        let predicates: Vec<_> = self.problem.predicates().to_vec();

        // Each entry is a pre-built frame[1] lemma: (predicate, formula, debug_description).
        // The debug_description is only consulted when self.config.verbose is set.
        let mut exit_bounds: Vec<(PredicateId, ChcExpr, String)> = Vec::new();

        for pred in &predicates {
            let canonical_vars = match self.canonical_vars(pred.id) {
                Some(v) => v.to_vec(),
                None => continue,
            };

            // Look at self-loop transitions for this predicate
            for clause in self.problem.clauses_defining(pred.id) {
                // Must be a self-loop (same predicate in body)
                if clause.body.predicates.len() != 1 {
                    continue;
                }
                let (body_pred, body_args) = &clause.body.predicates[0];
                if *body_pred != pred.id {
                    continue;
                }

                // Build mapping from body variable names to canonical variable indices
                // #2492: Also extract constituent vars from expression body args
                let mut body_to_canon: FxHashMap<String, ChcVar> = FxHashMap::default();
                for (i, body_arg) in body_args.iter().enumerate() {
                    if i < canonical_vars.len() {
                        match body_arg {
                            ChcExpr::Var(v) => {
                                body_to_canon.insert(v.name.clone(), canonical_vars[i].clone());
                            }
                            expr => {
                                for v in expr.vars() {
                                    body_to_canon
                                        .entry(v.name.clone())
                                        .or_insert_with(|| canonical_vars[i].clone());
                                }
                            }
                        }
                    }
                }

                // Extract exit bounds from the constraint (guard)
                if let Some(constraint) = &clause.body.constraint {
                    Self::collect_exit_bounds(
                        pred.id,
                        constraint,
                        &body_to_canon,
                        &mut exit_bounds,
                    );
                }
            }
        }

        // Now add the invariants
        for (predicate, bound_formula, description) in exit_bounds {
            // Check if already known
            let already_known = self.frames.len() > 1
                && self.frames[1]
                    .lemmas
                    .iter()
                    .any(|l| l.predicate == predicate && l.formula == bound_formula);

            if !already_known && self.frames.len() > 1 {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: Discovered loop exit bound for pred {}: {}",
                        predicate.index(),
                        description,
                    );
                }

                self.add_discovered_invariant(predicate, bound_formula, 1);
            }
        }
    }

    /// Collect exit bound information from a guard constraint.
    /// Unlike `collect_guard_bounds`, this extracts the exit bound (var <= K)
    /// rather than the in-loop bound (var <= K-1).
    ///
    /// Handles four guard shapes per index sort:
    /// - Int: `(not (<= K var))` ≡ `var < K` → emit `var <= K`
    /// - BV unsigned: `(bvult var K)` or `(not (bvule K var))` → emit `(bvule var K)`
    /// - BV signed: `(bvslt var K)` or `(not (bvsle K var))` → emit `(bvsle var K)`
    ///
    /// The result tuple is (predicate, pre_built_lemma_formula, human_description).
    pub(in crate::pdr::solver) fn collect_exit_bounds(
        predicate: PredicateId,
        constraint: &ChcExpr,
        body_to_canon: &FxHashMap<String, ChcVar>,
        result: &mut Vec<(PredicateId, ChcExpr, String)>,
    ) {
        // === Int: Pattern (not (<= K var)) ===
        if let ChcExpr::Op(ChcOp::Not, args) = constraint {
            if args.len() == 1 {
                match args[0].as_ref() {
                    // (not (<= K var)) means var < K, so exit bound is var <= K
                    ChcExpr::Op(ChcOp::Le, inner) if inner.len() == 2 => {
                        if let (ChcExpr::Int(k), ChcExpr::Var(var)) =
                            (inner[0].as_ref(), inner[1].as_ref())
                        {
                            if let Some(canon_var) = body_to_canon.get(&var.name) {
                                let formula =
                                    ChcExpr::le(ChcExpr::var(canon_var.clone()), ChcExpr::Int(*k));
                                let desc = format!("{} <= {}", canon_var.name, k);
                                result.push((predicate, formula, desc));
                            }
                        }
                    }
                    // (not (bvule K var)) ≡ (bvult var K), so exit bound is (bvule var K)
                    ChcExpr::Op(ChcOp::BvULe, inner) if inner.len() == 2 => {
                        if let (ChcExpr::BitVec(k, w), ChcExpr::Var(var)) =
                            (inner[0].as_ref(), inner[1].as_ref())
                        {
                            if let Some(canon_var) = body_to_canon.get(&var.name) {
                                let formula = ChcExpr::bv_ule(
                                    ChcExpr::var(canon_var.clone()),
                                    ChcExpr::BitVec(*k, *w),
                                );
                                let desc = format!("bvule {} (_ bv{} {})", canon_var.name, k, w);
                                result.push((predicate, formula, desc));
                            }
                        }
                    }
                    // (not (bvsle K var)) ≡ (bvslt var K), so exit bound is (bvsle var K)
                    ChcExpr::Op(ChcOp::BvSLe, inner) if inner.len() == 2 => {
                        if let (ChcExpr::BitVec(k, w), ChcExpr::Var(var)) =
                            (inner[0].as_ref(), inner[1].as_ref())
                        {
                            if let Some(canon_var) = body_to_canon.get(&var.name) {
                                let formula = ChcExpr::bv_sle(
                                    ChcExpr::var(canon_var.clone()),
                                    ChcExpr::BitVec(*k, *w),
                                );
                                let desc = format!("bvsle {} (_ bv{} {})", canon_var.name, k, w);
                                result.push((predicate, formula, desc));
                            }
                        }
                    }
                    _ => {}
                }
            }
        }

        // === BV: Direct (bvult var K) → (bvule var K) ===
        if let ChcExpr::Op(ChcOp::BvULt, inner) = constraint {
            if inner.len() == 2 {
                if let (ChcExpr::Var(var), ChcExpr::BitVec(k, w)) =
                    (inner[0].as_ref(), inner[1].as_ref())
                {
                    if let Some(canon_var) = body_to_canon.get(&var.name) {
                        let formula = ChcExpr::bv_ule(
                            ChcExpr::var(canon_var.clone()),
                            ChcExpr::BitVec(*k, *w),
                        );
                        let desc = format!("bvule {} (_ bv{} {})", canon_var.name, k, w);
                        result.push((predicate, formula, desc));
                    }
                }
            }
        }

        // === BV: Direct (bvslt var K) → (bvsle var K) ===
        if let ChcExpr::Op(ChcOp::BvSLt, inner) = constraint {
            if inner.len() == 2 {
                if let (ChcExpr::Var(var), ChcExpr::BitVec(k, w)) =
                    (inner[0].as_ref(), inner[1].as_ref())
                {
                    if let Some(canon_var) = body_to_canon.get(&var.name) {
                        let formula = ChcExpr::bv_sle(
                            ChcExpr::var(canon_var.clone()),
                            ChcExpr::BitVec(*k, *w),
                        );
                        let desc = format!("bvsle {} (_ bv{} {})", canon_var.name, k, w);
                        result.push((predicate, formula, desc));
                    }
                }
            }
        }

        // Pattern: (and ...) - recurse into conjuncts
        if let ChcExpr::Op(ChcOp::And, args) = constraint {
            for arg in args {
                Self::collect_exit_bounds(predicate, arg, body_to_canon, result);
            }
        }
    }

    /// Discover scaled post-transition bounds from guards like `not (<= (* k base) pivot)`.
    ///
    /// For self-loops with:
    /// - Guard: `not (<= (* k base) pivot)` meaning `pivot < k*base`
    /// - Update: `pivot' = pivot + delta` (start with delta=1)
    /// - Base preserved: `base' = base`
    ///
    /// We emit the post-transition bound: `pivot <= k*base + (delta-1)`
    /// (for delta=1: `pivot <= k*base`)
    ///
    /// Part of #1606 - enables gj2007 benchmark solving.
    pub(in crate::pdr::solver) fn discover_scaled_loop_exit_bounds(&mut self) {
        if self.frames.len() <= 1 {
            return;
        }

        let predicates: Vec<_> = self.problem.predicates().to_vec();

        // Collect scaled exit bound candidates: (pred, pivot_canon, k, base_canon)
        let mut scaled_bounds: Vec<(PredicateId, ChcVar, i128, ChcVar)> = Vec::new();

        for pred in &predicates {
            let canonical_vars = match self.canonical_vars(pred.id) {
                Some(v) => v.to_vec(),
                None => continue,
            };

            // Look at self-loop transitions for this predicate
            for clause in self.problem.clauses_defining(pred.id) {
                // Must be a self-loop (same predicate in body)
                if clause.body.predicates.len() != 1 {
                    continue;
                }
                let (body_pred, body_args) = &clause.body.predicates[0];
                if *body_pred != pred.id {
                    continue;
                }

                // Get head arguments
                let head_args = match &clause.head {
                    crate::ClauseHead::Predicate(_, args) => args,
                    crate::ClauseHead::False => continue,
                };

                // Build mapping from body variable names to canonical variable indices
                // #2492: Also extract constituent vars from expression body args
                let mut body_to_canon: FxHashMap<String, (usize, ChcVar)> = FxHashMap::default();
                for (i, body_arg) in body_args.iter().enumerate() {
                    if i < canonical_vars.len() {
                        match body_arg {
                            ChcExpr::Var(v) => {
                                body_to_canon
                                    .insert(v.name.clone(), (i, canonical_vars[i].clone()));
                            }
                            expr => {
                                for v in expr.vars() {
                                    body_to_canon
                                        .entry(v.name.clone())
                                        .or_insert_with(|| (i, canonical_vars[i].clone()));
                                }
                            }
                        }
                    }
                }

                // Extract scaled guards from the constraint
                if let Some(constraint) = &clause.body.constraint {
                    Self::collect_scaled_exit_bounds(
                        pred.id,
                        constraint,
                        &body_to_canon,
                        head_args,
                        &mut scaled_bounds,
                    );
                }
            }
        }

        // Deduplicate scaled_bounds to avoid redundant processing
        scaled_bounds.sort_by(|a, b| {
            (a.0.index(), &a.1.name, a.2, &a.3.name).cmp(&(b.0.index(), &b.1.name, b.2, &b.3.name))
        });
        scaled_bounds.dedup_by(|a, b| {
            a.0 == b.0 && a.1.name == b.1.name && a.2 == b.2 && a.3.name == b.3.name
        });

        // Add the discovered invariants
        for (predicate, pivot_canon, k, base_canon) in scaled_bounds {
            // Emit: pivot <= k * base (for delta=1)
            let k_times_base = ChcExpr::Op(
                ChcOp::Mul,
                vec![
                    Arc::new(ChcExpr::Int(k)),
                    Arc::new(ChcExpr::var(base_canon.clone())),
                ],
            );
            let bound_formula = ChcExpr::le(ChcExpr::var(pivot_canon.clone()), k_times_base);

            // Check if already known
            let already_known = self.frames[1]
                .lemmas
                .iter()
                .any(|l| l.predicate == predicate && l.formula == bound_formula);

            if !already_known {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: Discovered scaled loop exit bound for pred {}: {} <= {}*{}",
                        predicate.index(),
                        pivot_canon.name,
                        k,
                        base_canon.name,
                    );
                }

                self.add_discovered_invariant(predicate, bound_formula, 1);
            }
        }
    }

    /// Extract scaled guard pattern from constraint: `not (<= (* k base) pivot)`.
    ///
    /// Returns (k, base_var_name) if matched.
    pub(in crate::pdr::solver) fn extract_scaled_guard_lt(
        constraint: &ChcExpr,
        pivot_var_name: &str,
    ) -> Option<(i128, String)> {
        // Pattern: (not (<= (* k base) pivot)) means pivot < k*base
        if let ChcExpr::Op(ChcOp::Not, args) = constraint {
            if args.len() == 1 {
                if let ChcExpr::Op(ChcOp::Le, inner_args) = args[0].as_ref() {
                    if inner_args.len() == 2 {
                        // (<= limit pivot) where limit = (* k base)
                        if let ChcExpr::Var(pivot) = inner_args[1].as_ref() {
                            if pivot.name == pivot_var_name {
                                // Check if limit is (* k base)
                                if let ChcExpr::Op(ChcOp::Mul, mul_args) = inner_args[0].as_ref() {
                                    if mul_args.len() == 2 {
                                        // Try both orderings: (k * base) or (base * k)
                                        if let (ChcExpr::Int(k), ChcExpr::Var(base)) =
                                            (mul_args[0].as_ref(), mul_args[1].as_ref())
                                        {
                                            // Cap k to avoid blowup (per design doc)
                                            if *k > 0 && *k <= 16 {
                                                return Some((*k, base.name.clone()));
                                            }
                                        }
                                        if let (ChcExpr::Var(base), ChcExpr::Int(k)) =
                                            (mul_args[0].as_ref(), mul_args[1].as_ref())
                                        {
                                            if *k > 0 && *k <= 16 {
                                                return Some((*k, base.name.clone()));
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        None
    }

    /// Collect scaled exit bound candidates from a constraint.
    ///
    /// Given a self-loop with guard `not (<= (* k base) pivot)` (meaning pivot < k*base),
    /// increment delta=1, and preserved base, emit candidate (pred, pivot_canon, k, base_canon).
    pub(in crate::pdr::solver) fn collect_scaled_exit_bounds(
        predicate: PredicateId,
        constraint: &ChcExpr,
        body_to_canon: &FxHashMap<String, (usize, ChcVar)>,
        head_args: &[ChcExpr],
        result: &mut Vec<(PredicateId, ChcVar, i128, ChcVar)>,
    ) {
        // Try each integer variable as potential pivot
        for (body_var_name, (idx, pivot_canon)) in body_to_canon {
            // Only handle Int sort
            if !matches!(pivot_canon.sort, ChcSort::Int) {
                continue;
            }

            // Check for scaled guard: pivot < k*base
            if let Some((k, base_body_name)) =
                Self::extract_scaled_guard_lt(constraint, body_var_name)
            {
                // Get base variable's canonical form
                let (base_idx, base_canon) = match body_to_canon.get(&base_body_name) {
                    Some(bc) => bc,
                    None => continue,
                };

                // Check increment: delta = 1 for now (gj2007 pattern)
                let head_pivot = &head_args[*idx];
                let pivot_delta =
                    Self::get_offset_from_head_arg(head_pivot, body_var_name, constraint);
                if pivot_delta != Some(1) {
                    continue; // Only handle delta=1 for now
                }

                // Check base preservation: base' = base (delta = 0)
                let head_base = &head_args[*base_idx];
                let base_delta =
                    Self::get_offset_from_head_arg(head_base, &base_body_name, constraint);
                if base_delta != Some(0) {
                    continue; // Base must be preserved
                }

                result.push((predicate, pivot_canon.clone(), k, base_canon.clone()));
            }
        }

        // Recurse into AND conjuncts
        if let ChcExpr::Op(ChcOp::And, args) = constraint {
            for arg in args {
                Self::collect_scaled_exit_bounds(predicate, arg, body_to_canon, head_args, result);
            }
        }
    }

    /// Get the offset from a head argument expression for a variable.
    ///
    /// If head_arg = body_var + c (or encoded via constraint equality), returns Some(c).
    pub(in crate::pdr::solver) fn get_offset_from_head_arg(
        head_arg: &ChcExpr,
        body_var_name: &str,
        constraint: &ChcExpr,
    ) -> Option<i128> {
        // Case 1: head_arg is a direct expression like (+ 1 body_var)
        if let Some(offset) = Self::extract_addition_offset(head_arg, body_var_name) {
            return Some(offset);
        }

        // Case 2: head_arg is a variable, and constraint has head_var = body_var + c
        if let ChcExpr::Var(head_var) = head_arg {
            if let Some(offset) =
                Self::find_offset_in_constraint(constraint, body_var_name, &head_var.name)
            {
                return Some(offset);
            }
        }

        None
    }
}
