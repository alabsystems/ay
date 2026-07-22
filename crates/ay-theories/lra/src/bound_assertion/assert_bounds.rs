// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl LraSolver {
    /// #8406: Takes `Rational` instead of `BigRational` to avoid heap allocation
    /// on every bound assertion. Callers pass `Rational::zero()` for the common
    /// case of `expr <= 0` / `expr >= 0` comparisons.
    pub(crate) fn assert_bound_with_reasons(
        &mut self,
        expr: LinearExpr,
        mut bound: Rational,
        bound_type: BoundType,
        mut strict: bool,
        reasons: &[(TermId, bool)],
        atom_key: Option<(TermId, bool)>,
    ) {
        // Integer canonicalization: for integer-VALUED expressions, strict
        // bounds can be converted to non-strict with ±1 adjustment since all
        // values are integers. `expr < 0` → `expr <= -1`, `expr > 0` → `expr >= 1`.
        //
        // SOUNDNESS (#to_int floor-axiom false-UNSAT): this rewrite is valid
        // ONLY when `expr` is integer-valued. Even in `integer_mode` (the LIA
        // inner LRA relaxation) the EXPRESSION can be non-integer. Two ways:
        //   (1) a fractional constant or coefficient — e.g. the `to_int` floor
        //       axiom `0 <= (to_real i - 0.5) - to_int < 1`, whose
        //       `diff = i - to_int - 1/2` ranges over the half-integers; and
        //   (2) a REAL-sorted variable with an integer coefficient — e.g. the
        //       floor axiom `0 <= r - to_int < 1` over a Real `r` (the
        //       `to_int(r)` / `to_int(r - 0.25)` shared-`i0` family).
        // In either case canonicalizing `expr < 1` to `expr <= 0` wrongly
        // excludes the genuine fractional witness (e.g. `diff = 1/2`,
        // `r - to_int = 1/2`), manufacturing a spurious UNSAT (LRA-relaxation
        // or GCD-test). Restrict the ±1 tightening to PROVABLY integer-valued
        // expressions: integer bound, integer constant, integer coefficients,
        // and every participating variable Int-sorted (vars with no term, i.e.
        // internal continuous slacks, are NOT integer). Skipping it otherwise
        // keeps the exact strict bound — always sound — and the optimization
        // still fires for every genuinely integer atom.
        let expr_is_integer_valued = bound.is_integer()
            && expr.constant.is_integer()
            && expr.coeffs.iter().all(|(var, c)| {
                c.is_integer()
                    && self
                        .var_term_id(*var)
                        .is_some_and(|t| self.terms().sort(t) == &Sort::Int)
            });
        if self.integer_mode && strict && expr_is_integer_valued {
            match bound_type {
                BoundType::Upper => {
                    // expr < bound → expr <= bound - 1
                    bound -= Rational::one();
                    strict = false;
                }
                BoundType::Lower => {
                    // expr > bound → expr >= bound + 1
                    bound += Rational::one();
                    strict = false;
                }
            }
        }

        if expr.is_constant() {
            // Pure constant comparison - check immediately.
            // For example, `(- n (+ i 1)) < (- n i)` simplifies to `-1 < 0`.
            // After cancellation: constant_expr <=/>=/</>= bound.
            let const_val = &expr.constant;
            let cmp = const_val.cmp(&bound);
            let satisfied = match (bound_type, strict) {
                (BoundType::Upper, false) => cmp != std::cmp::Ordering::Greater, // expr <= bound
                (BoundType::Upper, true) => cmp == std::cmp::Ordering::Less,     // expr < bound
                (BoundType::Lower, false) => cmp != std::cmp::Ordering::Less,    // expr >= bound
                (BoundType::Lower, true) => cmp == std::cmp::Ordering::Greater,  // expr > bound
            };
            if !satisfied && self.trivial_conflict.is_none() {
                // Constant constraint violated - record trivial conflict.
                // Only record the first conflict (don't overwrite with subsequent ones).
                //
                // #8012: Store ALL reason literals so the blocking clause is complete.
                // Previously only the first reason was kept, producing overly-strong
                // single-literal blocking clauses.
                //
                // Axioms (empty reasons) cannot produce a meaningful conflict literal.
                // If an axiom's constant check fails, the problem is theory-level UNSAT
                // and the conflict clause needs no blame literals (#6187).
                debug_assert!(
                    !reasons.is_empty(),
                    "BUG: axiom constant-expression violated (const={const_val}, bound={bound}, type={bound_type:?}, strict={strict})"
                );
                if !reasons.is_empty() {
                    let conflict_lits: Vec<TheoryLit> = reasons
                        .iter()
                        .map(|&(term, value)| TheoryLit::new(term, value))
                        .collect();
                    self.trivial_conflict = Some(conflict_lits);
                }
            }
            return;
        }

        // Fast path: a single affine variable constraint can be asserted as a direct bound.
        //
        // The atom parser normalizes comparisons into the form `expr <= bound` or `expr >= bound`,
        // where `expr` may include a constant offset (e.g. `x - 5 <= 0`).
        //
        // Avoid creating slack variables/tableau rows for the common case:
        //   coeff*x + const <= bound
        //   coeff*x + const >= bound
        if expr.coeffs.len() == 1 {
            let (var, coeff) = &expr.coeffs[0];
            if !coeff.is_zero() {
                // #8406: Rational arithmetic avoids BigRational allocation.
                let rhs = &(&bound - &expr.constant) / coeff;
                let coeff_positive = coeff.is_positive();
                let var_bound_type = match (bound_type, coeff_positive) {
                    (BoundType::Upper, true) | (BoundType::Lower, false) => BoundType::Upper, // x <= rhs
                    (BoundType::Upper, false) | (BoundType::Lower, true) => BoundType::Lower, // x >= rhs
                };
                // Farkas scale: when the original atom is `coeff*x + const <= bound`,
                // we normalize to `x <= (bound-const)/coeff`. The Farkas coefficient
                // for this reason must be scaled by 1/|coeff| so that the original
                // atom's variable terms cancel correctly in the certificate.
                // #8406: Use Rational to avoid BigRational heap allocation.
                let farkas_scale = coeff.abs().recip();
                if reasons.len() == 1 {
                    let (reason, reason_value) = reasons[0];
                    self.assert_var_bound(
                        *var,
                        rhs,
                        var_bound_type,
                        strict,
                        reason,
                        reason_value,
                        farkas_scale,
                    );
                } else {
                    // Multi-reason or axiom (empty reasons): use the
                    // multi-reason path which handles empty correctly (#6187).
                    let scales: Vec<Rational> =
                        reasons.iter().map(|_| farkas_scale.clone()).collect();
                    self.assert_var_bound_with_reasons(
                        *var,
                        rhs,
                        var_bound_type,
                        strict,
                        reasons,
                        &scales,
                    );
                }
                return;
            }
        }

        // Reuse existing slack variable if this atom was previously asserted (#4919)
        // or pre-registered via register_atom (#4919 RC2).
        // After push/pop, bound_atoms is cleared but the slack variable and its
        // tableau row persist. Reusing the existing slack prevents unbounded tableau
        // growth across DPLL(T) backtracking cycles.
        let slack = if let Some((existing, ref cached_orig)) =
            atom_key.and_then(|k| self.atom_slack.get(&k).cloned())
        {
            // Reuse cached slack. Apply constant compensation (#6205):
            // The slack may have been created by a different atom's expression
            // via expr_to_slack, with a different constant offset. Without this
            // adjustment, re-assertions after push/pop assert the wrong bound,
            // causing false UNSAT on formulas with disjunctions.
            // #8406: Rational arithmetic avoids BigRational allocation.
            bound = &(&bound - &expr.constant) + cached_orig;
            existing
        } else {
            let (new_slack, orig_constant) = self.get_or_create_slack(&expr);
            // When the slack was created for an expression with a different constant
            // offset, adjust the bound to compensate (#6193).
            //
            // The slack `s` satisfies: s = sum(coeff_i * x_i) + orig_constant
            // We want to assert: sum(coeff_i * x_i) + expr.constant <=/>=  bound
            // Substituting: s - orig_constant + expr.constant <=/>=  bound
            // Therefore:    s <=/>=  bound - expr.constant + orig_constant
            // #8406: Rational arithmetic avoids BigRational allocation.
            bound = &(&bound - &expr.constant) + &orig_constant;
            // Cache (slack, orig_constant) for reuse after push/pop (#6205)
            if let Some(key) = atom_key {
                self.atom_slack.insert(key, (new_slack, orig_constant));
            }
            new_slack
        };

        // Assert bound on slack variable. Scale is 1 because the slack variable
        // represents the original expression directly (no coefficient normalization).
        if self.debug_lra {
            safe_eprintln!(
                "[LRA]   -> slack var={}, adjusted_bound={}, {:?}, strict={}",
                slack,
                bound,
                bound_type,
                strict,
            );
        }
        if reasons.len() == 1 {
            let (reason, reason_value) = reasons[0];
            self.assert_var_bound(
                slack,
                bound,
                bound_type,
                strict,
                reason,
                reason_value,
                Rational::one(),
            );
        } else {
            // Multi-reason or axiom (empty reasons): use the
            // multi-reason path which handles empty correctly (#6187).
            // #8406: Use Rational::one() to avoid BigRational heap allocation.
            let scales: Vec<Rational> = reasons.iter().map(|_| Rational::one()).collect();
            self.assert_var_bound_with_reasons(slack, bound, bound_type, strict, reasons, &scales);
        }
    }

    /// Assert a bound on a single variable. Returns `true` if the bound was
    /// actually tightened (new bound is stricter than existing), `false` if
    /// the new bound was redundant.
    ///
    /// #8406: Takes `Rational` instead of `BigRational` to avoid heap allocation.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn assert_var_bound(
        &mut self,
        var: u32,
        bound: Rational,
        bound_type: BoundType,
        strict: bool,
        reason: TermId,
        reason_value: bool,
        reason_scale: Rational,
    ) -> bool {
        let debug = self.debug_lra_bounds;
        if debug {
            safe_eprintln!("[LRA_BOUNDS] assert_var_bound: var={}, bound={}, type={:?}, strict={}, reason={:?}, scale={}",
                var, bound, bound_type, strict, reason, reason_scale);
        }

        while self.vars.len() <= var as usize {
            self.vars.push(VarInfo::default());
        }
        let info = &mut self.vars[var as usize];

        if debug {
            safe_eprintln!(
                "[LRA_BOUNDS]   BEFORE: lb={:?}, ub={:?}",
                info.lower.as_ref().map(|b| &b.value),
                info.upper.as_ref().map(|b| &b.value)
            );
        }

        // Save old bound for backtracking (only clone the bound being modified).
        let old_bound = match bound_type {
            BoundType::Lower => info.lower.clone(),
            BoundType::Upper => info.upper.clone(),
        };
        self.trail.push((var, bound_type, old_bound));
        // LIA algebraic-detection memo invalidation (`bound_revision`) is
        // decided AFTER the write below, and only when the write touches a
        // TIGHT (lower == upper, non-strict) pair — the only bound state the
        // detection reads. The BCP-time re-assert flood (process_check_atoms
        // re-presenting unchanged atom bounds every check) is should_update-
        // gated and never writes, so it must not invalidate the memo.
        let was_tight = matches!(
            (&info.lower, &info.upper),
            (Some(l), Some(u)) if l.value == u.value && !l.strict && !u.strict
        );

        let new_bound = Bound::new(
            bound,
            vec![reason],
            vec![reason_value],
            vec![reason_scale],
            strict,
        );

        let tightened = match bound_type {
            BoundType::Lower => {
                // Only update if tighter
                let should_update = match &info.lower {
                    None => true,
                    Some(existing) => {
                        new_bound.value > existing.value
                            || (new_bound.value == existing.value
                                && new_bound.strict
                                && !existing.strict)
                    }
                };
                if should_update {
                    info.lower = Some(new_bound);
                }
                should_update
            }
            BoundType::Upper => {
                // Only update if tighter
                let should_update = match &info.upper {
                    None => true,
                    Some(existing) => {
                        new_bound.value < existing.value
                            || (new_bound.value == existing.value
                                && new_bound.strict
                                && !existing.strict)
                    }
                };
                if should_update {
                    info.upper = Some(new_bound);
                }
                should_update
            }
        };

        if debug {
            let info = &self.vars[var as usize];
            safe_eprintln!(
                "[LRA_BOUNDS]   AFTER: lb={:?}, ub={:?}, tightened={}",
                info.lower.as_ref().map(|b| &b.value),
                info.upper.as_ref().map(|b| &b.value),
                tightened,
            );
        }

        // Tight-pair-aware memo invalidation (see comment at the trail push):
        // a write that leaves the var tight-free both before and after cannot
        // change anything `detect_algebraic_equalities` reads.
        if tightened {
            let info = &self.vars[var as usize];
            let now_tight = matches!(
                (&info.lower, &info.upper),
                (Some(l), Some(u)) if l.value == u.value && !l.strict && !u.strict
            );
            if was_tight || now_tight {
                self.bound_revision += 1;
            }
        }

        if tightened {
            self.bounds_tightened_since_simplex = true;
            // #8187: mirror bounds_tightened_since_simplex into the
            // soundness-gate flag. Both are set here; cleared at each simplex
            // completion. See docstring on `post_simplex_bounds_added` in
            // lib.rs for the consumption difference.
            self.post_simplex_bounds_added = true;
            // #inc-guard-memo: a tightened bound can newly exclude the current
            // assignment — the guard must rescan.
            self.guard_clean_valid = false;
            self.vars_tightened_since_simplex.push(var);
            self.direct_bounds_changed_since_implied = true;
            self.direct_bounds_changed_vars.push(var);
            self.bcp_implied_dry_streak = 0; // #8200
            self.bcp_cascade_dry_streak = 0; // #8255
            self.propagation_dirty_vars.insert(var);
            // Mark rows containing this variable as touched (#4919).
            // Z3 equivalent: activate() → insert_to_columns_with_changed_bounds(j)
            // → detect_rows_with_changed_bounds() → add_column_rows_to_touched_rows(j).
            // Without this, compute_implied_bounds sees an empty touched_rows set
            // and derives 0 bounds on benchmarks with many free variables.
            let vi = var as usize;
            if vi < self.col_index.len() {
                for entry in &self.col_index[vi] {
                    self.touched_rows.insert(entry.row_idx);
                }
            }
            if let Some(&ri) = self.basic_var_to_row.get(&var) {
                self.touched_rows.insert(ri);
            }
            self.propagate_direct_touched_rows_pending = true;
            // Eager per-variable propagation (#4919 RC2): when a bound on this
            // variable tightens, immediately propagate implications to atoms
            // involving this variable. This avoids waiting for the full simplex
            // round and gives the SAT solver immediate pruning.
            self.propagate_var_atoms(var);
            // Eager fixed-variable equality detection (#6617 Packet 2):
            // When lower == upper for a variable, register it immediately so
            // the value-table lookup can fire equalities without waiting for
            // compute_implied_bounds(). Z3 equivalent: fixed_var_eh().
            let is_fixed = {
                let vi = var as usize;
                self.vars.get(vi).is_some_and(|info| {
                    matches!(
                        (&info.lower, &info.upper),
                        (Some(lb), Some(ub)) if !lb.strict && !ub.strict && lb.value == ub.value
                    )
                })
            };
            if is_fixed {
                self.register_fixed_term_var(var);
            }
            // Pre-simplex inline refinement removed (#6617): the post-simplex
            // compute_implied_bounds() + queue_post_simplex_refinements() path
            // already handles all materializable vars (including slack) in a
            // single O(touched_rows) batch pass. The inline per-variable scan
            // was O(N × rows_per_var) where N = bound tightenings per check,
            // causing 20-350x slowdowns on sc-* benchmarks vs Z3.

            // Incrementally update the infeasible heap for this variable and
            // all basic variables in rows containing it (#8782). This avoids
            // a full O(rows) rebuild_infeasible_heap() at the start of simplex
            // when only a few variables' bounds changed.
            if !self.heap_stale {
                self.track_var_feasibility(var);
                let vi = var as usize;
                if vi < self.col_index.len() {
                    let n = self.col_index[vi].len();
                    for idx in 0..n {
                        let ri = self.col_index[vi][idx].row_idx;
                        let bv = self.rows[ri].basic_var;
                        self.track_var_feasibility(bv);
                    }
                }
            }
        }
        self.dirty = true;
        tightened
    }

    /// Assert a bound on a single variable with multiple reasons.
    /// Used when bounds are derived from multiple constraints (e.g., Diophantine solving).
    /// Returns `true` if the bound was actually tightened.
    ///
    /// #8406: Takes `Rational` instead of `BigRational`.
    pub(crate) fn assert_var_bound_with_reasons(
        &mut self,
        var: u32,
        bound: Rational,
        bound_type: BoundType,
        strict: bool,
        reasons: &[(TermId, bool)],
        reason_scales: &[Rational],
    ) -> bool {
        while self.vars.len() <= var as usize {
            self.vars.push(VarInfo::default());
        }
        let info = &mut self.vars[var as usize];

        // Save old bound for backtracking (only clone the bound being modified).
        let old_bound = match bound_type {
            BoundType::Lower => info.lower.clone(),
            BoundType::Upper => info.upper.clone(),
        };
        self.trail.push((var, bound_type, old_bound));
        // LIA algebraic-detection memo invalidation (`bound_revision`) is
        // decided AFTER the write below, and only when the write touches a
        // TIGHT (lower == upper, non-strict) pair — the only bound state the
        // detection reads. The BCP-time re-assert flood (process_check_atoms
        // re-presenting unchanged atom bounds every check) is should_update-
        // gated and never writes, so it must not invalidate the memo.
        let was_tight = matches!(
            (&info.lower, &info.upper),
            (Some(l), Some(u)) if l.value == u.value && !l.strict && !u.strict
        );

        let (reason_ids, reason_vals): (Vec<_>, Vec<_>) = reasons.iter().copied().unzip();
        let new_bound = Bound::new(
            bound,
            reason_ids,
            reason_vals,
            reason_scales.to_vec(),
            strict,
        );

        let tightened = match bound_type {
            BoundType::Lower => {
                // Only update if tighter
                let should_update = match &info.lower {
                    None => true,
                    Some(existing) => {
                        new_bound.value > existing.value
                            || (new_bound.value == existing.value
                                && new_bound.strict
                                && !existing.strict)
                    }
                };
                if should_update {
                    info.lower = Some(new_bound);
                }
                should_update
            }
            BoundType::Upper => {
                // Only update if tighter
                let should_update = match &info.upper {
                    None => true,
                    Some(existing) => {
                        new_bound.value < existing.value
                            || (new_bound.value == existing.value
                                && new_bound.strict
                                && !existing.strict)
                    }
                };
                if should_update {
                    info.upper = Some(new_bound);
                }
                should_update
            }
        };

        // Tight-pair-aware memo invalidation (see comment at the trail push).
        if tightened {
            let info = &self.vars[var as usize];
            let now_tight = matches!(
                (&info.lower, &info.upper),
                (Some(l), Some(u)) if l.value == u.value && !l.strict && !u.strict
            );
            if was_tight || now_tight {
                self.bound_revision += 1;
            }
        }

        if tightened {
            self.bounds_tightened_since_simplex = true;
            // #8187: mirror into the soundness-gate flag (see lib.rs docstring).
            self.post_simplex_bounds_added = true;
            // #inc-guard-memo: a tightened bound can newly exclude the current
            // assignment — the guard must rescan.
            self.guard_clean_valid = false;
            self.vars_tightened_since_simplex.push(var);
            self.direct_bounds_changed_since_implied = true;
            self.direct_bounds_changed_vars.push(var);
            self.bcp_implied_dry_streak = 0; // #8200
            self.bcp_cascade_dry_streak = 0; // #8255
            self.propagation_dirty_vars.insert(var);
            // Mark rows containing this variable as touched (#4919 Phase A)
            let vi = var as usize;
            if vi < self.col_index.len() {
                for entry in &self.col_index[vi] {
                    self.touched_rows.insert(entry.row_idx);
                }
            }
            if let Some(&ri) = self.basic_var_to_row.get(&var) {
                self.touched_rows.insert(ri);
            }
            self.propagate_direct_touched_rows_pending = true;
            self.propagate_var_atoms(var);
            // Incremental heap maintenance (#8782) — same as assert_var_bound.
            if !self.heap_stale {
                self.track_var_feasibility(var);
                let vi = var as usize;
                if vi < self.col_index.len() {
                    let n = self.col_index[vi].len();
                    for idx in 0..n {
                        let ri = self.col_index[vi][idx].row_idx;
                        let bv = self.rows[ri].basic_var;
                        self.track_var_feasibility(bv);
                    }
                }
            }
        }
        self.dirty = true;
        tightened
    }
}
