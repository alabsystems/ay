// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Row-level reason collection for implied bounds.
//!
//! Extracted from `implied_bounds.rs` to reduce file size.
//! Contains: `collect_reasons_from_explanation`, `collect_row_reasons_dedup`,
//! `collect_row_reasons_recursive`, `collect_reasons_from_row_for_basic`,
//! and `collect_single_row_reasons`.

use super::*;

/// RAII borrow of a reused reason-collection scratch set (reason-alloc-wip).
///
/// Moves the set out of its `RefCell` (leaving an empty placeholder), CLEARS
/// it so no stale membership from a prior call leaks into this traversal, and
/// moves it back on drop. Only momentary `RefCell` borrows are taken (the
/// `mem::take` on acquire and the restore on drop) — the set is owned by the
/// guard for the whole traversal, so nested reason collection can never panic
/// on a double `borrow_mut`. Clearing on acquire is load-bearing for
/// byte-identity: a leftover `visited`/`on_stack`/`seen` entry would drop a
/// real antecedent and change the collected reason set.
struct ReasonScratch<'a, E> {
    cell: &'a std::cell::RefCell<HashSet<E>>,
    val: HashSet<E>,
}

impl<'a, E> ReasonScratch<'a, E> {
    /// Take the scratch set out of `cell` and clear it for a fresh traversal.
    fn new(cell: &'a std::cell::RefCell<HashSet<E>>) -> Self {
        let mut val = std::mem::take(&mut *cell.borrow_mut());
        val.clear();
        Self { cell, val }
    }
}

impl<E> Drop for ReasonScratch<'_, E> {
    fn drop(&mut self) {
        // Restore the (now capacity-retaining) set for the next call. Momentary
        // borrow only; if re-entrancy left a different set here it is simply
        // clobbered — correctness holds because every acquire clears.
        *self.cell.borrow_mut() = std::mem::take(&mut self.val);
    }
}

impl<E> std::ops::Deref for ReasonScratch<'_, E> {
    type Target = HashSet<E>;
    fn deref(&self) -> &HashSet<E> {
        &self.val
    }
}

impl<E> std::ops::DerefMut for ReasonScratch<'_, E> {
    fn deref_mut(&mut self) -> &mut HashSet<E> {
        &mut self.val
    }
}

impl LraSolver {
    /// Whether the bound `(cur_value, cur_strict)` on side `is_upper` is at
    /// least as tight as `(used_value, used_strict)`: it entails it.
    #[inline]
    pub(crate) fn bound_at_least_as_tight(
        cur_value: &Rational,
        cur_strict: bool,
        used_value: &Rational,
        used_strict: bool,
        is_upper: bool,
    ) -> bool {
        match cur_value.cmp(used_value) {
            std::cmp::Ordering::Equal => cur_strict || !used_strict,
            std::cmp::Ordering::Less => is_upper,
            std::cmp::Ordering::Greater => !is_upper,
        }
    }

    /// Collect the reason literals that ground a row-derived bound through
    /// its derivation-time explanation (#6617), checking every step.
    ///
    /// For each antecedent `(var, side, value, strict)` the derivation
    /// consumed, the CURRENT bound on that side must be at least as tight
    /// (`bound_at_least_as_tight`), otherwise the chain fails closed:
    ///   * a direct bound that suffices and whose reason atoms are all
    ///     asserted is cited (shortest reason, no recursion);
    ///   * else a row-derived slot bound that suffices is recursed into
    ///     through its own explanation, once per `(var, side)` on this walk;
    ///   * else the antecedent cannot be grounded and the whole reason is
    ///     rejected.
    /// Because rows are equations valid in every model, "each antecedent is
    /// entailed by the cited literals" gives "the derived bound is entailed
    /// by the cited literals" by induction over the chain — the caller may
    /// rely on the collected set entailing the slot's `(value, strict)`.
    ///
    /// Soundness (#cyclic-explanation false-UNSAT): `on_stack` holds the
    /// (var, direction) pairs whose implied-bound explanation is CURRENTLY
    /// being resolved on this DFS path (gray nodes), seeded with the root
    /// bound being explained. Only the latest explanation per (var, side)
    /// is stored, so re-walking chains against CURRENT bounds can hit a
    /// cycle (implied_ub(x) cites implied_lb(y) which cites an EARLIER
    /// implied_ub(x)); the value check passes on such an edge (the current
    /// bound is tighter than the earlier one it replaced) but the
    /// well-founded history is gone, so a back edge fails closed. Nodes
    /// FULLY explained earlier on this walk (`visited_vars`, black) are
    /// skipped after their value check — their reasons are already
    /// collected and ground their current bound.
    pub(crate) fn collect_reasons_from_explanation(
        &self,
        explanation: &BoundExplanation,
        reasons: &mut Vec<TheoryLit>,
        seen: &mut HashSet<(TermId, bool)>,
        visited_vars: &mut HashSet<(u32, bool)>,
        on_stack: &mut HashSet<(u32, bool)>,
    ) -> bool {
        // #8003/#8452: Budget guard. Each antecedent does Rational
        // comparisons (potential bignum) and may recurse; 500 keeps dense
        // LP chains (rand_70_300, 70+ vars per row) explainable while
        // bounding worst-case cost.
        const MAX_VISITED: usize = 500;
        if visited_vars.len() >= MAX_VISITED {
            return false;
        }
        for ante in &explanation.contributing_vars {
            let var = ante.var;
            let used_upper = ante.used_upper;
            // Cycle (gray back edge): the justification is circular.
            if on_stack.contains(&(var, used_upper)) {
                return false;
            }
            let vi = var as usize;
            let Some(info) = self.vars.get(vi) else {
                return false;
            };
            let direct = if used_upper {
                info.upper.as_ref()
            } else {
                info.lower.as_ref()
            };
            // (1) The direct bound suffices and all its reason atoms are
            // still asserted (#8511: a retracted direct bound must not be
            // cited): cite it.
            if let Some(b) = direct {
                if Self::bound_at_least_as_tight(
                    &b.value,
                    b.strict,
                    &ante.value,
                    ante.strict,
                    used_upper,
                ) && b
                    .reason_pairs()
                    .filter(|(term, _)| !term.is_sentinel())
                    .all(|(term, val)| self.asserted.get(&term) == Some(&val))
                {
                    for (term, val) in b.reason_pairs() {
                        if !term.is_sentinel() && seen.insert((term, val)) {
                            reasons.push(TheoryLit::new(term, val));
                        }
                    }
                    continue;
                }
            }
            // (2) The current row-derived slot bound suffices: ground it
            // through its own explanation.
            let implied = self.implied_bounds.get(vi).and_then(|p| {
                if used_upper {
                    p.1.as_ref()
                } else {
                    p.0.as_ref()
                }
            });
            match implied {
                Some(ib)
                    if ib.row_idx != usize::MAX
                        && Self::bound_at_least_as_tight(
                            &ib.value,
                            ib.strict,
                            &ante.value,
                            ante.strict,
                            used_upper,
                        ) =>
                {
                    let Some(expl) = ib.explanation.as_ref() else {
                        return false;
                    };
                    if !visited_vars.insert((var, used_upper)) {
                        // Black node: this slot bound was grounded earlier on
                        // this walk and it entails the antecedent (checked
                        // above); its reasons are already collected.
                        continue;
                    }
                    on_stack.insert((var, used_upper));
                    let ok = self.collect_reasons_from_explanation(
                        expl,
                        reasons,
                        seen,
                        visited_vars,
                        on_stack,
                    );
                    on_stack.remove(&(var, used_upper));
                    if !ok {
                        return false;
                    }
                }
                _ => return false,
            }
        }
        true
    }

    /// Re-derive the `need_upper` bound on `var` from the CURRENT row at
    /// `row_idx` using DIRECT bounds only, returning the reason literals
    /// together with the derived `(value, strict)` they entail.
    ///
    /// The row equation `x_b - sum(a_j x_j) = constant` (equation
    /// coefficients: `+1` for the basic variable, `-a_j` for the others) is
    /// solved for `var`: with `e_t` its equation coefficient,
    /// `e_t * var = constant - sum_{i != t} e_i x_i`, so an upper bound on
    /// `var` needs the minimum of the sum when `e_t > 0` (lower bounds of
    /// positive-`e_i` variables, upper bounds of negative-`e_i` ones) and its
    /// maximum when `e_t < 0`; a lower bound is the mirror image. Every
    /// consumed bound must be a direct bound whose reason atoms are all
    /// asserted; otherwise `None`. The row is read as it is NOW, so the
    /// result is exact for the current state regardless of pivots since the
    /// slot bound was derived; the caller checks the returned value against
    /// what it needs to prove.
    pub(crate) fn derive_bound_from_row_direct_only(
        &self,
        var: u32,
        need_upper: bool,
        row_idx: usize,
    ) -> Option<(Vec<TheoryLit>, Rational, bool)> {
        let row = self.rows.get(row_idx)?;
        let bv = row.basic_var;
        // Equation coefficient of the target.
        let e_t: Rational = if bv == var {
            Rational::one()
        } else {
            let idx = row.coeffs.binary_search_by_key(&var, |(v, _)| *v).ok()?;
            -&row.coeffs[idx].1
        };
        if e_t.is_zero() {
            return None;
        }
        // Upper bound on var with e_t > 0 (or lower with e_t < 0) consumes the
        // MINIMUM of sum_{i != t} e_i x_i; the other two cases its MAXIMUM.
        let want_min = need_upper == e_t.is_positive();
        let mut sum = Rational::zero();
        let mut strict = false;
        let mut reasons = Vec::new();
        let mut seen = ReasonScratch::new(&self.scratch_reason_seen);
        let mut consume =
            |v: u32, e: &Rational, sum: &mut Rational, strict: &mut bool| -> Option<()> {
                let info = self.vars.get(v as usize)?;
                // min(e * x) uses lb(x) for e > 0 and ub(x) for e < 0.
                let use_upper = if want_min {
                    e.is_negative()
                } else {
                    e.is_positive()
                };
                let b = if use_upper {
                    info.upper.as_ref()?
                } else {
                    info.lower.as_ref()?
                };
                if !b
                    .reason_pairs()
                    .filter(|(term, _)| !term.is_sentinel())
                    .all(|(term, val)| self.asserted.get(&term) == Some(&val))
                {
                    return None;
                }
                sum.mul_add_assign(e, &b.value);
                *strict |= b.strict;
                for (term, val) in b.reason_pairs() {
                    if !term.is_sentinel() && seen.insert((term, val)) {
                        reasons.push(TheoryLit::new(term, val));
                    }
                }
                Some(())
            };
        if bv != var {
            consume(bv, &Rational::one(), &mut sum, &mut strict)?;
        }
        for &(v, ref coeff) in &row.coeffs {
            if v == var {
                continue;
            }
            let e = -coeff;
            consume(v, &e, &mut sum, &mut strict)?;
        }
        drop(consume);
        let value = &(&row.constant - &sum) / &e_t;
        Some((reasons, value, strict))
    }

    /// Collect reasons for a variable's implied bound from its tableau row.
    ///
    /// If `var` is a basic variable with row `x_b = c + sum(a_j * x_j)`,
    /// and all nonbasic variables have direct bounds contributing to the
    /// implied bound of `x_b`, collect those direct-bound reasons.
    ///
    /// Returns `true` if all reasons were collected successfully (complete).
    /// Deduplicates reason literals using a shared
    /// `seen` set. This prevents the same reason atom from appearing multiple times
    /// when multiple variables share the same bound reason (#4919).
    ///
    /// When a nonbasic variable lacks a direct bound, recursively searches for
    /// a tableau row defining it as a basic variable and collects transitive
    /// reasons (depth-limited to avoid pathological chains).
    pub(crate) fn collect_row_reasons_dedup(
        &self,
        var: u32,
        need_upper: bool,
        reasons: &mut Vec<TheoryLit>,
        seen: &mut HashSet<(TermId, bool)>,
    ) -> bool {
        // #6617: Try eager explanation first — flat loop, no depth limit.
        let vi = var as usize;
        if vi < self.implied_bounds.len() {
            let ib = if need_upper {
                &self.implied_bounds[vi].1
            } else {
                &self.implied_bounds[vi].0
            };
            if let Some(ib) = ib {
                if let Some(ref expl) = ib.explanation {
                    // reason-alloc-wip: reuse the DFS scratch sets (cleared on
                    // acquire) instead of a per-call HashSet::default().
                    let mut visited_vars = ReasonScratch::new(&self.scratch_reason_visited);
                    // Seed the DFS stack with the ROOT bound being explained:
                    // a chain that transitively cites (var, need_upper) is
                    // self-supporting (cyclic) and must fail closed.
                    let mut on_stack = ReasonScratch::new(&self.scratch_reason_on_stack);
                    on_stack.insert((var, need_upper));
                    if self.collect_reasons_from_explanation(
                        expl,
                        reasons,
                        seen,
                        &mut visited_vars,
                        &mut on_stack,
                    ) {
                        // #8764: Post-collection stale-reason guard.
                        // Backtracking between derivation and reason collection
                        // may retract bound reasons referenced transitively
                        // through the explanation chain. The per-step guard
                        // in collect_reasons_from_explanation checks the
                        // direct bound at each recursion level, but the
                        // recursive implied-bound path (lines 98-110 and
                        // 138-167) can accept reasons via the implied
                        // bound's own explanation without re-validating
                        // that those atoms are still asserted at the top
                        // level. Re-validate the assembled reason set here
                        // so any stale literal forces a clean fallback.
                        if !self.conflict_literals_all_asserted(reasons) {
                            reasons.clear();
                            seen.clear();
                            return false;
                        }
                        return true;
                    }
                    // #8003: Eager path failed (budget exceeded). Return false
                    // instead of falling through to the expensive depth-limited
                    // recursive walker. The caller (make_implied_propagation)
                    // will use the deferred path, which reconstructs reasons
                    // at propagation time via collect_interval_reasons — a
                    // different, cheaper path that walks expression coefficients
                    // with direct-bound lookups.
                    reasons.clear();
                    seen.clear();
                    return false;
                }
            }
        }
        // Fallback: depth-limited recursive walk — only reached when no
        // eager explanation exists (legacy implied bounds or direct bounds).
        // reason-alloc-wip: reuse cleared DFS scratch (the eager block above
        // always returns, so this never coexists with its visited scratch).
        let mut visited_vars = ReasonScratch::new(&self.scratch_reason_visited);
        if self.collect_row_reasons_recursive(var, need_upper, reasons, seen, &mut visited_vars, 0)
        {
            // #8764: Post-collection stale-reason guard. The recursive
            // walker performs per-step direct-bound lookups but does not
            // validate that the final reason set remains fully asserted
            // at return time. Any literal retracted by interleaved
            // backtracking makes the justification unsound.
            if !self.conflict_literals_all_asserted(reasons) {
                reasons.clear();
                seen.clear();
                return false;
            }
            true
        } else {
            false
        }
    }

    // collect_row_reasons_recursive, collect_reasons_from_row_for_basic
    // extracted to implied_row_recursive.rs

    // collect_row_derivation_reasons_lb/ub removed (#6564): these populated
    // eager implied-bound reason snapshots, which were the root cause of
    // stale-reason false-UNSAT. Reasons are collected lazily at propagation
    // time via collect_row_reasons_dedup.

    /// Single-level reason collection from a specific derivation row (#4919).
    /// For an implied bound on `var` derived from `row_idx`, collects direct-bound
    /// reasons from all other variables in the row. Returns `None` if any variable
    /// lacks a direct bound (reason chain would require expensive recursion).
    ///
    /// `need_upper`: the direction of the bound being derived for `var`.
    pub(crate) fn collect_single_row_reasons(
        &self,
        var: u32,
        need_upper: bool,
        row_idx: usize,
    ) -> Option<Vec<TheoryLit>> {
        if row_idx >= self.rows.len() {
            return None;
        }
        let row = &self.rows[row_idx];
        let bv = row.basic_var;
        let is_basic = bv == var;
        let mut reasons = Vec::new();
        // reason-alloc-wip: reuse the cleared `seen` dedup set. `reasons` is the
        // returned value and stays an owned Vec; only `seen` is scratch. This
        // borrows a different cell than collect_row_reasons_dedup's visited/
        // on_stack scratch, so passing `&mut seen` into it cannot self-conflict.
        let mut seen = ReasonScratch::new(&self.scratch_reason_seen);

        if !is_basic {
            // Target is nonbasic: determine sum direction from coefficient
            let var_coeff_pos = match row.coeffs.binary_search_by_key(&var, |(v, _)| *v) {
                Ok(idx) => row.coeffs[idx].1.is_positive(),
                Err(_) => return None,
            };
            let sum_need_upper = var_coeff_pos == need_upper;

            // Basic variable's bound
            let bvi = bv as usize;
            if bvi >= self.vars.len() {
                return None;
            }
            // #8254 fix: If the basic variable has a row-derived implied bound
            // (tighter than direct), using the direct bound's reason is unsound.
            // Return None to force collect_row_reasons_dedup which walks the chain.
            let bv_implied_derived = if bvi < self.implied_bounds.len() {
                let ib = if sum_need_upper {
                    &self.implied_bounds[bvi].1
                } else {
                    &self.implied_bounds[bvi].0
                };
                ib.as_ref()
                    .as_ref()
                    .is_some_and(|b| b.row_idx != usize::MAX)
            } else {
                false
            };
            if bv_implied_derived {
                return None;
            }
            let bv_bound = if sum_need_upper {
                &self.vars[bvi].upper
            } else {
                &self.vars[bvi].lower
            };
            match bv_bound {
                Some(b) => {
                    for (term, val) in b.reason_pairs() {
                        if seen.insert((term, val)) {
                            reasons.push(TheoryLit::new(term, val));
                        }
                    }
                }
                None => {
                    // #6564: Collect implied-bound reasons lazily.
                    if !self.collect_row_reasons_dedup(bv, sum_need_upper, &mut reasons, &mut seen)
                    {
                        return None;
                    }
                }
            }

            // Other nonbasic variables
            for &(nv, ref coeff) in &row.coeffs {
                if nv == var {
                    continue;
                }
                let nvi = nv as usize;
                if nvi >= self.vars.len() {
                    return None;
                }
                let nv_need_upper = coeff.is_positive() != sum_need_upper;
                // #8254 fix: row-derived implied bound check for nonbasic var.
                let nv_implied_derived = if nvi < self.implied_bounds.len() {
                    let ib = if nv_need_upper {
                        &self.implied_bounds[nvi].1
                    } else {
                        &self.implied_bounds[nvi].0
                    };
                    ib.as_ref().is_some_and(|b| b.row_idx != usize::MAX)
                } else {
                    false
                };
                if nv_implied_derived {
                    return None;
                }
                let nv_bound = if nv_need_upper {
                    &self.vars[nvi].upper
                } else {
                    &self.vars[nvi].lower
                };
                match nv_bound {
                    Some(b) => {
                        for (term, val) in b.reason_pairs() {
                            if seen.insert((term, val)) {
                                reasons.push(TheoryLit::new(term, val));
                            }
                        }
                    }
                    None => {
                        // #6564: Collect implied-bound reasons lazily.
                        if !self.collect_row_reasons_dedup(
                            nv,
                            nv_need_upper,
                            &mut reasons,
                            &mut seen,
                        ) {
                            return None;
                        }
                    }
                }
            }
        } else {
            // Target is basic: need all nonbasic vars' bounds
            let sum_need_upper = need_upper;
            for &(nv, ref coeff) in &row.coeffs {
                let nvi = nv as usize;
                if nvi >= self.vars.len() {
                    return None;
                }
                let eq_c_positive = (-coeff).is_positive();
                let nv_need_upper = eq_c_positive != sum_need_upper;
                // #8254 fix: row-derived implied bound check for nonbasic var.
                let nv_implied_derived = if nvi < self.implied_bounds.len() {
                    let ib = if nv_need_upper {
                        &self.implied_bounds[nvi].1
                    } else {
                        &self.implied_bounds[nvi].0
                    };
                    ib.as_ref().is_some_and(|b| b.row_idx != usize::MAX)
                } else {
                    false
                };
                if nv_implied_derived {
                    return None;
                }
                let nv_bound = if nv_need_upper {
                    &self.vars[nvi].upper
                } else {
                    &self.vars[nvi].lower
                };
                match nv_bound {
                    Some(b) => {
                        for (term, val) in b.reason_pairs() {
                            if seen.insert((term, val)) {
                                reasons.push(TheoryLit::new(term, val));
                            }
                        }
                    }
                    None => {
                        // #6564: Collect implied-bound reasons lazily.
                        if !self.collect_row_reasons_dedup(
                            nv,
                            nv_need_upper,
                            &mut reasons,
                            &mut seen,
                        ) {
                            return None;
                        }
                    }
                }
            }
        }

        if reasons.is_empty() {
            return None;
        }
        // #8764: Post-collection stale-reason guard. Row reason collection
        // walks direct bounds and falls back to collect_row_reasons_dedup
        // for variables without direct bounds. Between the lookups and
        // the final return the SAT trail may have retracted atoms, so
        // validate that every reason literal is currently asserted.
        // Mirrors the conflict-layer guard (farkas.rs:293 etc.) and the
        // propagation-layer guard (theory_solver/propagation.rs:975-986).
        if !self.conflict_literals_all_asserted(&reasons) {
            return None;
        }
        Some(reasons)
    }

    /// #8467 Phase 4: Extract reason literals for an implied bound without
    /// wrapping in a PendingPropagation. Used by explain_propagation() for
    /// lazy justification. Returns `None` if eager reason collection fails.
    pub(crate) fn make_eager_implied_propagation_reasons(
        &self,
        var_idx: usize,
        need_upper: bool,
    ) -> Option<Vec<TheoryLit>> {
        let ib = if need_upper {
            self.implied_bounds.get(var_idx)?.1.as_ref()?
        } else {
            self.implied_bounds.get(var_idx)?.0.as_ref()?
        };
        let explanation = ib.explanation.as_ref()?;
        // #8452/#8256: Removed max_row_width > 50 guard that prevented eager
        // reason collection on dense LP benchmarks (rand_70_300, vpm2-30,
        // tsp_rand, ecoliMILP). When this guard fires, ALL implied bound
        // propagations fall back to DeferredReason::ImpliedBound, which
        // propagate_impl()'s semantic re-verification filter then rejects
        // (97.7% rejection rate on sc-6). Without propagations, the SAT
        // solver makes 10-100x more decisions than Z3 (which does 56K bound
        // propagations on the same benchmarks). The contributing_vars budget
        // is kept to bound worst-case reason collection cost.
        if explanation.contributing_vars.len() > 200 {
            return None;
        }
        let mut reasons = Vec::new();
        // reason-alloc-wip: reuse cleared DFS scratch instead of per-call
        // HashSet::default(). `reasons` is returned and stays an owned Vec.
        let mut seen = ReasonScratch::new(&self.scratch_reason_seen);
        let mut visited_vars = ReasonScratch::new(&self.scratch_reason_visited);
        // Seed the DFS stack with the ROOT bound being explained: a chain
        // that transitively cites (var_idx, need_upper) is self-supporting
        // (cyclic) and must fail closed (false-UNSAT otherwise; _hhk2008).
        let mut on_stack = ReasonScratch::new(&self.scratch_reason_on_stack);
        on_stack.insert((var_idx as u32, need_upper));
        if self.collect_reasons_from_explanation(
            explanation,
            &mut reasons,
            &mut seen,
            &mut visited_vars,
            &mut on_stack,
        ) && !reasons.is_empty()
        {
            // #8764: Post-collection stale-reason guard. Mirrors
            // collect_row_reasons_dedup — validate every literal is
            // asserted before handing the reason set to the propagation
            // layer; stale justifications would otherwise leak into
            // learned clauses and cause false UNSAT.
            if !self.conflict_literals_all_asserted(&reasons) {
                return None;
            }
            return Some(reasons);
        }
        None
    }

    /// #8008: Build a propagation for an implied bound using eager-only reason
    /// collection. Returns `None` if eager reason collection fails, which means
    /// the propagation is silently dropped rather than using the unsafe deferred
    /// `DeferredReason::ImpliedRow` fallback that walks tableau rows at
    /// reason-collection time (producing stale reasons after basis changes).
    ///
    /// This is the soundness-safe replacement for `make_implied_propagation`.
    /// Z3's new solver (arith_solver.h) uses UINT_MAX for its propagation cap
    /// and never disables bound propagation. The eager-only approach trades a
    /// small number of missed propagations for guaranteed soundness.
    #[allow(dead_code)]
    pub(crate) fn make_eager_implied_propagation(
        &self,
        literal: TheoryLit,
        _var_idx: usize,
        need_upper: bool,
    ) -> Option<PendingPropagation> {
        // #8467: Convert to lazy justification. Instead of eagerly collecting
        // reasons from the BoundExplanation (which allocates Vec<TheoryLit>
        // for every propagation), use the interval-based lazy encoding.
        // explain_propagation() will reconstruct via collect_interval_reasons()
        // only when the reason is actually needed (~10% of propagations).
        //
        // The atom_cache lookup and for_upper flag are encoded in reason_data
        // with bit 63=1 (interval encoding). Previously this eagerly collected
        // from BoundExplanation.contributing_vars with O(vars * Rational_cmp).
        let atom_term = literal.term;
        // Verify the atom is in atom_cache before emitting lazy propagation.
        self.atom_cache.get(&atom_term).and_then(|v| v.as_ref())?;
        // Determine for_upper: the reason bound direction depends on what
        // we are proving. For implied upper bounds proving an upper-bound
        // atom true, for_upper=true. For implied lower bounds proving a
        // lower-bound atom true, for_upper=false.
        let for_upper = need_upper;
        let reason_data = u64::from(atom_term.0)
            | (if for_upper { 1u64 << 32 } else { 0 })
            | (if literal.value { 1u64 << 33 } else { 0 })
            | (1u64 << 63);
        Some(PendingPropagation {
            propagation: TheoryPropagation {
                literal,
                reason: Vec::new(),
                reason_data: Some(reason_data),
            },
            deferred: None,
        })
    }

    /// #8064: Build a propagation for an implied bound, trying lazy
    /// justification first and falling back to a deferred token.
    ///
    /// #8467: Converted the eager single-row reason path to lazy justification.
    /// Instead of calling collect_single_row_reasons() which iterates O(row_width)
    /// variables with Rational comparisons, use the interval-based lazy encoding.
    /// The reason is only materialized via explain_propagation() during conflict
    /// analysis when the variable is actually resolved (~10% of propagations).
    ///
    /// The deferred fallback ensures the propagation is still queued when the
    /// atom is not in atom_cache.
    #[allow(dead_code)]
    pub(crate) fn make_implied_propagation(
        &self,
        literal: TheoryLit,
        var: u32,
        need_upper: bool,
        row_idx: usize,
    ) -> PendingPropagation {
        // #8467: Try lazy justification via interval encoding first.
        // This is O(1) at propagation time — just pack atom_term + for_upper
        // into reason_data. explain_propagation() reconstructs the full reason
        // via collect_interval_reasons() only when needed.
        let atom_term = literal.term;
        if self
            .atom_cache
            .get(&atom_term)
            .and_then(|v| v.as_ref())
            .is_some()
        {
            let for_upper = need_upper;
            let reason_data = u64::from(atom_term.0)
                | (if for_upper { 1u64 << 32 } else { 0 })
                | (if literal.value { 1u64 << 33 } else { 0 })
                | (1u64 << 63);
            return PendingPropagation {
                propagation: TheoryPropagation {
                    literal,
                    reason: Vec::new(),
                    reason_data: Some(reason_data),
                },
                deferred: None,
            };
        }
        // Fallback: atom not in atom_cache. Use deferred ImpliedRow which
        // propagate_impl() materializes via compute_expr_interval.
        // Reference: Z3 defers reason collection via lambda capture
        // (bound_analyzer_on_row.h:301-318).
        PendingPropagation::deferred(
            literal,
            DeferredReason::ImpliedRow {
                var,
                need_upper,
                fallback_row_idx: Some(row_idx),
            },
        )
    }
}
