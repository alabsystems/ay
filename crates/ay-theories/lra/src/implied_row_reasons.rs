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
    /// Collect reasons using eagerly-stored explanation data (#6617).
    /// See `implied_bounds.rs::collect_reasons_from_explanation` for docs.
    ///
    /// #8003: Added `max_vars_budget` parameter to bound total work on dense LPs.
    /// When `visited_vars` exceeds the budget, returns false to signal that
    /// eager reason collection is too expensive and should be abandoned.
    /// Callers fall back to deferred reason collection or skip the propagation.
    /// Soundness (#cyclic-explanation false-UNSAT): `on_stack` holds the
    /// (var, direction) pairs whose implied-bound explanation is CURRENTLY
    /// being resolved on this DFS path (gray nodes), seeded with the root
    /// bound being explained. Implied-bound cascades store only
    /// (var, direction) in `BoundExplanation` — not the derivation
    /// generation — so re-walking the chains against CURRENT bounds can hit
    /// a cycle (e.g. implied_ub(x) cites implied_lb(y) and implied_lb(y)
    /// cites implied_ub(x); each was derived from the other's EARLIER-round
    /// value). Previously a back edge was silently skipped via
    /// `visited_vars`, DROPPING the antecedent entirely and producing an
    /// over-strong reason clause (observed on _hhk2008 bpl_7/bpl_8: reason
    /// set collapsed to one unrelated fringe atom => false UNSAT). A back
    /// edge means the justification is circular and cannot be grounded on
    /// this path: fail closed (return false) so the caller falls back to
    /// another strategy or drops the propagation. Re-encounters of nodes
    /// FULLY explained earlier (black: in `visited_vars` but not
    /// `on_stack`) remain safe to skip — their reasons are already
    /// collected.
    pub(crate) fn collect_reasons_from_explanation(
        &self,
        explanation: &BoundExplanation,
        reasons: &mut Vec<TheoryLit>,
        seen: &mut HashSet<(TermId, bool)>,
        visited_vars: &mut HashSet<(u32, bool)>,
        on_stack: &mut HashSet<(u32, bool)>,
    ) -> bool {
        // #8003/#8452: Budget guard. Each contributing_var iteration does
        // Rational comparisons (potential bignum) and may recurse. On
        // benchmarks with many implied-bound chains, unbounded recursion
        // produces O(depth^width) work.
        //
        // Raised from 40 to 500 (#8452): The old budget of 40 was too low
        // for dense LP benchmarks (rand_70_300 with 70+ vars per row). A
        // single row derivation visits all contributing variables (row width),
        // and with row width > 40, the budget was exceeded on the first level,
        // causing ALL implied bound propagations to fail reason collection.
        // This produced 0 theory propagations (vs Z3's 56K), making the
        // SAT solver rely entirely on decisions.
        //
        // Cost: 500 * O(Rational_cmp) per propagation. With ~5K propagations
        // per solve, this adds at most ~1s total. The alternative (0 propagations)
        // causes timeouts on all dense LP benchmarks.
        //
        // Reference: Z3 defers reason collection entirely (u_dependency in
        // bound_analyzer_on_row.h), avoiding this cost at derivation time.
        const MAX_VISITED: usize = 500;
        if visited_vars.len() >= MAX_VISITED {
            return false;
        }
        for &(var, used_upper) in &explanation.contributing_vars {
            // Cycle (gray back edge): this bound is currently being explained
            // higher on the DFS path — the justification is circular. Fail
            // closed; silently skipping would drop a real antecedent.
            if on_stack.contains(&(var, used_upper)) {
                return false;
            }
            if !visited_vars.insert((var, used_upper)) {
                continue;
            }
            let vi = var as usize;
            let info = match self.vars.get(vi) {
                Some(i) => i,
                None => return false,
            };
            let direct = if used_upper { &info.upper } else { &info.lower };

            // #8254 fix: compute_implied_bounds() derives bounds using
            // self.implied_bounds[vi] (the tighter of direct and row-derived).
            // The old code unconditionally used the direct bound if it existed,
            // even if the implied bound was tighter. This produces unsound theory
            // lemmas: the reason references a weaker bound than what was actually
            // used in the derivation. Fix: check if the implied bound is strictly
            // tighter; if so, recurse through the implied bound's explanation chain.
            let implied = if vi < self.implied_bounds.len() {
                if used_upper {
                    self.implied_bounds[vi].1.as_ref()
                } else {
                    self.implied_bounds[vi].0.as_ref()
                }
            } else {
                None
            };

            // #8003: Fast-path for dense LPs. If the implied bound slot holds
            // a direct bound overlay (row_idx == usize::MAX), it cannot be
            // tighter than `direct` — skip the expensive Rational comparison.
            // Row-derived bounds (row_idx != usize::MAX) require the full check
            // for soundness (#8254).
            let implied_is_tighter = match (direct, implied) {
                (Some(direct_b), Some(ib)) if ib.row_idx != usize::MAX => {
                    if used_upper {
                        ib.value < direct_b.value
                            || (ib.value == direct_b.value && ib.strict && !direct_b.strict)
                    } else {
                        ib.value > direct_b.value
                            || (ib.value == direct_b.value && ib.strict && !direct_b.strict)
                    }
                }
                _ => false,
            };

            if implied_is_tighter {
                match implied {
                    Some(ib) if ib.explanation.is_some() => {
                        on_stack.insert((var, used_upper));
                        let ok = self.collect_reasons_from_explanation(
                            ib.explanation.as_ref().unwrap(),
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
            } else if let Some(bound) = direct {
                // #8511 soundness fix: Before using direct bound reasons,
                // verify ALL non-sentinel reason atoms are still asserted.
                // Between derivation time and reason-collection time, the
                // SAT solver may have backtracked, retracting some direct
                // bound assertions. If that happens, the direct bound's
                // reasons no longer form a valid justification. In that case,
                // fall back to the implied bound's explanation chain (if
                // available), which traces through a different derivation path
                // that may still have asserted reasons.
                //
                // This is the root cause of #8511: collect_reasons_from_explanation
                // was using direct bound reasons even when the direct bound had
                // been retracted (making those reason atoms unasserted), producing
                // syntactically-valid but semantically-wrong reason sets.
                let all_direct_asserted = bound
                    .reason_pairs()
                    .filter(|(term, _)| !term.is_sentinel())
                    .all(|(term, val)| self.asserted.get(&term) == Some(&val));

                if all_direct_asserted {
                    for (term, val) in bound.reason_pairs() {
                        if !term.is_sentinel() && seen.insert((term, val)) {
                            reasons.push(TheoryLit::new(term, val));
                        }
                    }
                } else {
                    // Direct bound retracted — try implied bound chain.
                    match implied {
                        Some(ib) if ib.explanation.is_some() => {
                            on_stack.insert((var, used_upper));
                            let ok = self.collect_reasons_from_explanation(
                                ib.explanation.as_ref().unwrap(),
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
            } else {
                match implied {
                    Some(ib) if ib.explanation.is_some() => {
                        on_stack.insert((var, used_upper));
                        let ok = self.collect_reasons_from_explanation(
                            ib.explanation.as_ref().unwrap(),
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
        }
        true
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
