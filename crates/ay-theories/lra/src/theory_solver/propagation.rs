// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Propagation pipeline for the LRA theory solver.

use super::*;

impl LraSolver {
    /// Drop any propagation that cannot be soundly justified, BEFORE its literal
    /// reaches the SAT trail.
    ///
    /// Two unsound shapes are rejected here:
    ///
    /// 1. Circular / tautological reason — the reason references the propagated
    ///    atom's own term, producing the reason clause
    ///    `(propagated \/ ... \/ ¬propagated \/ ...)`. This tautology does not
    ///    justify the propagation, and storing it as a propagation reason
    ///    injects a duplicate-variable clause into the SAT clause database,
    ///    corrupting the two-watched-literal invariant (debug: trips the
    ///    duplicate-variable canary in replace_clause_checked / vivify during
    ///    the next level-0 GC; release: silent wrong UNSAT).
    ///
    /// 2. Over-tight implied bound — a lazy ImpliedBound propagation whose
    ///    reconstructed reason is syntactically valid (all premises asserted, no
    ///    self-reference) but does NOT actually prove the propagated literal
    ///    under the direct (asserted) bounds (#8754 shape). Such a propagation
    ///    forces a literal the reasons cannot defend, leading to false UNSAT.
    ///
    /// Validating eagerly (rather than only at conflict-analysis materialization
    /// time, where `explain_propagation` already returns `None` for the same
    /// cases) is soundness-critical: an unsound propagation that reaches the
    /// trail has already pruned valid assignments by the time conflict analysis
    /// would discover the bad reason. Dropping a propagation is always sound (it
    /// only forgoes a deduction), so over-dropping at worst costs completeness,
    /// never soundness.
    fn filter_unsound_propagations(&mut self, propagations: &mut Vec<TheoryPropagation>) {
        // Validate every propagation BEFORE its literal can be placed on the SAT
        // trail, and drop any whose reason cannot be soundly justified. Doing
        // this eagerly (rather than only at conflict-analysis materialization
        // time via explain_propagation -> None) is soundness-critical: an
        // unsound propagation that reaches the trail prunes valid assignments
        // and can produce false UNSAT, and a circular (tautological) reason also
        // injects a duplicate-variable clause into the SAT clause database,
        // corrupting the two-watched-literal invariant.
        //
        // We cannot use Vec::retain alone because the lazy reconstruction needs
        // `&self` while retain's closure already borrows the element; build a
        // keep-mask first, then drop.
        let mut keep: Vec<bool> = Vec::with_capacity(propagations.len());
        let mut dropped = 0u64;
        for prop in propagations.iter() {
            let valid = if prop.is_lazy() {
                match prop.reason_data {
                    Some(rd) => self.lazy_propagation_is_sound(&prop.literal, rd),
                    // No reason_data and no eager reason: cannot justify.
                    None => false,
                }
            } else {
                // Eager reason: must be non-empty and not self-referential.
                let self_term = prop.literal.term;
                !prop.reason.is_empty() && !prop.reason.iter().any(|r| r.term == self_term)
            };
            keep.push(valid);
            if !valid {
                dropped += 1;
            }
        }
        if dropped > 0 {
            let mut i = 0;
            propagations.retain(|prop| {
                let k = keep[i];
                i += 1;
                if !k {
                    self.propagated_atoms
                        .remove(&(prop.literal.term, prop.literal.value));
                }
                k
            });
            self.stats.stale_reason_filtered_count += dropped;
        }
    }

    /// Side-effect-free soundness check for a lazy theory propagation.
    ///
    /// Reconstructs the reason that the DPLL layer would materialize during
    /// conflict analysis (via `explain_propagation_inner`) and verifies that it
    /// genuinely justifies the propagated literal:
    ///   * a reason can be reconstructed at all,
    ///   * the reason does not reference the propagated atom's own term
    ///     (circular / tautological reason), and
    ///   * every reason literal is currently asserted (sound, falsified premise).
    ///
    /// If any condition fails, the propagation is unsound to place on the trail
    /// and must be dropped at the source. This mirrors the rejection performed
    /// at materialization time in `explain_propagation`, but applied eagerly so
    /// the unsound assignment never reaches the SAT trail in the first place.
    fn lazy_propagation_is_sound(&self, lit: &TheoryLit, reason_data: u64) -> bool {
        let self_term = lit.term;
        let reason = match self.explain_propagation_inner(self_term, reason_data) {
            Some(r) => r,
            None => return false,
        };
        if reason.is_empty() {
            return false;
        }
        // Circular / tautological reason (references the propagated atom).
        if reason.iter().any(|r| r.term == self_term) {
            return false;
        }
        // Every reason literal must be an asserted (falsified-premise) fact.
        if !reason
            .iter()
            .all(|r| self.asserted.get(&r.term) == Some(&r.value))
        {
            return false;
        }
        // Freshness / entailment gate for lazy ImpliedBound propagations.
        //
        // An ImpliedBound propagation concludes a derived (row-computed) bound on
        // the propagated variable. Its reconstructed reason can be syntactically
        // valid (premises asserted, no self-reference) yet still NOT entail the
        // propagation once the implied bound that justified it goes STALE: the
        // tableau may move (simplex pivots, new direct bounds) between the
        // propagation's enqueue (check() time) and this drain. A stale propagation
        // forces a literal the current state no longer supports; when conflict
        // analysis resolves through it the SAT layer learns an over-constrained
        // clause and can report false UNSAT. On _hhk2008 the stale reason also
        // becomes circular under SAT-variable aliasing — which is what injected the
        // duplicate-variable / tautological reason clause into the SAT database.
        //
        // Re-verify entailment against the FRESHLY recomputed implied bound on the
        // propagating variable. This filter runs at the end of propagate_impl(),
        // AFTER compute_implied_bounds() has refreshed `implied_bounds`, so the
        // check reflects the present tableau. A genuinely row-derivable
        // propagation (whose implied bound is current) still passes — preserving
        // legitimate single-row / cascade implied-bound propagation, exercised by
        // the propagation_regression tests — while a stale one is dropped.
        // Dropping a propagation is always sound.
        //
        // Scope to ImpliedBound reasons (bit62=1, bit63=0). DirectBound reasons
        // come straight from an asserted bound (sound by construction); Interval
        // reasons (bit63=1) are eagerly materialized and verified elsewhere.
        let is_interval = (reason_data >> 63) & 1 != 0;
        let is_implied = !is_interval && ((reason_data >> 62) & 1 != 0);
        if is_implied {
            let var = (reason_data & 0xFFFF_FFFF) as u32;
            let need_upper = (reason_data >> 32) & 1 != 0;
            if !self.implied_bound_still_implies(var, need_upper, lit) {
                return false;
            }
        }
        true
    }

    /// Whether the propagated literal `lit` is still entailed by the FRESHLY
    /// recomputed implied bound on `var` (upper if `need_upper`, else lower).
    ///
    /// Computes the propagated atom's expression interval using direct bounds for
    /// every variable, except that for the propagating variable `var` it
    /// substitutes the current `implied_bounds[var]` overlay (the bound the
    /// propagation was derived from). If the resulting interval still implies the
    /// literal, the implied bound is live and the propagation is sound to keep;
    /// otherwise the bound is stale (or no longer present) and the propagation is
    /// dropped. This preserves genuine row-derived propagation while rejecting the
    /// stale, false-UNSAT-inducing propagations seen on _hhk2008.
    fn implied_bound_still_implies(&self, var: u32, need_upper: bool, lit: &TheoryLit) -> bool {
        let vi = var as usize;
        // The fresh implied bound must currently exist.
        let Some((lower_ib, upper_ib)) = self.implied_bounds.get(vi) else {
            return false;
        };
        let ib = if need_upper {
            upper_ib.as_ref()
        } else {
            lower_ib.as_ref()
        };
        let Some(ib) = ib else {
            return false;
        };
        let Some(Some(info)) = self.atom_cache.get(&lit.term) else {
            return false;
        };
        // Compute the atom expression interval, using the fresh implied bound for
        // `var` and direct bounds for the rest. Mirrors compute_expr_interval's
        // direction handling (c>0 vs c<0; upper vs lower accumulation).
        let mut lb = info.expr.constant.clone();
        let mut ub = info.expr.constant.clone();
        let mut lb_finite = true;
        let mut ub_finite = true;
        let mut lb_strict = false;
        let mut ub_strict = false;
        for &(v, ref coeff) in &info.expr.coeffs {
            let vj = v as usize;
            if vj >= self.vars.len() {
                return false;
            }
            // Resolve the (lb, ub) endpoints to use for this variable. For the
            // propagating var, override the relevant side with the fresh implied
            // bound; for the rest use direct bounds only.
            let vinfo = &self.vars[vj];
            let direct_lb = vinfo.lower.as_ref().map(|b| (b.value.clone(), b.strict));
            let direct_ub = vinfo.upper.as_ref().map(|b| (b.value.clone(), b.strict));
            let (use_lb, use_ub) = if v == var {
                let implied = (ib.value.clone(), ib.strict);
                if need_upper {
                    (direct_lb, Some(implied))
                } else {
                    (Some(implied), direct_ub)
                }
            } else {
                (direct_lb, direct_ub)
            };
            if coeff.is_positive() {
                if ub_finite {
                    match &use_ub {
                        Some((bv, strict)) => {
                            ub.mul_add_assign(coeff, bv);
                            ub_strict |= *strict;
                        }
                        None => ub_finite = false,
                    }
                }
                if lb_finite {
                    match &use_lb {
                        Some((bv, strict)) => {
                            lb.mul_add_assign(coeff, bv);
                            lb_strict |= *strict;
                        }
                        None => lb_finite = false,
                    }
                }
            } else {
                if ub_finite {
                    match &use_lb {
                        Some((bv, strict)) => {
                            ub.mul_add_assign(coeff, bv);
                            ub_strict |= *strict;
                        }
                        None => ub_finite = false,
                    }
                }
                if lb_finite {
                    match &use_ub {
                        Some((bv, strict)) => {
                            lb.mul_add_assign(coeff, bv);
                            lb_strict |= *strict;
                        }
                        None => lb_finite = false,
                    }
                }
            }
            if !lb_finite && !ub_finite {
                break;
            }
        }
        let lb_ep = lb_finite.then(|| IntervalEndpoint::new(lb, lb_strict));
        let ub_ep = ub_finite.then(|| IntervalEndpoint::new(ub, ub_strict));
        let is_le = info.is_le;
        let strict = info.strict;
        if lit.value {
            if is_le {
                ub_ep
                    .as_ref()
                    .is_some_and(|ep| Self::endpoint_implies_le_zero(ep, strict))
            } else {
                lb_ep
                    .as_ref()
                    .is_some_and(|ep| Self::endpoint_implies_ge_zero(ep, strict))
            }
        } else if is_le {
            lb_ep
                .as_ref()
                .is_some_and(|ep| Self::endpoint_implies_not_le_zero(ep, strict))
        } else {
            ub_ep
                .as_ref()
                .is_some_and(|ep| Self::endpoint_implies_not_ge_zero(ep, strict))
        }
    }

    pub(super) fn propagate_impl(&mut self) -> Vec<TheoryPropagation> {
        // #8319: AY_NO_THEORY_PROPAGATION disables all LRA propagations.
        if self.no_theory_propagation {
            self.pending_propagations.clear();
            self.propagation_dirty_vars.clear();
            return Vec::new();
        }
        // #8608: Reuse persistent buffer — clear() preserves capacity from prior calls.
        let mut propagations = std::mem::take(&mut self.propagation_output_buf);
        propagations.clear();
        // Drain same-variable chain propagations computed in check().
        // Slack variables are filtered at the source (propagate_var_atoms,
        // compute_bound_propagations, implied bounds) via slack_var_set (#6242).
        let pending: Vec<PendingPropagation> = std::mem::take(&mut self.pending_propagations);
        let pending_count = pending.len();
        let mut seen = std::mem::take(&mut self.reason_seen_buf);
        seen.clear();
        // #8064: Removed retained_dirty mechanism that permanently kept all
        // compound-use variables in propagation_dirty_vars. This caused O(N)
        // wasted work per propagation call on QF_LRA instances with many
        // compound atoms (e.g., 404 dirty vars scanned every call, finding 0
        // propagations). Compound variables are properly re-dirtied when their
        // bounds change via compute_implied_bounds() or assert_literal().
        for p in pending {
            let mut prop = p.propagation;
            if let Some(deferred) = p.deferred {
                match deferred {
                    DeferredReason::DirectBound { var, need_upper } => {
                        // #8511 fix: Eagerly materialize DirectBound reasons.
                        //
                        // Previously used lazy justification (reason_data set,
                        // reason empty). But the stale-reason retain filter at
                        // the end of propagate_impl() rejects all propagations
                        // with empty reasons, so DirectBound lazy propagations
                        // were silently dropped — causing false-UNSAT.
                        //
                        // Now eagerly collect reason_pairs() into prop.reason.
                        let vi = var as usize;
                        let mut emitted_db = false;
                        if let Some(info) = self.vars.get(vi) {
                            let bound = if need_upper {
                                info.upper.as_ref()
                            } else {
                                info.lower.as_ref()
                            };
                            if let Some(b) = bound {
                                let reason: Vec<TheoryLit> = b
                                    .reason_pairs()
                                    .filter(|(term, _)| !term.is_sentinel())
                                    .filter(|(term, val)| self.asserted.get(term) == Some(val))
                                    .map(|(term, val)| TheoryLit::new(term, val))
                                    .collect();
                                let total_non_sentinel = b
                                    .reason_pairs()
                                    .filter(|(term, _)| !term.is_sentinel())
                                    .count();
                                if !reason.is_empty() && reason.len() == total_non_sentinel {
                                    prop.reason = reason;
                                    self.propagated_atoms
                                        .insert((prop.literal.term, prop.literal.value));
                                    self.stats.emitted_direct_count += 1;
                                    propagations.push(prop);
                                    emitted_db = true;
                                }
                            }
                        }
                        if !emitted_db {
                            // Bound retracted or stale — skip.
                        }
                        continue;
                    }
                    DeferredReason::ImpliedRow { .. } => {
                        // #7935 / #6242: Deferred row-reason materialization is DISABLED.
                        //
                        // Row-walking at propagation time is unsound because the simplex
                        // basis may have changed between check() and propagate(). Instead,
                        // try to reconstruct the reason from the current variable-interval
                        // bounds via compute_expr_interval + collect_interval_reasons.
                        // #8599: Compute interval + collect reasons while
                        // holding only a shared borrow on atom_cache; release
                        // the borrow before mutating self fields.
                        let emitted = 'interval: {
                            let atom_term = prop.literal.term;
                            let reason = {
                                let Some(Some(info)) = self.atom_cache.get(&atom_term) else {
                                    break 'interval false;
                                };
                                let is_le = info.is_le;
                                let strict = info.strict;
                                let (lb, ub) = self.compute_expr_interval(&info.expr);
                                let implied_true = if prop.literal.value {
                                    if is_le {
                                        ub.as_ref().is_some_and(|ep| {
                                            Self::endpoint_implies_le_zero(ep, strict)
                                        })
                                    } else {
                                        lb.as_ref().is_some_and(|ep| {
                                            Self::endpoint_implies_ge_zero(ep, strict)
                                        })
                                    }
                                } else if is_le {
                                    lb.as_ref().is_some_and(|ep| {
                                        Self::endpoint_implies_not_le_zero(ep, strict)
                                    })
                                } else {
                                    ub.as_ref().is_some_and(|ep| {
                                        Self::endpoint_implies_not_ge_zero(ep, strict)
                                    })
                                };
                                if !implied_true {
                                    break 'interval false;
                                }
                                let for_upper = if prop.literal.value { is_le } else { !is_le };
                                let reason = self.collect_interval_reasons(&info.expr, for_upper);
                                if reason.is_empty() {
                                    break 'interval false;
                                }
                                reason
                            };
                            // Shared borrow on atom_cache is now released.
                            prop.reason = reason;
                            self.stats.deferred_reason_count += 1;
                            self.stats.emitted_implied_row_count += 1;
                            self.propagated_atoms
                                .insert((prop.literal.term, prop.literal.value));
                            propagations.push(prop);
                            true
                        };
                        if !emitted {
                            continue;
                        }
                    }
                    DeferredReason::Interval {
                        atom_term,
                        for_upper: _,
                    } => {
                        // #8151 Phase 3: Materialize interval reason at drain time.
                        // #8511 soundness fix: Re-verify interval before collecting reasons.
                        let lit = prop.literal;
                        // #8599: Scope atom_cache borrow to avoid cloning LinearExpr.
                        let emitted = 'interval_mat: {
                            if !self.verify_interval_still_implied(&prop.literal) {
                                break 'interval_mat false;
                            }
                            let reason = {
                                let Some(Some(info)) = self.atom_cache.get(&atom_term) else {
                                    break 'interval_mat false;
                                };
                                let is_le = info.is_le;
                                let for_upper = if prop.literal.value { is_le } else { !is_le };
                                let reason = self.collect_interval_reasons(&info.expr, for_upper);
                                if reason.is_empty() {
                                    break 'interval_mat false;
                                }
                                reason
                            };
                            prop.reason = reason;
                            self.stats.deferred_interval_count += 1;
                            Self::note_propagated(
                                &mut self.propagated_atoms,
                                &mut self.propagated_trail,
                                lit.term,
                                lit.value,
                            );
                            propagations.push(prop);
                            true
                        };
                        if !emitted {
                            continue;
                        }
                    }
                    DeferredReason::ImpliedBound { var, need_upper } => {
                        // #8467/#9704: Lazy justification for ImpliedBound propagations.
                        //
                        // Instead of eagerly materializing the reason here (which
                        // involves BoundExplanation chain walking, single-row reason
                        // collection, and interval fallbacks), emit a lazy propagation
                        // with a compact reason_data tag. The DPLL layer will call
                        // explain_propagation() only when the reason is actually
                        // needed during conflict analysis (~90% never need it).
                        //
                        // This eliminates the per-propagation O(contributing_vars)
                        // reason collection that was the primary bottleneck identified
                        // in issue #8467 (285x per-propagation overhead vs Z3).
                        //
                        // Encoding: bit62=1 (implied), bit33=polarity,
                        // bit32=need_upper, bits0-31=var.
                        let polarity_bit = if prop.literal.value { 1u64 << 33 } else { 0 };
                        let upper_bit = if need_upper { 1u64 << 32 } else { 0 };
                        let reason_data = (1u64 << 62) | polarity_bit | upper_bit | u64::from(var);
                        prop.reason_data = Some(reason_data);
                        self.stats.lazy_emitted_count += 1;
                        self.stats.emitted_implied_count += 1;
                        self.propagated_atoms
                            .insert((prop.literal.term, prop.literal.value));
                        propagations.push(prop);
                    }
                }
            } else if prop.is_lazy() {
                // #8467/#9704: Lazy propagations pass through to the DPLL layer.
                //
                // DirectBound (bit62=0, bit63=0) and ImpliedBound (bit62=1)
                // lazy propagations are materialized on demand via
                // explain_propagation() during conflict analysis. ~90% of
                // propagations never need their reasons materialized.
                //
                // Interval (bit63=1) lazy propagations are eagerly materialized
                // because they depend on compute_expr_interval state that can
                // change with basis pivots.
                if let Some(reason_data) = prop.reason_data {
                    let is_interval = (reason_data >> 63) & 1 != 0;
                    if is_interval {
                        // Interval: must eagerly materialize (state-dependent).
                        if let Some(reason) =
                            self.eagerly_materialize_reason_data(reason_data, &prop.literal)
                        {
                            prop.reason = reason;
                            prop.reason_data = None;
                            self.stats.eager_reason_count += 1;
                            self.propagated_atoms
                                .insert((prop.literal.term, prop.literal.value));
                            propagations.push(prop);
                        } else {
                            self.propagated_atoms
                                .remove(&(prop.literal.term, prop.literal.value));
                        }
                    } else {
                        // DirectBound or ImpliedBound: pass through as lazy.
                        self.propagated_atoms
                            .insert((prop.literal.term, prop.literal.value));
                        propagations.push(prop);
                    }
                } else {
                    self.propagated_atoms
                        .remove(&(prop.literal.term, prop.literal.value));
                }
            } else if !prop.reason.is_empty() {
                self.stats.eager_reason_count += 1;
                propagations.push(prop);
            }
        }
        self.reason_seen_buf = seen;

        // #8553: Propagation is always active. Z3's new solver sets
        // arith_propagation_threshold = UINT_MAX (never disables propagation).
        // AY matches this: no conflict-count gating on bound propagation.

        // #6987: Refresh simplex feasibility before propagate-time row analysis.
        // Z3's propagate_core() calls make_feasible() before deriving LP-backed
        // implications. Without this, compute_implied_bounds() runs against a
        // stale basis when BCP tightens bounds between check() calls.
        //
        // #6256: If the refresh fails (infeasible), skip interval propagation —
        // variable values are stale and would compute incorrect implied bounds.
        // check() will report the actual conflict on the next round.
        // #8422: Track whether refresh_simplex_for_propagate ran simplex.
        // If it did, the pivots may have seeded touched_rows that contain
        // new implied bound derivation opportunities. Previously, the
        // implied_bounds_fresh flag blocked reprocessing these rows, and
        // the propagate_direct_touched_rows_pending flag was not re-armed.
        // This lost transitive bound derivations from simplex pivots.
        //
        // Root cause: Z3's propagate_core() calls make_feasible() then
        // immediately runs propagate_bounds_for_touched_rows() on the same
        // rows touched by pivots. AY's architecture separates check() and
        // propagate(), creating a gap where refresh-simplex-touched rows
        // were skipped.
        let had_pending_simplex = self.bounds_tightened_since_simplex;
        if !self.refresh_simplex_for_propagate() {
            self.propagation_dirty_vars.clear();
            // #8608/#8599: Transfer ownership instead of drain+collect.
            self.propagation_output_buf = propagations;
            return std::mem::take(&mut self.propagation_output_buf);
        }
        // #8422: After refresh simplex ran pivots, ensure the cascade
        // processes the newly-touched rows. This was previously blocked
        // by implied_bounds_fresh + stale propagate_direct_touched_rows_pending.
        if had_pending_simplex && !self.touched_rows.is_empty() {
            self.propagate_direct_touched_rows_pending = true;
            self.implied_bounds_fresh = false;
            self.direct_bounds_changed_since_implied = true;
        }

        // #6617 Packet 1: Run compute_implied_bounds during propagation when
        // rows are touched by BCP atom assertions. This restores the tighter
        // BCP -> theory -> BCP feedback loop that regressed out of current
        // HEAD during the lib.rs / module extraction churn.
        //
        // Reference: Z3 theory_lra.cpp:2206-2271, lar_solver.h:281-301
        //
        // Z3 runs touched-row analysis whenever rows are activated; skipping
        // small row sets strands single-row cascades until the next check()
        // round and leaves the main sc-* path on the slower check-time lane.
        //
        // #8468: Skip when implied_bounds_fresh is set AND no new basis changes
        // occurred (bounds_tightened_since_simplex is false). This means
        // check_during_propagate already ran compute_implied_bounds on the same
        // tableau state, so rerunning it would produce identical results.
        // When bounds_tightened_since_simplex is true, new direct bounds arrived
        // (from propagation assertions) and a fresh implied bounds pass is needed.
        let skip_for_freshness = self.implied_bounds_fresh && !self.bounds_tightened_since_simplex;
        if self.propagate_direct_touched_rows_pending
            && !self.touched_rows.is_empty()
            && !skip_for_freshness
        {
            // #7853: Snapshot touched rows using persistent buffer instead of clone.
            // Avoids per-propagate() HashSet heap allocation.
            self.touched_rows_snapshot_buf.clear();
            self.touched_rows_snapshot_buf
                .extend(self.touched_rows.iter());
            // #8422: Fixpoint loop for cascade derivation during propagate().
            // Previously, only a single compute_implied_bounds() call ran here,
            // missing multi-hop cascades (e.g., bound on X enables Y's row to
            // derive bound on Z). The check() path already has a fixpoint loop
            // (check_atoms.rs:714), but propagate() did not. Z3 achieves cascade
            // derivation via its SAT-theory feedback loop (BCP -> unit_propagate()
            // -> BCP -> ...), but AY's architecture requires the fixpoint internally.
            //
            // #8256: Increased from 3 to 6. The propagation-time fixpoint
            // must be deep enough for transitive bound chains (e.g.,
            // x_3 <= x_4 <= x_5 <= ...) that arise in simple_startup
            // benchmarks. Z3 has no explicit cap; its SAT-theory feedback
            // loop handles cascading. AY's batch architecture requires
            // an internal fixpoint. Each iteration only processes
            // touched_rows seeded by the previous iteration's newly-bounded
            // variables, so the cost scales with cascade width.
            // #8599: Reuse persistent buffer for all_newly_bounded to avoid
            // per-propagation HashSet allocation.
            self.all_newly_bounded_buf.clear();
            let mut fixpoint_iters = 0u32;
            // #8422: Adaptive propagation-time fixpoint cap matching check-time
            // depth. Z3's bound_analyzer iterates without an explicit cap; AY
            // needs one to bound per-call cost. Small/medium problems (< 200
            // rows) benefit from deeper cascades -- matching the check-time
            // adaptive cap in run_post_simplex_propagation.
            let max_propagate_fixpoint = if self.rows.len() < 200 { 16u32 } else { 8u32 };
            let fixpoint_continuation_needed = loop {
                let result = self.compute_implied_bounds();
                let is_empty = result.newly_bounded.is_empty();
                if !is_empty {
                    // #7853: Reuse persistent buffer for newly_bounded_sorted
                    // to avoid per-fixpoint-iteration Vec allocation.
                    self.newly_bounded_sorted_buf.clear();
                    self.newly_bounded_sorted_buf
                        .extend(result.newly_bounded.iter().copied());
                    self.newly_bounded_sorted_buf.sort_unstable();
                    if !self.atom_index.is_empty() && !self.newly_bounded_sorted_buf.is_empty() {
                        // #7853: Take the buffer temporarily to avoid borrow conflict.
                        let sorted = std::mem::take(&mut self.newly_bounded_sorted_buf);
                        self.compute_bound_propagations_for_vars(&sorted);
                        self.newly_bounded_sorted_buf = sorted;
                    }
                    self.all_newly_bounded_buf.extend(&result.newly_bounded);
                }
                // #8256: Stop when inner cascade converged (see check_atoms.rs).
                let reached_cap =
                    !is_empty && !result.converged && fixpoint_iters >= max_propagate_fixpoint;
                if is_empty || result.converged || reached_cap {
                    break reached_cap && !self.touched_rows.is_empty();
                }
                fixpoint_iters += 1;
            };
            self.propagate_direct_touched_rows_pending = fixpoint_continuation_needed;
            self.implied_bounds_fresh = false;
            if !self.all_newly_bounded_buf.is_empty() {
                self.propagation_dirty_vars
                    .extend(self.all_newly_bounded_buf.iter());
                // #8599: Take the buffer temporarily to avoid borrow conflict with &mut self.
                let all_nb = std::mem::take(&mut self.all_newly_bounded_buf);
                self.queue_post_simplex_refinements(&all_nb, self.debug_lra);
                self.all_newly_bounded_buf = all_nb;
            }
            // #6617 Packet 1: Discover offset equalities (nf==2 rows) from
            // the same touched rows. Z3's cheap_eq_on_nbase detects x1 = x2
            // when two rows share a non-fixed column y with coefficient +/-1
            // and equal offsets. Equalities feed the E-graph for BCP cascades.
            // Reference: z3/src/math/lp/lp_bound_propagator.h:357-418
            // #7853: Temporarily take the snapshot buffer to avoid borrow conflict
            // with &mut self in discover_offset_equalities.
            let touched_snapshot = std::mem::take(&mut self.touched_rows_snapshot_buf);
            self.discover_offset_equalities(&touched_snapshot);
            self.touched_rows_snapshot_buf = touched_snapshot;
        } else if self.propagate_direct_touched_rows_pending && skip_for_freshness {
            // #8468: check_during_propagate already ran compute_implied_bounds
            // on these touched rows and no new simplex-affecting bounds arrived.
            // Clear both flags without re-running.
            self.propagate_direct_touched_rows_pending = false;
            self.implied_bounds_fresh = false;
            self.stats.propagate_implied_bounds_fresh_skips += 1;
        }

        // #8422: Drain Phase 2 bound chain propagations that were added to
        // pending_propagations by compute_bound_propagations_for_vars above.
        // These use implied bounds derived during this propagate() call and
        // need the same stale-reason processing as check()-time propagations.
        if !self.pending_propagations.is_empty() {
            let phase2_pending: Vec<PendingPropagation> =
                std::mem::take(&mut self.pending_propagations);
            // #8511: Phase 2 drain — propagations from compute_bound_propagations_for_vars
            // called inside the fixpoint loop. Eagerly materialize all types. Even after
            // the fixpoint loop, bounds only get tighter (never retracted within a
            // propagation call), so over-constrained reasons are sound. The stale-reason
            // filter below catches any reason atoms that are no longer asserted.
            for p in phase2_pending {
                let mut prop = p.propagation;
                if let Some(deferred) = p.deferred {
                    match deferred {
                        DeferredReason::DirectBound { var, need_upper } => {
                            // #8511 fix: Eagerly materialize DirectBound reasons
                            // in Phase 2 drain (same fix as Phase 1 first-pass).
                            // Previously created lazy propagations that were
                            // rejected by the stale-reason retain filter.
                            let vi = var as usize;
                            let mut emitted_p2 = false;
                            if let Some(info) = self.vars.get(vi) {
                                let bound = if need_upper {
                                    info.upper.as_ref()
                                } else {
                                    info.lower.as_ref()
                                };
                                if let Some(b) = bound {
                                    let reason: Vec<TheoryLit> = b
                                        .reason_pairs()
                                        .filter(|(term, _)| !term.is_sentinel())
                                        .filter(|(term, val)| self.asserted.get(term) == Some(val))
                                        .map(|(term, val)| TheoryLit::new(term, val))
                                        .collect();
                                    let total_non_sentinel = b
                                        .reason_pairs()
                                        .filter(|(term, _)| !term.is_sentinel())
                                        .count();
                                    if !reason.is_empty() && reason.len() == total_non_sentinel {
                                        prop.reason = reason;
                                        self.propagated_atoms
                                            .insert((prop.literal.term, prop.literal.value));
                                        self.stats.emitted_direct_count += 1;
                                        propagations.push(prop);
                                        emitted_p2 = true;
                                    }
                                }
                            }
                            if !emitted_p2 {
                                // Bound retracted or stale — skip.
                            }
                            continue;
                        }
                        DeferredReason::ImpliedRow { .. } => {
                            // #8599: Scope atom_cache borrow to avoid cloning LinearExpr.
                            let emitted = 'interval_p2: {
                                let atom_term = prop.literal.term;
                                let reason = {
                                    let Some(Some(info)) = self.atom_cache.get(&atom_term) else {
                                        break 'interval_p2 false;
                                    };
                                    let is_le = info.is_le;
                                    let strict = info.strict;
                                    let (lb, ub) = self.compute_expr_interval(&info.expr);
                                    let implied_true = if prop.literal.value {
                                        if is_le {
                                            ub.as_ref().is_some_and(|ep| {
                                                Self::endpoint_implies_le_zero(ep, strict)
                                            })
                                        } else {
                                            lb.as_ref().is_some_and(|ep| {
                                                Self::endpoint_implies_ge_zero(ep, strict)
                                            })
                                        }
                                    } else if is_le {
                                        lb.as_ref().is_some_and(|ep| {
                                            Self::endpoint_implies_not_le_zero(ep, strict)
                                        })
                                    } else {
                                        ub.as_ref().is_some_and(|ep| {
                                            Self::endpoint_implies_not_ge_zero(ep, strict)
                                        })
                                    };
                                    if !implied_true {
                                        break 'interval_p2 false;
                                    }
                                    let for_upper = if prop.literal.value { is_le } else { !is_le };
                                    let reason =
                                        self.collect_interval_reasons(&info.expr, for_upper);
                                    if reason.is_empty() {
                                        break 'interval_p2 false;
                                    }
                                    reason
                                };
                                prop.reason = reason;
                                self.stats.deferred_reason_count += 1;
                                self.stats.emitted_implied_row_count += 1;
                                self.propagated_atoms
                                    .insert((prop.literal.term, prop.literal.value));
                                propagations.push(prop);
                                true
                            };
                            if !emitted {
                                continue;
                            }
                        }
                        DeferredReason::Interval {
                            atom_term,
                            for_upper: _,
                        } => {
                            // #8151 Phase 3: Materialize interval reason at Phase 2 drain.
                            // #8511 soundness fix: Re-verify interval before collecting reasons.
                            let lit = prop.literal;
                            // #8599: Scope atom_cache borrow to avoid cloning LinearExpr.
                            let emitted = 'interval_mat_p2: {
                                if !self.verify_interval_still_implied(&prop.literal) {
                                    break 'interval_mat_p2 false;
                                }
                                let reason = {
                                    let Some(Some(info)) = self.atom_cache.get(&atom_term) else {
                                        break 'interval_mat_p2 false;
                                    };
                                    let is_le = info.is_le;
                                    let for_upper = if prop.literal.value { is_le } else { !is_le };
                                    let reason =
                                        self.collect_interval_reasons(&info.expr, for_upper);
                                    if reason.is_empty() {
                                        break 'interval_mat_p2 false;
                                    }
                                    reason
                                };
                                prop.reason = reason;
                                self.stats.deferred_interval_count += 1;
                                Self::note_propagated(
                                    &mut self.propagated_atoms,
                                    &mut self.propagated_trail,
                                    lit.term,
                                    lit.value,
                                );
                                propagations.push(prop);
                                true
                            };
                            if !emitted {
                                continue;
                            }
                        }
                        DeferredReason::ImpliedBound { var, need_upper } => {
                            // #8467/#9704: Lazy justification for ImpliedBound
                            // propagations in Phase 2 drain (same as Phase 1).
                            let polarity_bit = if prop.literal.value { 1u64 << 33 } else { 0 };
                            let upper_bit = if need_upper { 1u64 << 32 } else { 0 };
                            let reason_data =
                                (1u64 << 62) | polarity_bit | upper_bit | u64::from(var);
                            prop.reason_data = Some(reason_data);
                            self.stats.lazy_emitted_count += 1;
                            self.stats.emitted_implied_count += 1;
                            self.propagated_atoms
                                .insert((prop.literal.term, prop.literal.value));
                            propagations.push(prop);
                        }
                    }
                } else if prop.is_lazy() {
                    // #8467/#9704: Same as Phase 1 — pass DirectBound/ImpliedBound
                    // lazy propagations through; eagerly materialize Interval.
                    if let Some(reason_data) = prop.reason_data {
                        let is_interval = (reason_data >> 63) & 1 != 0;
                        if is_interval {
                            if let Some(reason) =
                                self.eagerly_materialize_reason_data(reason_data, &prop.literal)
                            {
                                prop.reason = reason;
                                prop.reason_data = None;
                                self.stats.eager_reason_count += 1;
                                self.propagated_atoms
                                    .insert((prop.literal.term, prop.literal.value));
                                propagations.push(prop);
                            } else {
                                self.propagated_atoms
                                    .remove(&(prop.literal.term, prop.literal.value));
                            }
                        } else {
                            self.propagated_atoms
                                .insert((prop.literal.term, prop.literal.value));
                            propagations.push(prop);
                        }
                    } else {
                        self.propagated_atoms
                            .remove(&(prop.literal.term, prop.literal.value));
                    }
                } else if !prop.reason.is_empty() {
                    self.stats.eager_reason_count += 1;
                    propagations.push(prop);
                }
            }
        }

        // #4919 Phase C: removed atom_cache.len() < 4 threshold.
        // Interval propagation now runs whenever dirty variables exist, regardless
        // of cache size. The dirty_vars filter already limits work to O(dirty × atoms_per_var).

        // Collect candidate atoms whose variables had bounds change (#4919 propagation opt).
        // Instead of scanning ALL atoms in atom_cache, only check atoms referencing
        // variables in propagation_dirty_vars. This reduces work from O(all_atoms) to
        // O(dirty_vars * atoms_per_var) per propagate() call.
        let dirty = std::mem::take(&mut self.propagation_dirty_vars);

        // #7853: Reuse persistent buffers for candidates and seen set to avoid
        // per-propagate() heap allocation.
        self.propagation_candidates_buf.clear();
        self.propagation_seen_buf.clear();
        if !dirty.is_empty() {
            // For each dirty variable, look up atoms that reference it via var_to_atoms.
            for &var in &dirty {
                // #7851 D2: Skip variables where all bound atoms are already assigned.
                let vi = var as usize;
                if vi < self.unassigned_atom_count.len() && self.unassigned_atom_count[vi] == 0 {
                    continue;
                }
                if let Some(atoms) = self.var_to_atoms.get(&var) {
                    for &atom_term in atoms {
                        if !self.propagation_seen_buf.insert(atom_term) {
                            continue;
                        }
                        // Filter: not eq/distinct, not already asserted.
                        // Note: multi-variable atoms (coeffs.len() > 1) are now
                        // included (#4919). compute_expr_interval uses implied
                        // bounds to derive finite intervals for compound atoms.
                        if let Some(Some(info)) = self.atom_cache.get(&atom_term) {
                            if info.is_eq || info.is_distinct {
                                continue;
                            }
                            if self.asserted.contains_key(&atom_term) {
                                continue;
                            }
                            self.propagation_candidates_buf
                                .push((atom_term, info.strict));
                        }
                    }
                }
            }
        }
        // Take candidates out so we can iterate while mutating self.
        let candidates = std::mem::take(&mut self.propagation_candidates_buf);

        let candidate_count = candidates.len();
        // Diagnostic counters for interval propagation pipeline (#TL48).
        let mut diag_no_ub = 0u32;
        let mut diag_no_lb = 0u32;
        let mut diag_both_none = 0u32;
        let mut diag_not_implied = 0u32;
        let mut diag_already_propagated = 0u32;
        let mut diag_empty_reason = 0u32;
        let mut diag_success = 0u32;
        // #8599: Take persistent seen buffer for interval reason dedup to avoid
        // per-candidate HashSet allocation in the hot loop below.
        let mut interval_seen = std::mem::take(&mut self.interval_reason_seen_buf);
        for (atom_term, strict) in &candidates {
            // Borrow the expression from atom_cache without cloning.
            // We need the LinearExpr for compute_expr_interval and collect_interval_reasons.
            // Since we don't mutate atom_cache during this loop, this is safe via
            // index-based access: get the expr reference, compute, then collect reasons.
            let (expr, is_le) = match self.atom_cache.get(atom_term) {
                Some(Some(info)) => (&info.expr, info.is_le),
                _ => continue,
            };

            // Compound atoms are queued during check(); the remaining candidates are
            // single-variable atoms handled with plain interval propagation.
            let (lb, ub) = self.compute_expr_interval(expr);

            // Diagnostic: track why interval propagation fails.
            if lb.is_none() && ub.is_none() {
                diag_both_none += 1;
            } else if ub.is_none() {
                diag_no_ub += 1;
            } else if lb.is_none() {
                diag_no_lb += 1;
            }

            // is_le=true: atom asserts "expr <= 0" (or "expr < 0" if strict)
            //   true when UB(expr) <= 0, false when LB(expr) > 0
            // is_le=false: atom asserts "expr >= 0" (or "expr > 0" if strict)
            //   true when LB(expr) >= 0, false when UB(expr) < 0
            let implied_true = if is_le {
                ub.as_ref()
                    .is_some_and(|ep| Self::endpoint_implies_le_zero(ep, *strict))
            } else {
                lb.as_ref()
                    .is_some_and(|ep| Self::endpoint_implies_ge_zero(ep, *strict))
            };

            let implied_false = if is_le {
                lb.as_ref()
                    .is_some_and(|ep| Self::endpoint_implies_not_le_zero(ep, *strict))
            } else {
                ub.as_ref()
                    .is_some_and(|ep| Self::endpoint_implies_not_ge_zero(ep, *strict))
            };

            if !implied_true && !implied_false {
                diag_not_implied += 1;
            }

            // Mutual exclusion: an atom cannot be both implied-true and implied-false.
            // If both hold, the expression interval brackets zero from both sides,
            // which means the bounds are contradictory — simplex should have returned UNSAT.
            debug_assert!(
                !(implied_true && implied_false),
                "LRA propagate() contradiction: atom {atom_term:?} is both implied-true and implied-false",
            );

            if implied_true && !self.propagated_atoms.contains(&(*atom_term, true)) {
                // is_le=true: implied-true uses UB → for_upper=true
                // is_le=false: implied-true uses LB → for_upper=false
                let for_upper = is_le;
                // #8599: Pass expr reference directly — NLL ensures the shared
                // borrow on self.atom_cache ends after this call returns, before
                // the &mut self operations below. No clone needed.
                let reason =
                    self.collect_interval_reasons_with_seen(expr, for_upper, &mut interval_seen);
                if !reason.is_empty() {
                    diag_success += 1;
                    self.stats.eager_reason_count += 1;
                    Self::note_propagated(
                        &mut self.propagated_atoms,
                        &mut self.propagated_trail,
                        *atom_term,
                        true,
                    );
                    propagations.push(TheoryPropagation {
                        literal: TheoryLit::new(*atom_term, true),
                        reason,
                        reason_data: None,
                    });
                } else {
                    diag_empty_reason += 1;
                }
            } else if implied_false && !self.propagated_atoms.contains(&(*atom_term, false)) {
                // is_le=true: implied-false uses LB → for_upper=false
                // is_le=false: implied-false uses UB → for_upper=true
                let for_upper = !is_le;
                // #8599: Pass expr reference directly — no clone needed (NLL).
                let reason =
                    self.collect_interval_reasons_with_seen(expr, for_upper, &mut interval_seen);
                if !reason.is_empty() {
                    diag_success += 1;
                    self.stats.eager_reason_count += 1;
                    Self::note_propagated(
                        &mut self.propagated_atoms,
                        &mut self.propagated_trail,
                        *atom_term,
                        false,
                    );
                    propagations.push(TheoryPropagation {
                        literal: TheoryLit::new(*atom_term, false),
                        reason,
                        reason_data: None,
                    });
                } else {
                    diag_empty_reason += 1;
                }
            } else if implied_true || implied_false {
                diag_already_propagated += 1;
            }
        }
        // #7853: Return candidates buffer for reuse in next propagate() call.
        self.propagation_candidates_buf = candidates;
        // #8599: Return interval reason seen buffer for reuse.
        self.interval_reason_seen_buf = interval_seen;

        if self.debug_lra && (!propagations.is_empty() || candidate_count > 0) {
            safe_eprintln!(
                "[LRA] propagate(): pending={}, candidates={}, interval_found={}, total={} | \
                 diag: both_none={}, no_ub={}, no_lb={}, not_implied={}, already_prop={}, empty_reason={}, success={}",
                pending_count,
                candidate_count,
                propagations.len().saturating_sub(pending_count),
                propagations.len(),
                diag_both_none,
                diag_no_ub,
                diag_no_lb,
                diag_not_implied,
                diag_already_propagated,
                diag_empty_reason,
                diag_success,
            );
        }
        // Soundness filter: every propagation must have non-empty reasons, and
        // every reason literal must be currently asserted. Empty reasons cause
        // invalid conflict clauses in the DPLL layer; stale reasons cause unsound
        // learning and false UNSAT.
        //
        // In combined_theory_mode (LIRA/AUFLIRA), cross-sort reason atoms from
        // the partner theory (e.g., LIA Int atoms) are injected via
        // assert_tight_bound/assert_cross_sort_bounds/assert_shared_equality and
        // are NOT tracked in this LRA's local `asserted` map. The reason chain
        // is still valid because the DPLL layer tracks all assertions globally.
        //
        // #9031: Promoted from debug_assert to production filter. Stale reasons
        // were the root cause of false UNSAT on 6 QF_LRA benchmarks. Multiple
        // propagation paths (interval, implied-row, direct-bound) can produce
        // reasons referencing atoms that are no longer asserted due to basis
        // changes or bound retractions between check() and propagate().
        // Filtering these out restores soundness without disabling propagation.
        //
        // #8511: Lazy propagations now go through the stale-reason filter too.
        // Previously (comment #8467), lazy propagations bypassed this filter
        // with the assumption that the DPLL extension's falsification guard
        // (#6262) would catch stale reasons at materialization time. But this
        // was insufficient: a stale lazy propagation forces a literal on the
        // DPLL trail, causing simplex to find conflicts in an over-constrained
        // system. The learned clause from that conflict is sound given the
        // (incorrect) trail, but wrong because the trail should never have
        // included the stale propagation. The falsification guard only catches
        // stale reasons when they're materialized for conflict analysis — but
        // by then the damage (incorrect conflict learning) has already happened.
        //
        // For DirectBound lazy propagations, we validate reason_pairs() against
        // self.asserted in-place (no allocation). For ImpliedBound and Interval
        // lazy propagations, we eagerly materialize the reason, validate it,
        // and convert to eager if valid. The materialization cost is justified
        // by soundness requirements.
        if !self.combined_theory_mode {
            let pre_filter = propagations.len();
            // #8511: First pass — semantic + syntactic validation of ALL
            // lazy propagations. This covers three categories:
            //
            // 1. DirectBound (bits63=0, 62=0): validate reason_pairs() against
            //    self.asserted. DirectBound propagations reference direct bounds
            //    from assert_literal which should always be current.
            //
            // 2. Interval (bit63=1): Re-verify the interval conclusion by
            //    re-running compute_expr_interval() with current bounds. The
            //    interval was computed at propagation time but implied bounds may
            //    have changed since then. If the interval no longer implies the
            //    propagation, reject it.
            //
            // 3. ImpliedBound (bits63=0, 62=1): Same semantic re-verification
            //    via the atom's expression interval. The implied bound may be
            //    stale; checking the expression interval with current bounds
            //    validates whether the propagation conclusion still holds.
            //
            // This two-level (semantic + syntactic) validation is necessary
            // because #8254 showed that stale implied bounds produce
            // syntactically-valid reasons (all asserted) that are semantically
            // wrong (the reasons prove a different bound than what was used).
            // #8467's lazy justification defers reason collection to
            // materialization time, creating a window where the implied bounds
            // used in the interval computation at propagation-time differ from
            // the current state. Pure syntactic validation of materialized
            // reasons cannot detect this mismatch.
            for prop in propagations.iter_mut() {
                if !prop.is_lazy() {
                    continue;
                }
                let reason_data = match prop.reason_data {
                    Some(rd) => rd,
                    None => continue,
                };
                let is_interval = (reason_data >> 63) & 1 != 0;
                let is_implied = !is_interval && ((reason_data >> 62) & 1 != 0);

                if !is_interval && !is_implied {
                    // DirectBound: eagerly materialize reason from reason_pairs().
                    // #8511 fix: Previously this path only validated reason_pairs()
                    // but left prop.reason empty (lazy). The retain filter at the
                    // end rejects all propagations with empty reasons, so ALL
                    // DirectBound lazy propagations were silently dropped. This
                    // caused the solver to miss critical bound propagations,
                    // leading to false-UNSAT on QF_LRA benchmarks (rand_70_300,
                    // tsp_rand_70_300) where direct-bound propagations are the
                    // primary source of theory guidance.
                    //
                    // Fix: eagerly collect reason_pairs() into prop.reason and
                    // clear reason_data, converting from lazy to eager. This
                    // ensures the retain filter keeps valid DirectBound propagations.
                    let var = (reason_data & 0xFFFF_FFFF) as u32;
                    let need_upper = (reason_data >> 32) & 1 != 0;
                    let vi = var as usize;
                    let mut materialized = false;
                    if let Some(info) = self.vars.get(vi) {
                        let bound = if need_upper {
                            info.upper.as_ref()
                        } else {
                            info.lower.as_ref()
                        };
                        if let Some(b) = bound {
                            let reason: Vec<TheoryLit> = b
                                .reason_pairs()
                                .filter(|(term, _)| !term.is_sentinel())
                                .filter(|(term, val)| self.asserted.get(term) == Some(val))
                                .map(|(term, val)| TheoryLit::new(term, val))
                                .collect();
                            // Must have at least one non-sentinel asserted reason.
                            // Also verify ALL original reason_pairs are asserted
                            // (not just the filtered subset).
                            let total_non_sentinel = b
                                .reason_pairs()
                                .filter(|(term, _)| !term.is_sentinel())
                                .count();
                            if !reason.is_empty() && reason.len() == total_non_sentinel {
                                prop.reason = reason;
                                prop.reason_data = None;
                                materialized = true;
                            }
                        }
                    }
                    if !materialized {
                        self.propagated_atoms
                            .remove(&(prop.literal.term, prop.literal.value));
                        prop.reason_data = None;
                    }
                } else if is_implied {
                    // #8467/#9704: ImpliedBound lazy propagations pass through
                    // to the DPLL layer without eager materialization. The reason
                    // will be reconstructed on demand via explain_propagation()
                    // during conflict analysis. This is the core of the lazy
                    // justification optimization: ~90% of propagations are never
                    // explained, so deferring reason collection eliminates most
                    // of the per-propagation overhead.
                    //
                    // No semantic validation is needed here because:
                    // 1. The implied bound was valid at derivation time.
                    // 2. explain_propagation() validates asserted status at
                    //    materialization time (if it's ever called).
                    // 3. The DPLL layer's mark_propagation_rejected() handles
                    //    the case where explain_propagation() returns None.
                    //
                    // The reason_data is already set (bit62=1, bit33=polarity,
                    // bit32=need_upper, bits0-31=var). Leave it as-is.
                } else {
                    // Pure Interval: semantic re-verification via interval computation.
                    // #8599: Scope atom_cache borrow to avoid cloning LinearExpr.
                    let lit_term = prop.literal.term;
                    let lit_value = prop.literal.value;
                    let mut semantically_valid = false;

                    let reasons = {
                        if let Some(Some(info)) = self.atom_cache.get(&lit_term) {
                            let is_le = info.is_le;
                            let strict = info.strict;
                            let (lb, ub) = self.compute_expr_interval(&info.expr);

                            let still_implied = if lit_value {
                                if is_le {
                                    ub.as_ref().is_some_and(|ep| {
                                        Self::endpoint_implies_le_zero(ep, strict)
                                    })
                                } else {
                                    lb.as_ref().is_some_and(|ep| {
                                        Self::endpoint_implies_ge_zero(ep, strict)
                                    })
                                }
                            } else if is_le {
                                lb.as_ref().is_some_and(|ep| {
                                    Self::endpoint_implies_not_le_zero(ep, strict)
                                })
                            } else {
                                ub.as_ref().is_some_and(|ep| {
                                    Self::endpoint_implies_not_ge_zero(ep, strict)
                                })
                            };

                            if still_implied {
                                let for_upper = (reason_data >> 32) & 1 != 0;
                                let r = self.collect_interval_reasons(&info.expr, for_upper);
                                if !r.is_empty() {
                                    Some(r)
                                } else {
                                    None
                                }
                            } else {
                                None
                            }
                        } else {
                            None
                        }
                    };
                    // Shared borrow on atom_cache is now released.
                    if let Some(reasons) = reasons {
                        let all_asserted = reasons
                            .iter()
                            .all(|r| self.asserted.get(&r.term) == Some(&r.value));
                        if all_asserted {
                            prop.reason = reasons;
                            prop.reason_data = None;
                            semantically_valid = true;
                        }
                    }

                    if !semantically_valid {
                        self.propagated_atoms
                            .remove(&(prop.literal.term, prop.literal.value));
                        prop.reason_data = None;
                    }
                }
            }
            // Second pass: retain valid propagations (eager with valid reasons,
            // lazy with reason_data set, or DirectBound lazy that passed validation).
            propagations.retain(|prop| {
                // #8467/#9704: Lazy propagations with reason_data pass through
                // to the DPLL layer — their reasons will be materialized on
                // demand via explain_propagation() during conflict analysis.
                if prop.is_lazy() {
                    return true;
                }
                // Eager propagations must have non-empty reasons.
                if prop.reason.is_empty() {
                    return false;
                }
                for r in &prop.reason {
                    if self.asserted.get(&r.term) != Some(&r.value) {
                        self.propagated_atoms
                            .remove(&(prop.literal.term, prop.literal.value));
                        return false;
                    }
                }
                true
            });
            let filtered = pre_filter - propagations.len();
            self.stats.stale_reason_filtered_count += filtered as u64;
        } else {
            propagations.retain(|prop| !prop.reason.is_empty() || prop.is_lazy());
        }

        self.filter_unsound_propagations(&mut propagations);

        self.stats.propagation_count += propagations.len() as u64;
        // #8608/#8599: Transfer ownership instead of drain+collect. The caller
        // consumes the Vec, so mem::take is correct. The buffer field gets an
        // empty Vec (no allocation); on the NEXT call, capacity is restored
        // because the buffer is repopulated via std::mem::take at the top.
        self.propagation_output_buf = propagations;
        std::mem::take(&mut self.propagation_output_buf)
    }

    /// Drain pending propagations without running the full propagation pipeline (#8422).
    ///
    /// This is a lightweight version of `propagate_impl()` that only drains
    /// propagations from the `pending_propagations` buffer. It does NOT run
    /// simplex, implied bounds, interval propagation, or dirty-var scanning.
    ///
    /// #8511: All deferred reasons are eagerly materialized at drain time.
    /// This is sound because drain runs in the same propagation context as
    /// the propagations were created — no backtracking has occurred.
    pub(super) fn drain_pending_propagations_impl(&mut self) -> Vec<TheoryPropagation> {
        if self.no_theory_propagation || self.pending_propagations.is_empty() {
            return Vec::new();
        }

        let pending: Vec<PendingPropagation> = std::mem::take(&mut self.pending_propagations);
        // #8608: Reuse persistent buffer — clear() preserves capacity from prior calls.
        let mut propagations = std::mem::take(&mut self.propagation_output_buf);
        propagations.clear();

        for p in pending {
            let PendingPropagation {
                propagation: mut prop,
                deferred,
            } = p;

            if let Some(ref d) = deferred {
                // #8467/#9704: ImpliedBound deferred reasons become lazy propagations.
                if let DeferredReason::ImpliedBound { var, need_upper } = d {
                    let polarity_bit = if prop.literal.value { 1u64 << 33 } else { 0 };
                    let upper_bit = if *need_upper { 1u64 << 32 } else { 0 };
                    let reason_data = (1u64 << 62) | polarity_bit | upper_bit | u64::from(*var);
                    prop.reason_data = Some(reason_data);
                    self.stats.lazy_emitted_count += 1;
                    self.stats.emitted_implied_count += 1;
                    self.propagated_atoms
                        .insert((prop.literal.term, prop.literal.value));
                    propagations.push(prop);
                    continue;
                }
                if let Some(reason) = self.eagerly_materialize_deferred(d, &prop.literal) {
                    prop.reason = reason;
                    prop.reason_data = None;
                    self.propagated_atoms
                        .insert((prop.literal.term, prop.literal.value));
                    propagations.push(prop);
                } else {
                    self.propagated_atoms
                        .remove(&(prop.literal.term, prop.literal.value));
                }
                continue;
            }
            if prop.is_lazy() {
                // #8467/#9704: Lazy propagations with reason_data pass through
                // directly — their reasons are materialized on demand.
                self.propagated_atoms
                    .insert((prop.literal.term, prop.literal.value));
                propagations.push(prop);
                continue;
            }
            // Already has materialized reason.
            if self
                .propagated_atoms
                .contains(&(prop.literal.term, prop.literal.value))
            {
                continue;
            }
            self.propagated_atoms
                .insert((prop.literal.term, prop.literal.value));
            propagations.push(prop);
        }

        // #8467/#9704: Stale-reason filter — lazy propagations pass through.
        if !self.combined_theory_mode {
            let pre_filter = propagations.len();
            propagations.retain(|prop| {
                // Lazy propagations pass through to DPLL layer.
                if prop.is_lazy() {
                    return true;
                }
                if prop.reason.is_empty() {
                    return false;
                }
                for r in &prop.reason {
                    if self.asserted.get(&r.term) != Some(&r.value) {
                        self.propagated_atoms
                            .remove(&(prop.literal.term, prop.literal.value));
                        return false;
                    }
                }
                true
            });
            let filtered = pre_filter - propagations.len();
            self.stats.stale_reason_filtered_count += filtered as u64;
        } else {
            propagations.retain(|prop| !prop.reason.is_empty() || prop.is_lazy());
        }

        self.filter_unsound_propagations(&mut propagations);

        self.stats.propagation_count += propagations.len() as u64;
        // #8608/#8599: Transfer ownership instead of drain+collect.
        self.propagation_output_buf = propagations;
        std::mem::take(&mut self.propagation_output_buf)
    }

    /// #8511: Eagerly materialize a DeferredReason into a Vec<TheoryLit>.
    ///
    /// This reads the CURRENT theory state (bounds, implied_bounds, intervals)
    /// at drain time, when the state corresponds to the propagation's creation
    /// context. This is sound because drain happens in the same propagate() call
    /// as the propagation was created, before any backtracking or new assertions.
    ///
    /// Returns None if reason collection fails (bound retracted, no explanation).
    fn eagerly_materialize_deferred(
        &self,
        deferred: &DeferredReason,
        literal: &TheoryLit,
    ) -> Option<Vec<TheoryLit>> {
        match deferred {
            DeferredReason::DirectBound { var, need_upper } => {
                let vi = *var as usize;
                let info = self.vars.get(vi)?;
                let bound = if *need_upper {
                    info.upper.as_ref()
                } else {
                    info.lower.as_ref()
                };
                let bound = bound?;
                let reason: Vec<TheoryLit> = bound
                    .reason_pairs()
                    .filter(|(term, _)| !term.is_sentinel())
                    .map(|(term, val)| TheoryLit::new(term, val))
                    .collect();
                if reason.is_empty() {
                    return None;
                }
                Some(reason)
            }
            DeferredReason::ImpliedBound { var, need_upper } => {
                // #8511: BoundExplanation chain + single-row + interval fallbacks.
                // collect_reasons_from_explanation() now validates direct bound
                // asserted status, preventing unsound reason sets.
                let vi = *var as usize;
                // Try eager reason collection from BoundExplanation first.
                if let Some(reasons) = self.make_eager_implied_propagation_reasons(vi, *need_upper)
                {
                    if !reasons.is_empty() {
                        return Some(reasons);
                    }
                }
                // Fallback: single-row reason collection.
                if let Some(ib_pair) = self.implied_bounds.get(vi) {
                    let ib = if *need_upper {
                        ib_pair.1.as_ref()
                    } else {
                        ib_pair.0.as_ref()
                    };
                    if let Some(ib) = ib {
                        if ib.row_idx != usize::MAX && self.max_row_width <= 50 {
                            if let Some(reasons) =
                                self.collect_single_row_reasons(*var, *need_upper, ib.row_idx)
                            {
                                if !reasons.is_empty() {
                                    return Some(reasons);
                                }
                            }
                        }
                    }
                }
                // Third fallback: interval-based reasons from atom expression.
                let atom_term = literal.term;
                if let Some(Some(info)) = self.atom_cache.get(&atom_term) {
                    // #7853: Use reference instead of cloning LinearExpr.
                    let is_le = info.is_le;
                    let strict = info.strict;
                    let for_upper = if literal.value { is_le } else { !is_le };
                    // #8754 soundness fix: verify the direct-only interval
                    // actually IMPLIES the literal before returning reasons
                    // from collect_interval_reasons. Without this check, when
                    // the ImpliedBound propagation was enqueued against a
                    // tighter implied bound (post-simplex cascade or
                    // cross-negation overlay), the collected direct-bound
                    // reasons are syntactically valid but do not prove the
                    // propagation.
                    let (lb, ub) = self.compute_expr_interval_direct_only(&info.expr);
                    let implied_true = if literal.value {
                        if is_le {
                            ub.as_ref()
                                .is_some_and(|ep| Self::endpoint_implies_le_zero(ep, strict))
                        } else {
                            lb.as_ref()
                                .is_some_and(|ep| Self::endpoint_implies_ge_zero(ep, strict))
                        }
                    } else if is_le {
                        lb.as_ref()
                            .is_some_and(|ep| Self::endpoint_implies_not_le_zero(ep, strict))
                    } else {
                        ub.as_ref()
                            .is_some_and(|ep| Self::endpoint_implies_not_ge_zero(ep, strict))
                    };
                    if !implied_true {
                        return None;
                    }
                    let reason = self.collect_interval_reasons(&info.expr, for_upper);
                    if !reason.is_empty() {
                        return Some(reason);
                    }
                }
                None
            }
            DeferredReason::ImpliedRow { .. } => {
                // #8511 soundness fix: Re-verify interval before collecting reasons.
                let atom_term = literal.term;
                if let Some(Some(info)) = self.atom_cache.get(&atom_term) {
                    // #7853: Use reference instead of cloning LinearExpr.
                    let is_le = info.is_le;
                    let strict = info.strict;
                    let (lb, ub) = self.compute_expr_interval(&info.expr);
                    let implied_true = if literal.value {
                        if is_le {
                            ub.as_ref()
                                .is_some_and(|ep| Self::endpoint_implies_le_zero(ep, strict))
                        } else {
                            lb.as_ref()
                                .is_some_and(|ep| Self::endpoint_implies_ge_zero(ep, strict))
                        }
                    } else if is_le {
                        lb.as_ref()
                            .is_some_and(|ep| Self::endpoint_implies_not_le_zero(ep, strict))
                    } else {
                        ub.as_ref()
                            .is_some_and(|ep| Self::endpoint_implies_not_ge_zero(ep, strict))
                    };
                    if !implied_true {
                        return None;
                    }
                    let for_upper = if literal.value { is_le } else { !is_le };
                    let reason = self.collect_interval_reasons(&info.expr, for_upper);
                    if !reason.is_empty() {
                        return Some(reason);
                    }
                }
                None
            }
            DeferredReason::Interval {
                atom_term,
                for_upper: _,
            } => {
                // #8511 soundness fix: Re-verify interval before collecting reasons.
                if let Some(Some(info)) = self.atom_cache.get(atom_term) {
                    // #7853: Use reference instead of cloning LinearExpr.
                    let is_le = info.is_le;
                    let strict = info.strict;
                    let (lb, ub) = self.compute_expr_interval(&info.expr);
                    let implied_true = if literal.value {
                        if is_le {
                            ub.as_ref()
                                .is_some_and(|ep| Self::endpoint_implies_le_zero(ep, strict))
                        } else {
                            lb.as_ref()
                                .is_some_and(|ep| Self::endpoint_implies_ge_zero(ep, strict))
                        }
                    } else if is_le {
                        lb.as_ref()
                            .is_some_and(|ep| Self::endpoint_implies_not_le_zero(ep, strict))
                    } else {
                        ub.as_ref()
                            .is_some_and(|ep| Self::endpoint_implies_not_ge_zero(ep, strict))
                    };
                    if !implied_true {
                        return None;
                    }
                    let for_upper = if literal.value { is_le } else { !is_le };
                    let reason = self.collect_interval_reasons(&info.expr, for_upper);
                    if !reason.is_empty() {
                        return Some(reason);
                    }
                }
                None
            }
        }
    }

    /// #8511: Eagerly materialize a lazy propagation's reason_data into reasons.
    ///
    /// Handles propagations created by make_implied_propagation /
    /// make_eager_implied_propagation that have reason_data set but
    /// deferred: None. Decodes the reason_data encoding and collects reasons.
    fn eagerly_materialize_reason_data(
        &self,
        reason_data: u64,
        literal: &TheoryLit,
    ) -> Option<Vec<TheoryLit>> {
        let is_interval = (reason_data >> 63) & 1 != 0;
        let is_implied = !is_interval && ((reason_data >> 62) & 1 != 0);

        if is_interval {
            // Interval encoding: bits 0-31 = atom_term, bit 32 = for_upper.
            let atom_term = TermId((reason_data & 0xFFFF_FFFF) as u32);
            // #8511 soundness fix: Re-verify interval conclusion before
            // collecting reasons. Without this, stale interval computations
            // produce syntactically-valid but semantically-wrong reasons.
            if let Some(Some(info)) = self.atom_cache.get(&atom_term) {
                // #7853: Use reference instead of cloning LinearExpr.
                let is_le = info.is_le;
                let strict = info.strict;
                let (lb, ub) = self.compute_expr_interval(&info.expr);
                let implied_true = if literal.value {
                    if is_le {
                        ub.as_ref()
                            .is_some_and(|ep| Self::endpoint_implies_le_zero(ep, strict))
                    } else {
                        lb.as_ref()
                            .is_some_and(|ep| Self::endpoint_implies_ge_zero(ep, strict))
                    }
                } else if is_le {
                    lb.as_ref()
                        .is_some_and(|ep| Self::endpoint_implies_not_le_zero(ep, strict))
                } else {
                    ub.as_ref()
                        .is_some_and(|ep| Self::endpoint_implies_not_ge_zero(ep, strict))
                };
                if !implied_true {
                    return None;
                }
                let for_upper = if literal.value { is_le } else { !is_le };
                let reason = self.collect_interval_reasons(&info.expr, for_upper);
                if !reason.is_empty() {
                    return Some(reason);
                }
            }
            None
        } else if is_implied {
            // ImpliedBound encoding: bits 0-31 = var, bit 32 = need_upper.
            let var = (reason_data & 0xFFFF_FFFF) as u32;
            let need_upper = (reason_data >> 32) & 1 != 0;
            // #8511 soundness fix: Re-verify implied bound still implies atom.
            if !self.verify_implied_bound_for_atom(var, need_upper, literal.term, literal.value) {
                return None;
            }
            let deferred = DeferredReason::ImpliedBound { var, need_upper };
            self.eagerly_materialize_deferred(&deferred, literal)
        } else {
            // DirectBound encoding: bits 0-31 = var, bit 32 = need_upper.
            let var = (reason_data & 0xFFFF_FFFF) as u32;
            let need_upper = (reason_data >> 32) & 1 != 0;
            let deferred = DeferredReason::DirectBound { var, need_upper };
            self.eagerly_materialize_deferred(&deferred, literal)
        }
    }

    /// #8511: Re-verify that the current implied/direct bound for a variable
    /// still implies the given atom. Returns true if the propagation is still
    /// sound, false if the bound has changed and the propagation should be
    /// rejected.
    ///
    /// This is a targeted check for ImpliedBound propagations that verifies
    /// against the actual variable bound (direct or implied), rather than
    /// compute_expr_interval which requires ALL variables in an expression
    /// to have direct bounds (too conservative for implied-bound propagations).
    fn verify_implied_bound_for_atom(
        &self,
        var: u32,
        need_upper: bool,
        atom_term: TermId,
        literal_value: bool,
    ) -> bool {
        let vi = var as usize;
        let atoms = match self.atom_index.get(&var) {
            Some(a) => a,
            None => return false,
        };
        let atom = match atoms.iter().find(|a| a.term == atom_term) {
            Some(a) => a,
            None => return false,
        };

        // Get tighter of direct and implied bound
        let ib = if vi < self.implied_bounds.len() {
            if need_upper {
                self.implied_bounds[vi].1.as_ref()
            } else {
                self.implied_bounds[vi].0.as_ref()
            }
        } else {
            None
        };
        let direct_bound = if let Some(info) = self.vars.get(vi) {
            if need_upper {
                info.upper.as_ref().map(|b| (&b.value, b.strict))
            } else {
                info.lower.as_ref().map(|b| (&b.value, b.strict))
            }
        } else {
            None
        };
        let (bound_val, bound_strict) = match (direct_bound, ib) {
            (Some((dv, ds)), Some(iv)) => {
                if need_upper {
                    if iv.value < *dv || (iv.value == *dv && iv.strict && !ds) {
                        (&iv.value, iv.strict)
                    } else {
                        (dv, ds)
                    }
                } else if iv.value > *dv || (iv.value == *dv && iv.strict && !ds) {
                    (&iv.value, iv.strict)
                } else {
                    (dv, ds)
                }
            }
            (Some((dv, ds)), None) => (dv, ds),
            (None, Some(iv)) => (&iv.value, iv.strict),
            (None, None) => return false,
        };

        // Check if bound still implies the atom
        if atom.is_upper {
            // atom: var <= k
            if literal_value {
                // true: need upper bound <= k
                let cmp = bound_val.cmp(&atom.bound_value);
                if atom.strict {
                    cmp == std::cmp::Ordering::Less
                        || (cmp == std::cmp::Ordering::Equal && bound_strict)
                } else {
                    cmp == std::cmp::Ordering::Less || cmp == std::cmp::Ordering::Equal
                }
            } else {
                // false: need lower bound > k
                let cmp = bound_val.cmp(&atom.bound_value);
                if atom.strict {
                    cmp == std::cmp::Ordering::Greater || cmp == std::cmp::Ordering::Equal
                } else {
                    cmp == std::cmp::Ordering::Greater
                        || (cmp == std::cmp::Ordering::Equal && bound_strict)
                }
            }
        } else {
            // atom: var >= k
            if literal_value {
                // true: need lower bound >= k
                let cmp = bound_val.cmp(&atom.bound_value);
                if atom.strict {
                    cmp == std::cmp::Ordering::Greater
                        || (cmp == std::cmp::Ordering::Equal && bound_strict)
                } else {
                    cmp == std::cmp::Ordering::Greater || cmp == std::cmp::Ordering::Equal
                }
            } else {
                // false: need upper bound < k
                let cmp = bound_val.cmp(&atom.bound_value);
                if atom.strict {
                    cmp == std::cmp::Ordering::Less || cmp == std::cmp::Ordering::Equal
                } else {
                    cmp == std::cmp::Ordering::Less
                        || (cmp == std::cmp::Ordering::Equal && bound_strict)
                }
            }
        }
    }

    /// #8511: Re-verify that a deferred interval or compound expression
    /// propagation is still valid using compute_expr_interval with current
    /// direct bounds. Returns true if the interval still implies the literal.
    fn verify_interval_still_implied(&self, literal: &TheoryLit) -> bool {
        let Some(Some(info)) = self.atom_cache.get(&literal.term) else {
            return false;
        };
        let is_le = info.is_le;
        let strict = info.strict;
        let (lb, ub) = self.compute_expr_interval(&info.expr);
        if literal.value {
            if is_le {
                ub.as_ref()
                    .is_some_and(|ep| Self::endpoint_implies_le_zero(ep, strict))
            } else {
                lb.as_ref()
                    .is_some_and(|ep| Self::endpoint_implies_ge_zero(ep, strict))
            }
        } else if is_le {
            lb.as_ref()
                .is_some_and(|ep| Self::endpoint_implies_not_le_zero(ep, strict))
        } else {
            ub.as_ref()
                .is_some_and(|ep| Self::endpoint_implies_not_ge_zero(ep, strict))
        }
    }
}
