// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// Result from `compute_implied_bounds` indicating which variables received
/// tighter bounds and whether the inner cascade converged naturally (did not
/// hit the depth limit).
#[derive(Debug)]
pub(crate) struct ImpliedBoundsResult {
    /// Variables that received tighter implied bounds during this call.
    pub newly_bounded: DenseU32Set,
    /// True when the inner cascade loop terminated because no new bounds were
    /// discovered (natural fixpoint). False when the cascade hit
    /// MAX_CASCADE_DEPTH, meaning further cascading might still produce tighter
    /// bounds.
    pub converged: bool,
    /// True when cascade rounds beyond depth 1 discovered new bounds.
    /// Used by BCP cascade dry-streak tracking to throttle deep cascading
    /// when it is consistently unproductive.
    pub deep_cascade_productive: bool,
}

impl LraSolver {
    /// #inc-ib-gate (Rank 2, Yices2 propagator1.h:252-261 clean-room): a
    /// derived bound is worth STORING only if it could decide a pending atom
    /// (`bound_is_interesting`) or feed compound-atom interval propagation
    /// (`compound_use_index` — NOT covered by atom_index, so it gets its own
    /// check). Non-interesting bounds previously fed only the in-call cascade
    /// (#8422 "store everything"); with #inc-implied-trail persistence the
    /// cascade re-derives through direct bounds on demand, so skipping them
    /// is the same sound propagation-weakening as the work-budget guard.
    /// Kill switch: AY_LRA_NO_IB_GATE=1 restores store-everything.
    #[inline]
    fn derived_bound_worth_storing(&self, var: u32, is_upper: bool, value: &Rational) -> bool {
        fn gate_disabled() -> bool {
            static D: OnceLock<bool> = OnceLock::new();
            *D.get_or_init(|| {
                false // B24: kill-switch env retired; the gate stays on.
            })
        }
        gate_disabled()
            || self.compound_use_index.contains_key(&var)
            || self.bound_is_interesting(var, is_upper, value)
    }

    /// Compute implied bounds for all variables from tableau rows.
    ///
    /// Two-pass approach following Z3's `bound_analyzer_on_row`:
    ///
    /// Pass 1: For each row `x_b = c + sum(a_j * x_j)`, if all nonbasic
    /// variables have bounds, derive bounds for the basic variable.
    ///
    /// Pass 2: For each row, if exactly one variable (basic or nonbasic)
    /// lacks a bound, derive that bound from all the others. This is Z3's
    /// "single unbounded" optimization from `limit_monoid_u`/`limit_monoid_l`.
    ///
    /// Reference: Z3 `bound_analyzer_on_row.h`, `theory_arith_core.h:2600-3060`
    pub(crate) fn compute_implied_bounds(&mut self) -> ImpliedBoundsResult {
        // Deterministic work budget — ENTRY guard (backstop to the per-variable Zeno
        // throttle #8857). On u64-offset obligations the outer DPLL(T) loop re-enters
        // this function unboundedly; each call does expensive bignum cascade work
        // (to_rug/mul_add_assign churn observed under `sample`) and NEVER returns to
        // poll the wall-clock deadline — which is exactly why the timeout can't stop
        // it. Once the cumulative work budget is exhausted, return IMMEDIATELY with no
        // derivations, skipping the cascade entirely. The solver then stays responsive
        // (the deadline/watchdog can fire) and the propagation handshake quiesces.
        // Sound: implied bounds are an optimization — skipping them only weakens
        // propagation, never changes a verdict (feasibility is the bounded dual
        // simplex's call). Per-solve: a fresh solver is built per obligation.
        self.implied_work_done = self.implied_work_done.saturating_add(1);
        let work_budget = lra_debug_flags().implied_work_budget;
        if work_budget != 0 && self.implied_work_done >= work_budget {
            return ImpliedBoundsResult {
                newly_bounded: DenseU32Set::default(),
                converged: true,
                deep_cascade_productive: false,
            };
        }
        let num_vars = self.vars.len();
        // #4919: Persist implied bounds across check() calls. Previously,
        // implied_bounds was cleared every call, discarding bounds derived
        // in the previous fixpoint. This prevented cascading: bounds derived
        // in check #1 were lost, so check #2's fixpoint couldn't build on
        // them. Z3's LP solver persists bounds across propagation passes.
        //
        // Soundness: implied bounds are cleared on pop()/reset()/soft_reset()
        // (when direct bounds may revert). Between those events, previously-
        // derived bounds remain valid because the direct bounds they depend
        // on are still asserted.
        //
        // We resize to accommodate new variables (added since last call),
        // then overlay direct bounds (keeping the tighter of direct vs
        // previously-derived implied bound).
        // Force overlay when new variables have been added since last call.
        let need_resize = self.implied_bounds.len() < num_vars;
        if need_resize {
            self.direct_bounds_changed_since_implied = true;
        }
        self.implied_bounds.resize(num_vars, (None, None));
        self.var_bound_gen.resize(num_vars, 0);
        self.row_computed_gen.resize(self.rows.len(), 0);
        self.implied_tighten_streak.resize(num_vars, 0);
        // #inc-cib-nodelta: repeat call with no new inputs — no touched rows,
        // no direct-bound change, no rows added, and the overlay already
        // reflects a completed full sweep. A sweep here would re-visit rows
        // whose input generations are all stale and derive nothing; return
        // empty instead of full-sweeping every accumulated row (measured
        // ~390k calls / 39M swept rows per check-sat at BMC depth 14). Same
        // sound weakening as the work-budget early return above: implied
        // bounds are advisory, feasibility verdicts belong to the simplex.
        if self.ib_overlay_complete
            && self.touched_rows.is_empty()
            && !self.direct_bounds_changed_since_implied
            && self.rows.len() == self.rows_len_at_last_implied
        {
            return ImpliedBoundsResult {
                newly_bounded: DenseU32Set::default(),
                converged: true,
                deep_cascade_productive: false,
            };
        }
        let mut newly_bounded = DenseU32Set::default();
        // Per-variable tighten budget for this compute call. On slow-converging
        // boundary-chain problems the cascade re-tightens the same variables by
        // ever-smaller exact amounts (measured: 35M derivations / 15s on a
        // 149-assertion problem). After MAX_TIGHTENS_PER_VAR re-tightenings we
        // still STORE each tighter bound (bounds remain valid) but stop feeding
        // the variable back into the cascade frontier. Implied bounds are an
        // optimization: a less-than-maximally-tight bound is never unsound.
        const MAX_TIGHTENS_PER_VAR: u8 = 4;
        // #certora-ib-scratch: persistent scratch replaces the former
        // per-call `vec![0; num_vars]` (O(num_vars) alloc+zero per call was
        // ~12% of the solve window on 10^5-var Certora files). Restore the
        // zeros the PREVIOUS call dirtied, in O(touched); every entry not in
        // the touched list is already zero.
        if self.implied_tighten_scratch.len() < num_vars {
            self.implied_tighten_scratch.resize(num_vars, 0);
        }
        {
            let scratch = &mut self.implied_tighten_scratch;
            for &v in &self.implied_tighten_touched {
                if let Some(slot) = scratch.get_mut(v as usize) {
                    *slot = 0;
                }
            }
            self.implied_tighten_touched.clear();
        }

        // Overlay direct bounds into implied_bounds. A direct bound always
        // replaces a missing implied bound. When both exist, keep the tighter
        // one (direct bounds are always valid; implied bounds may be tighter
        // from previous fixpoint passes).
        // Direct bounds use row_idx = usize::MAX as sentinel.
        //
        // Incremental skip: when no direct bound has changed since the last
        // call (direct_bounds_changed_since_implied == false), the overlay
        // would recompute the same comparisons. Skip the O(num_vars) loop
        // entirely. This eliminates the dominant per-BCP cost when the theory
        // callback fires on cascade rows without new bound assertions.
        if self.direct_bounds_changed_since_implied {
            self.direct_bounds_changed_since_implied = false;
            // Incremental overlay (#8782): when direct_bounds_changed_vars tracks
            // specific changed variables, only overlay those instead of scanning
            // all vars. On resize or after pop/reset (vec empty + flag true),
            // fall back to full scan. Reduces O(num_vars) to O(changed_vars)
            // in the common BCP-cascade case.
            let use_incremental = !need_resize && !self.direct_bounds_changed_vars.is_empty();
            if use_incremental {
                let changed = std::mem::take(&mut self.direct_bounds_changed_vars);
                // #8003: Bump generation once for the batch of direct bound changes.
                self.bound_generation += 1;
                let cur_gen = self.bound_generation;
                for &var in &changed {
                    let i = var as usize;
                    if i >= self.vars.len() {
                        continue;
                    }
                    self.big_bound_seen |= Self::var_has_big_direct_bound(&self.vars[i]);
                    Self::overlay_direct_bound_for_var(&self.vars[i], &mut self.implied_bounds[i]);
                    self.register_fixed_term_var(var);
                    // Stamp variable so rows containing it are re-analyzed.
                    if i < self.var_bound_gen.len() {
                        self.var_bound_gen[i] = cur_gen;
                    }
                    // #8857: A direct-bound change legitimately enables a new
                    // round of derived tightenings for this variable.
                    if i < self.implied_tighten_streak.len() {
                        self.implied_tighten_streak[i] = 0;
                    }
                }
                self.direct_bounds_changed_vars = changed;
                self.direct_bounds_changed_vars.clear();
            } else {
                self.direct_bounds_changed_vars.clear();
                // #8857: Full-scan overlay is a lattice rebuild — reset all
                // Zeno-throttle streaks.
                self.implied_tighten_streak.fill(0);
                // #8003: Full scan — bump generation and stamp all vars.
                self.bound_generation += 1;
                let cur_gen = self.bound_generation;
                let mut fixed_vars = std::mem::take(&mut self.ib_fixed_vars_scratch);
                fixed_vars.clear();
                fixed_vars.reserve(num_vars);
                let mut any_big = false;
                for (i, info) in self.vars.iter().enumerate() {
                    any_big |= Self::var_has_big_direct_bound(info);
                    Self::overlay_direct_bound_for_var(info, &mut self.implied_bounds[i]);
                    fixed_vars.push(i as u32);
                    if i < self.var_bound_gen.len() {
                        self.var_bound_gen[i] = cur_gen;
                    }
                }
                self.big_bound_seen |= any_big;
                for var_idx in fixed_vars.drain(..) {
                    self.register_fixed_term_var(var_idx);
                }
                self.ib_fixed_vars_scratch = fixed_vars;
            }
        }

        // #certora-bigint-fast: with 2^256-scale direct bounds in play, the
        // exact-Rational accumulation is bignum-dominated even on narrow rows,
        // so the f64 pre-screen pays for itself from width 2 upward. Plain
        // i64 workloads keep the measured >= 4 gate.
        let prescreen_min_width: usize = if self.big_bound_seen { 2 } else { 4 };

        // Z3's bound propagation is a single pass over touched rows. When that
        // pass tightens bounds, the DPLL(T) loop re-enters theory propagation
        // later with freshly-touched rows instead of doing an in-function
        // fixpoint. Keep that architecture here: analyze the current row set
        // once, then seed touched_rows for the next call below.
        //
        // When touched_rows is empty we fall back to a full sweep. This keeps
        // initialization and direct unit tests working without requiring the
        // caller to pre-seed a row set.
        // #7719 D1: Use std::mem::take instead of clone to avoid O(rows) HashSet
        // clone per call. The function clears and reseeds touched_rows at the end
        // anyway, so taking ownership is equivalent but allocation-free.
        let iter_rows = if self.touched_rows.is_empty() {
            None
        } else {
            Some(std::mem::take(&mut self.touched_rows))
        };
        // #inc-cib-nodelta: a None here means this call sweeps EVERY row —
        // record that below so provably-empty repeat sweeps can be skipped.
        let was_full_sweep = iter_rows.is_none();
        // Pre-allocate contribution vectors outside both loops to avoid
        // repeated heap allocation. Cleared and reused per row (#4919, P1:129).
        // #8003: Changed from (vi, eq_c, contrib, strict) to (vi, eq_c, strict).
        // Z3's bound_analyzer_on_row doesn't store per-variable contributions;
        // it recomputes `total / a_j + bound_j` on demand. Removing the contrib
        // Rational eliminates ~70 BigRational allocations per row on dense LPs.
        // #cib-alloc: reuse persistent scratch (mem::take + restore at exit)
        // instead of per-call Vec::new(). Cleared before each row's use below,
        // so reuse is byte-identical.
        let mut lb_contribs = std::mem::take(&mut self.ib_lb_contribs_scratch);
        let mut ub_contribs = std::mem::take(&mut self.ib_ub_contribs_scratch);
        // #8200: f64 shadow accumulators for floating-point pre-screening.
        let mut lb_contribs_f64 = std::mem::take(&mut self.ib_lb_contribs_f64_scratch);
        let mut ub_contribs_f64 = std::mem::take(&mut self.ib_ub_contribs_f64_scratch);

        // Approach G diagnostic (#4919): count per-row unbounded-variable
        // distribution to understand bound starvation.
        if self.debug_lra
            && (self.stats.check_count == 1 || self.stats.check_count.is_multiple_of(200))
        {
            let mut unbounded_dist: [u32; 6] = [0; 6]; // 0,1,2,3,4,5+
            for row in &self.rows {
                let bv = row.basic_var as usize;
                let mut n_unbounded_lb = 0u32;
                // Count unbounded (no lower bound) for basic var
                if bv < num_vars && self.implied_bounds[bv].0.is_none() {
                    n_unbounded_lb += 1;
                }
                for &(v, ref coeff) in &row.coeffs {
                    let vi = v as usize;
                    if vi >= num_vars {
                        continue;
                    }
                    let eq_c_pos = coeff.is_negative(); // eq_coeff = -coeff
                    let need_lb = eq_c_pos;
                    if need_lb {
                        if self.implied_bounds[vi].0.is_none() {
                            n_unbounded_lb += 1;
                        }
                    } else if self.implied_bounds[vi].1.is_none() {
                        n_unbounded_lb += 1;
                    }
                }
                let idx = std::cmp::min(n_unbounded_lb as usize, 5);
                unbounded_dist[idx] += 1;
            }
            safe_eprintln!(
                "[LRA] Approach G: row unbounded-var distribution (lb direction): \
                0={}, 1={}, 2={}, 3={}, 4={}, 5+={}, total_rows={}",
                unbounded_dist[0],
                unbounded_dist[1],
                unbounded_dist[2],
                unbounded_dist[3],
                unbounded_dist[4],
                unbounded_dist[5],
                self.rows.len()
            );
        }

        // #cib-alloc: reuse persistent scratch; cleared at each cascade round
        // start (below) and drained empty, so reuse is byte-identical.
        let mut updates = std::mem::take(&mut self.ib_updates_scratch);
        updates.clear();

        // #7973: When touched-row filtering is active, iterate only the
        // touched rows instead of scanning all rows. This converts O(total_rows)
        // to O(touched_rows), significant on LP benchmarks with 100+ rows
        // but only 5-10 touched per BCP callback.
        // #cib-alloc: reuse persistent scratch instead of collecting a fresh
        // Vec per call. Same contents/order as the former collect+sort.
        let mut row_indices = std::mem::take(&mut self.ib_row_indices_scratch);
        row_indices.clear();
        match &iter_rows {
            Some(touched) => {
                row_indices.extend(touched.iter().copied());
                row_indices.sort_unstable();
            }
            None => row_indices.extend(0..self.rows.len()),
        }
        // #8008: Cascade bound propagation through containing rows.
        //
        // Z3's architecture cascades bound derivations through the SAT-theory
        // feedback loop: BCP -> unit_propagate() -> BCP -> ... Each call to
        // bound_analyzer_on_row discovers bounds that immediately feed back
        // into the next BCP round. AY's batch architecture requires this
        // cascade to happen WITHIN compute_implied_bounds().
        //
        // When a new tighter bound is derived for variable X, all rows
        // containing X are added to the worklist for re-evaluation. This
        // continues until no new bounds are discovered or the depth limit
        // is reached. The depth limit of 5 prevents exponential blowup
        // on dense problems where every variable appears in many rows.
        //
        // Previously, cascading happened only BETWEEN compute_implied_bounds()
        // calls via the fixpoint loop in propagation.rs. That required one
        // full function call per cascade hop (overlay direct bounds, generation
        // checks, etc.), making deep cascades expensive. This inner cascade
        // amortizes the per-call overhead across all cascade hops.
        //
        // Reference: Z3 theory_lra.cpp has no explicit cascade depth limit;
        // its SAT-theory loop naturally bounds depth via conflict-driven
        // backtracking. AY's depth limit was previously 5, which was too
        // conservative for induction benchmarks where Z3 achieves 228K
        // bound propagations via deep transitive cascades.
        //
        // #8008: Adaptive cascade depth based on tableau size. Small
        // problems (< 200 rows) benefit from deep cascading that discovers
        // transitive bound chains in a single compute_implied_bounds() call.
        // Large problems (>= 200 rows) risk over-propagation leading to
        // conflict storms (observed on simple_startup benchmarks at depth 20).
        //
        // The inner cascade only processes rows containing newly-bounded
        // variables, so per-round cost scales with cascade width (not total
        // tableau size). But on large tableaux with many inter-row
        // dependencies, each round touches more rows, creating exponential
        // growth. Cap depth proportional to tableau density.
        let base_cascade_depth: u32 = if self.rows.len() < 100 {
            20 // Small problems: deep cascading for full transitive closure
        } else if self.rows.len() < 300 {
            10 // Medium problems: moderate depth
        } else if self.rows.len() < 500 {
            3 // Medium-large (300-499 rows): conservative. With 380+ rows
              // (simple_startup), each cascade round does O(touched_rows * width)
              // bignum arithmetic. Combined with BCP fixpoint cap of 3, this yields
              // 3*3=9 compute_implied_bounds calls per BCP callback (down from
              // 8*5=40). The DPLL loop re-enters for deeper cascading.
        } else {
            2 // Large (500+ rows): minimal to prevent conflict storms
        };
        // #8255: Cascade dry streak throttling. When consecutive BCP checks
        // find that cascading beyond depth 1 produces zero additional bounds,
        // the bound lattice has saturated for this problem region. Cap cascade
        // depth to 1 (single pass only) to avoid O(cascade_depth * rows_per_round)
        // wasted work per check. The streak resets when deep cascading produces
        // bounds, on pop/reset, or when new direct bounds are asserted.
        //
        // On windowreal-no_t_deadlock-16 (718 rows, 2677 checks, 25706 cascade
        // rounds), most deep cascade rounds produce nothing — the bound lattice
        // is fully explored after round 1. Throttling reduces total cascade
        // rounds dramatically while preserving the occasional productive deep
        // cascade when new bounds break the monotone.
        let max_cascade_depth: u32 = if self.warm_reuse_hint {
            // #lra-inc-engine S3 (warm theory): this check reuses a theory
            // persisted across check-sats. On a region shift (alternating .ind, a
            // property sign change) the warm cache is stale and the recursive
            // cascade re-derives through the accumulated bounds and explodes
            // (implied_row_recursive dominates the profile), making warm SLOWER
            // than from-scratch. Cap to a single pass so warm is never worse than
            // from-scratch. The monotone (.bmc) benefit is unaffected: a valid
            // warm cache early-returns via #inc-cib-nodelta above, before this
            // cascade is ever reached. Sound: implied bounds are advisory —
            // weaker propagation never changes a verdict.
            1
        } else if self.bcp_implied_single_pass {
            // Fix #2 (sat-side-model-search diagnosis): BCP-time restraint on the
            // propagation-disabled cex lane. The derived bounds have no surviving
            // BCP consumer here (propagate_impl discards them and BP_REFINE is a
            // no-op), so the multi-hop transitive cascade is pure per-check cost.
            // Cap to a single row-derivation pass; the full cascade still runs at
            // final check (bcp_mode=false), preserving eager-arm completeness.
            1
        } else if self.bcp_cascade_dry_streak >= 3 {
            self.stats.cascade_depth_throttles += 1;
            1
        } else {
            base_cascade_depth
        };
        let mut cascade_round = 0u32;
        let mut cascade_converged = true; // Set to false if we hit depth limit
        let mut deep_cascade_productive = false;
        // #cib-alloc: hoist the former per-round `Vec::new()` allocations to
        // persistent scratch, taken once and cleared per round below.
        let mut round_newly_bounded = std::mem::take(&mut self.ib_round_newly_bounded_scratch);
        let mut cross_neg_updates = std::mem::take(&mut self.ib_cross_neg_updates_scratch);
        let mut cascade_rows = std::mem::take(&mut self.ib_cascade_rows_scratch);
        loop {
            updates.clear();
            // #8008: Removed coefficient budget (#8257). Z3's
            // bound_analyzer_on_row has no coefficient budget. The budget was
            // preventing implied bound discovery on large tableaux, limiting
            // propagation cascades that Z3 exploits heavily.
            for &row_idx in row_indices.iter() {
                let row = &self.rows[row_idx];
                let bv = row.basic_var as usize;
                // #6617: unified row-width limit (was 100 here, 300 in the
                // old inline path). Z3's bound_analyzer_on_row has no width
                // cap. Shared constant ensures rows 101-300 are still covered
                // now that the inline bound-writing path is removed.
                if bv >= num_vars || row.coeffs.len() > Self::MAX_TOUCHED_ROW_BOUND_SCAN_WIDTH {
                    continue;
                }
                // #8003: Generation-based skip. If no variable in this row has had
                // its bound tightened since we last analyzed this row, the result
                // would be identical — skip the expensive arithmetic.
                //
                // #8857: Also applies to full sweeps (previously gated to the
                // touched-row path). A full sweep recurs whenever touched_rows
                // drains empty; rows whose input bounds have not changed since
                // their last analysis (row_gen > 0) would re-derive identical
                // bounds. After pop/reset the gen arrays are cleared (gen 0)
                // and after a full-scan overlay all vars are stamped newer, so
                // stale skips cannot occur on rebuild paths.
                if row_idx < self.row_computed_gen.len() {
                    let row_gen = self.row_computed_gen[row_idx];
                    if row_gen > 0 {
                        let mut any_newer = false;
                        if bv < self.var_bound_gen.len() && self.var_bound_gen[bv] > row_gen {
                            any_newer = true;
                        }
                        if !any_newer {
                            for &(var, _) in &row.coeffs {
                                let vi = var as usize;
                                if vi < self.var_bound_gen.len() && self.var_bound_gen[vi] > row_gen
                                {
                                    any_newer = true;
                                    break;
                                }
                            }
                        }
                        if !any_newer {
                            continue;
                        }
                    }
                }
                // #6615 Packet 3: Skip rows with pathologically large coefficients.
                // Z3's row_has_a_big_num() (lar_solver.cpp:373-378) skips rows with
                // coefficients exceeding ~1000 bits. Matching on Rational::Big is a
                // zero-cost proxy: most LRA coefficients are Small(i64, i64).
                if row
                    .coeffs
                    .iter()
                    .any(|(_, c)| matches!(c, Rational::Big(_)))
                {
                    continue;
                }
                // #8008: Budget check removed (was #8257).
                // #4919: Previously skipped rows with no unassigned atoms and
                // no refinement candidates. This optimization prevented the
                // fixpoint from discovering transitive bound implications:
                // deriving a bound for variable X in row A enables row B to
                // derive a bound for variable Y, even when neither X nor Y
                // has atoms. Z3's bound_analyzer_on_row has no such skip.
                // Removing this skip allows the current pass to discover row-local
                // implications, while cross-row cascading is handled by the next
                // compute_implied_bounds() call via touched_rows seeding below.

                // Build the full equation: x_b + sum((-a_j) * x_j) = constant
                // We analyze ALL variables in the equation (basic + nonbasic).
                //
                // Z3-style bound_analyzer_on_row algorithm:
                // Track how many variables lack needed bounds in each direction.
                // - 0 unbounded: derive bounds for ALL variables (O(n) trick)
                // - 1 unbounded: derive bound for that single variable
                // - 2+ unbounded: no derivation possible
                //
                // All arithmetic uses Rational (inline i64/i64) to avoid
                // BigRational heap allocation in the common case (#4919).

                // #7973: Two-pass approach for LB direction.
                // Pass 1: Cheap pre-scan to count unbounded variables (no arithmetic).
                // Pass 2: Full arithmetic only for rows with <=1 unbounded.
                // This avoids expensive Rational operations on rows where 2+ variables
                // lack bounds, which is the common case on LP-heavy benchmarks.
                let mut lb_unbounded_count = 0u32;
                let mut lb_prescan_valid = true;
                if self.implied_bounds[bv].0.is_none() {
                    lb_unbounded_count += 1;
                }
                if lb_unbounded_count < 2 {
                    for &(var, ref coeff) in &row.coeffs {
                        let vi = var as usize;
                        if vi >= num_vars {
                            lb_prescan_valid = false;
                            break;
                        }
                        let eq_c_pos = coeff.is_negative();
                        let has_bound = if eq_c_pos {
                            self.implied_bounds[vi].0.is_some()
                        } else {
                            self.implied_bounds[vi].1.is_some()
                        };
                        if !has_bound {
                            lb_unbounded_count += 1;
                            if lb_unbounded_count >= 2 {
                                break;
                            }
                        }
                    }
                }

                // Lower bound direction: compute sum of min contributions
                // For eq_coeff > 0: min = eq_coeff * lb(x)
                // For eq_coeff < 0: min = eq_coeff * ub(x)
                // Track strictness: derived bound is strict iff any contributing
                // bound is strict (Z3 infinitesimal model, #4919).
                let mut lb_total = Rational::zero();
                let mut lb_total_f64: f64 = 0.0; // #8200
                let mut lb_unbounded_idx: i32 = -1; // -1: none, >=0: exactly one, -2: multiple
                let mut lb_valid = true;
                let mut lb_any_strict = false;

                // Reuse pre-allocated contribution storage (cleared each row).
                // Each entry: (var_idx, eq_coeff, is_strict)
                lb_contribs.clear();
                lb_contribs_f64.clear();

                // #8003: f64 pre-screen for the "all bounded" (lb_unbounded_count==0) case.
                // Compute all implied bounds using ONLY f64 arithmetic. If none would be
                // tighter than existing bounds (with conservative margin), skip the entire
                // exact Rational accumulation for this direction. This eliminates most bignum
                // arithmetic on dense LP benchmarks where implied bounds are weaker than
                // existing direct bounds.
                let mut lb_f64_skip = false;
                if lb_prescan_valid
                    && lb_unbounded_count == 0
                    && row.coeffs.len() >= prescreen_min_width
                {
                    // #8003: Widen f64 pre-screen margin for dense rows. On wide sums
                    // (50+ terms), floating-point cancellation accumulates O(sqrt(n))
                    // relative error. 1e-9 is too tight and causes false negatives
                    // (declaring a row "might be tighter" when it's actually weaker).
                    // Use 1e-6 for dense rows, 1e-9 for narrow rows.
                    let prescreen_margin = if row.coeffs.len() > 30 { 1e-6 } else { 1e-9 };
                    let const_f64 = row.constant.approx_f64();
                    let mut lb_sum_f64: f64 = 0.0;
                    let mut f64_ok = const_f64.is_finite();
                    // Basic var contribution
                    if f64_ok {
                        if let Some(ref ib) = self.implied_bounds[bv].0 {
                            let v = ib.value.approx_f64();
                            if v.is_finite() {
                                lb_sum_f64 += v;
                            } else {
                                f64_ok = false;
                            }
                        } else {
                            f64_ok = false;
                        }
                    }
                    if f64_ok {
                        for &(var, ref coeff) in &row.coeffs {
                            let vi = var as usize;
                            if vi >= num_vars {
                                f64_ok = false;
                                break;
                            }
                            let eq_c_pos = coeff.is_negative();
                            let bound_ref = if eq_c_pos {
                                &self.implied_bounds[vi].0
                            } else {
                                &self.implied_bounds[vi].1
                            };
                            if let Some(ref ib) = bound_ref {
                                let ec_f64 = -(coeff.approx_f64());
                                let ib_f64 = ib.value.approx_f64();
                                let prod = ec_f64 * ib_f64;
                                if prod.is_finite() {
                                    lb_sum_f64 += prod;
                                } else {
                                    f64_ok = false;
                                    break;
                                }
                            } else {
                                f64_ok = false;
                                break; // unbounded (shouldn't happen with count==0)
                            }
                        }
                    }
                    if f64_ok && lb_sum_f64.is_finite() {
                        let rhs_f64 = const_f64 - lb_sum_f64;
                        let mut any_tighter = false;
                        // Check basic var: eq_c=+1 → derives upper bound
                        if let Some(ref bv_ib) = self.implied_bounds[bv].0 {
                            let bv_f64 = bv_ib.value.approx_f64();
                            let bnd = rhs_f64 + bv_f64; // (rhs_base + contrib) / eq_c, eq_c=1
                            if bnd.is_finite() {
                                if let Some(ref eb) = self.implied_bounds[bv].1 {
                                    let eb_f64 = eb.value.approx_f64();
                                    let margin = (eb_f64.abs() + 1.0) * prescreen_margin;
                                    if bnd < eb_f64 - margin {
                                        any_tighter = true;
                                    }
                                } else {
                                    any_tighter = true;
                                }
                            }
                        }
                        // Check each non-basic variable
                        if !any_tighter {
                            for &(var, ref coeff) in &row.coeffs {
                                let vi = var as usize;
                                if vi >= num_vars {
                                    break;
                                }
                                let ec_f64 = -(coeff.approx_f64());
                                if ec_f64.abs() < 1e-15 {
                                    continue;
                                }
                                let eq_c_pos = coeff.is_negative();
                                let contrib_ref = if eq_c_pos {
                                    &self.implied_bounds[vi].0
                                } else {
                                    &self.implied_bounds[vi].1
                                };
                                if let Some(ref ib) = contrib_ref {
                                    let cf64 = ec_f64 * ib.value.approx_f64();
                                    let bnd = (rhs_f64 + cf64) / ec_f64;
                                    if bnd.is_finite() {
                                        let is_upper = ec_f64 > 0.0;
                                        let existing = if is_upper {
                                            &self.implied_bounds[vi].1
                                        } else {
                                            &self.implied_bounds[vi].0
                                        };
                                        if let Some(ref eb) = existing {
                                            let eb_f64 = eb.value.approx_f64();
                                            let margin = (eb_f64.abs() + 1.0) * prescreen_margin;
                                            let tighter = if is_upper {
                                                bnd < eb_f64 - margin
                                            } else {
                                                bnd > eb_f64 + margin
                                            };
                                            if tighter {
                                                any_tighter = true;
                                                break;
                                            }
                                        } else {
                                            any_tighter = true;
                                            break;
                                        }
                                    }
                                }
                            }
                        }
                        if !any_tighter {
                            lb_f64_skip = true;
                            self.stats.f64_rows_skipped += 1;
                        }
                    }
                }

                // Skip the expensive arithmetic pass for rows with 2+ unbounded,
                // or when f64 pre-screen determined no bound would be tighter.
                if lb_prescan_valid && lb_unbounded_count < 2 && !lb_f64_skip {
                    // Basic var: eq_coeff = +1
                    let bv_eq_c = Rational::one();
                    match &self.implied_bounds[bv].0 {
                        Some(ib) => {
                            // #8003: bv_eq_c == 1 for basic var, so contrib == ib.value.
                            let contrib_f64 = ib.value.approx_f64();
                            lb_total += &ib.value; // eq_c=1, so total += bound
                            lb_total_f64 += contrib_f64;
                            lb_any_strict |= ib.strict;
                            lb_contribs.push((bv, bv_eq_c.clone(), ib.strict));
                            lb_contribs_f64.push(contrib_f64);
                        }
                        None => {
                            lb_contribs.push((bv, bv_eq_c.clone(), false));
                            lb_contribs_f64.push(0.0);
                            lb_unbounded_idx = 0; // index into lb_contribs
                        }
                    }

                    for &(var, ref coeff) in &row.coeffs {
                        let vi = var as usize;
                        if vi >= num_vars {
                            lb_valid = false;
                            break;
                        }
                        // #7973: Avoid computing -coeff; check coeff sign directly.
                        // eq_c = -coeff, so eq_c.is_positive() iff coeff.is_negative().
                        let eq_c_pos = coeff.is_negative();
                        let bound_ref = if eq_c_pos {
                            &self.implied_bounds[vi].0
                        } else {
                            &self.implied_bounds[vi].1
                        };
                        match bound_ref {
                            Some(ib) => {
                                // #8406: Use neg_small fast path to avoid enum dispatch.
                                let eq_c = coeff.neg_small().unwrap_or_else(|| -coeff);
                                let eq_c_f64 = eq_c.approx_f64();
                                let ib_f64 = ib.value.approx_f64();
                                let cf64 = eq_c_f64 * ib_f64;
                                // #8406: Fused multiply-add without product return.
                                // Uses mul_add_assign which skips the product GCD
                                // reduction step since we only need the accumulated total.
                                lb_total.mul_add_assign(&eq_c, &ib.value);
                                lb_any_strict |= ib.strict;
                                lb_total_f64 += cf64;
                                lb_contribs.push((vi, eq_c, ib.strict));
                                lb_contribs_f64.push(cf64);
                            }
                            None => {
                                // Exactly one unbounded (pre-scan guaranteed <=1).
                                // #8406: Use neg_small fast path.
                                let eq_c = coeff.neg_small().unwrap_or_else(|| -coeff);
                                lb_contribs.push((vi, eq_c, false));
                                lb_contribs_f64.push(0.0);
                                lb_unbounded_idx = (lb_contribs.len() - 1) as i32;
                            }
                        }
                    }
                } else {
                    lb_valid = lb_prescan_valid;
                    lb_unbounded_idx = -2; // 2+ unbounded
                }

                if lb_valid {
                    if lb_unbounded_idx == -1 {
                        // ALL variables bounded: derive bound for each variable.
                        // Strictness fix (#6242): when deriving a bound for variable vi,
                        // the strictness should be the OR of all OTHER variables'
                        // contributing bound strictness (excluding vi's own bound).
                        // Using lb_any_strict for all variables is unsound when only one
                        // variable contributes a strict bound — the derivation for THAT
                        // variable should NOT be strict.
                        let lb_strict_count = lb_contribs.iter().filter(|c| c.2).count();
                        let rhs_base = &row.constant - &lb_total;
                        let rhs_base_f64 = row.constant.approx_f64() - lb_total_f64; // #8200
                                                                                     // #8003: Dense row optimization. For rows with many coefficients,
                                                                                     // building BoundExplanation for each derived variable is O(n^2)
                                                                                     // because each explanation iterates all other variables. On dense
                                                                                     // LP benchmarks (rand_70_300, vpm2-30 with 50+ coefficients per
                                                                                     // row), this SmallVec construction dominates runtime per profile.
                                                                                     // Skip eager explanation for dense rows; the fallback
                                                                                     // collect_row_reasons_recursive() reconstructs from row_idx.
                                                                                     //
                                                                                     // Also widen the f64 pre-screen margin for dense rows because
                                                                                     // floating-point cancellation on wide sums makes 1e-9 too tight.
                        let row_width = lb_contribs.len();
                        let skip_eager_explanation = row_width > 30;
                        let f64_margin_factor = if row_width > 30 { 1e-6 } else { 1e-9 };
                        // #8008: Removed BigRational rhs_base bailout (#8800). f64 pre-screen filters weak bounds.
                        for (ci, &(vi, ref eq_c, var_strict)) in lb_contribs.iter().enumerate() {
                            if eq_c.is_zero() {
                                continue;
                            }
                            let is_upper = eq_c.is_positive();
                            // #8257: f64 pre-screen for LB direction.
                            let ec_f64 = eq_c.approx_f64();
                            if ec_f64.abs() > 1e-15 {
                                let cf = lb_contribs_f64[ci];
                                let bnd_f64 = (rhs_base_f64 + cf) / ec_f64;
                                if bnd_f64.is_finite() {
                                    let existing = if is_upper {
                                        &self.implied_bounds[vi].1
                                    } else {
                                        &self.implied_bounds[vi].0
                                    };
                                    if let Some(ref eb) = existing {
                                        let eb_f64 = eb.value.approx_f64();
                                        let margin = (eb_f64.abs() + 1.0) * f64_margin_factor;
                                        let weaker = if is_upper {
                                            bnd_f64 >= eb_f64 + margin
                                        } else {
                                            bnd_f64 <= eb_f64 - margin
                                        };
                                        if weaker {
                                            self.stats.f64_vars_skipped += 1;
                                            continue;
                                        }
                                    }
                                }
                            }
                            // #8003: Z3-style derivation without storing per-variable contrib.
                            // bound_val = rhs_base / eq_c + bound_j, where bound_j is the
                            // bound we used for variable vi during accumulation. This avoids
                            // storing a BigRational contrib per variable.
                            // LB direction: eq_c > 0 used lb(vi), eq_c < 0 used ub(vi).
                            // #8406: Use div_add_small to fuse division+addition in one
                            // i128 pass, avoiding two separate GCD reductions.
                            let bound_val = {
                                let bound_ref = if eq_c.is_positive() {
                                    &self.implied_bounds[vi].0
                                } else {
                                    &self.implied_bounds[vi].1
                                };
                                match bound_ref {
                                    Some(ib_ref) => rhs_base
                                        .div_add_small(eq_c, &ib_ref.value)
                                        .unwrap_or_else(|| &(&rhs_base / eq_c) + &ib_ref.value),
                                    None => &rhs_base / eq_c,
                                }
                            };
                            // derived_strict = any OTHER variable's bound was strict
                            let derived_strict = if lb_strict_count >= 2 {
                                true // multiple strict bounds -> all derivations are strict
                            } else if lb_strict_count == 1 {
                                !var_strict // strict only if THIS variable wasn't the strict one
                            } else {
                                false // no strict bounds at all
                            };
                            // #8422: Do NOT filter bounds at the LP derivation level.
                            // Z3's bound_analyzer_on_row stores ALL derived bounds and
                            // only checks interest at the propagation level (arith_solver.cpp:363).
                            // Filtering here blocks cascade derivation: variable X might
                            // have atom x >= 10, and we derive x >= 3 (not directly
                            // interesting). But x >= 3 enables Y's row to derive y <= 5,
                            // which IS interesting. Previously #6615 filtered x >= 3
                            // and blocked the cascade.
                            //
                            // For bounds that won't directly imply atoms, skip the
                            // expensive explanation building (O(n) SmallVec construction)
                            // but still store the bound value for cascade derivation.
                            let interesting =
                                self.bound_is_interesting(vi as u32, is_upper, &bound_val);
                            // #6617: Build eager explanation -- all OTHER variables that
                            // contributed bounds in this LB direction derivation.
                            // LB direction: eq_c > 0 used lower bound, eq_c < 0 used upper.
                            // #8003: Skip eager explanation for dense rows (>30 coefficients)
                            // to avoid O(n^2) SmallVec construction. The fallback
                            // collect_row_reasons_recursive() uses row_idx to reconstruct.
                            // #8422: Also skip explanation for non-interesting bounds
                            // (these are only stored for cascade, not for propagation).
                            let explanation = if skip_eager_explanation || !interesting {
                                None
                            } else {
                                let mut contributing_vars = SmallVec::new();
                                for &(other_vi, ref other_eq_c, _) in &lb_contribs {
                                    if other_vi == vi {
                                        continue;
                                    }
                                    let used_upper = other_eq_c.is_negative();
                                    contributing_vars.push((other_vi as u32, used_upper));
                                }
                                Some(BoundExplanation { contributing_vars })
                            };
                            let ib = ImpliedBound {
                                value: bound_val,
                                strict: derived_strict,
                                row_idx,
                                explanation,
                            };
                            if is_upper {
                                updates.push((vi, None, Some(ib)));
                            } else {
                                updates.push((vi, Some(ib), None));
                            }
                        }
                    } else if lb_unbounded_idx >= 0 {
                        // Exactly one unbounded: derive bound for that variable.
                        let idx = lb_unbounded_idx as usize;
                        let (target_vi, ref eq_c, _) = lb_contribs[idx];
                        if !eq_c.is_zero() {
                            let rhs = &row.constant - &lb_total;
                            let bound_val = &rhs / eq_c;
                            let is_upper = eq_c.is_positive();
                            // #8782: Always store single-unbounded implied bounds.
                            // This variable had NO bound on this side before; the new
                            // bound is genuine new information for cascade derivations.
                            // Z3 applies bound_is_interesting at the propagation layer,
                            // not at LP-level derivation. Filtering here blocks
                            // transitive cascades through intermediate variables.
                            {
                                let derived_strict = lb_any_strict;
                                // #6617: Build eager explanation -- all other variables.
                                let mut contributing_vars = SmallVec::new();
                                for &(other_vi, ref other_eq_c, _) in &lb_contribs {
                                    if other_vi == target_vi {
                                        continue;
                                    }
                                    let used_upper = other_eq_c.is_negative();
                                    contributing_vars.push((other_vi as u32, used_upper));
                                }
                                let ib = ImpliedBound {
                                    value: bound_val,
                                    strict: derived_strict,
                                    row_idx,
                                    explanation: Some(BoundExplanation { contributing_vars }),
                                };
                                if is_upper {
                                    updates.push((target_vi, None, Some(ib)));
                                } else {
                                    updates.push((target_vi, Some(ib), None));
                                }
                            }
                        }
                    }
                    // lb_unbounded_idx == -2: 2+ unbounded, skip
                }

                // #7973: Two-pass approach for UB direction (symmetric with LB).
                let mut ub_unbounded_count = 0u32;
                let mut ub_prescan_valid = true;
                if self.implied_bounds[bv].1.is_none() {
                    ub_unbounded_count += 1;
                }
                if ub_unbounded_count < 2 {
                    for &(var, ref coeff) in &row.coeffs {
                        let vi = var as usize;
                        if vi >= num_vars {
                            ub_prescan_valid = false;
                            break;
                        }
                        let eq_c_pos = coeff.is_negative();
                        let has_bound = if eq_c_pos {
                            self.implied_bounds[vi].1.is_some()
                        } else {
                            self.implied_bounds[vi].0.is_some()
                        };
                        if !has_bound {
                            ub_unbounded_count += 1;
                            if ub_unbounded_count >= 2 {
                                break;
                            }
                        }
                    }
                }

                // Upper bound direction (symmetric): sum of max contributions
                let mut ub_total = Rational::zero();
                let mut ub_total_f64: f64 = 0.0; // #8200
                let mut ub_unbounded_idx: i32 = -1;
                let mut ub_valid = true;
                let mut ub_any_strict = false;
                ub_contribs.clear();
                ub_contribs_f64.clear();

                // #8003: f64 pre-screen for UB direction (symmetric with LB above).
                let mut ub_f64_skip = false;
                if ub_prescan_valid
                    && ub_unbounded_count == 0
                    && row.coeffs.len() >= prescreen_min_width
                {
                    // #8003: Dense row margin (symmetric with LB).
                    let ub_prescreen_margin = if row.coeffs.len() > 30 { 1e-6 } else { 1e-9 };
                    let const_f64 = row.constant.approx_f64();
                    let mut ub_sum_f64: f64 = 0.0;
                    let mut f64_ok = const_f64.is_finite();
                    if f64_ok {
                        if let Some(ref ib) = self.implied_bounds[bv].1 {
                            let v = ib.value.approx_f64();
                            if v.is_finite() {
                                ub_sum_f64 += v;
                            } else {
                                f64_ok = false;
                            }
                        } else {
                            f64_ok = false;
                        }
                    }
                    if f64_ok {
                        for &(var, ref coeff) in &row.coeffs {
                            let vi = var as usize;
                            if vi >= num_vars {
                                f64_ok = false;
                                break;
                            }
                            let eq_c_pos = coeff.is_negative();
                            let bound_ref = if eq_c_pos {
                                &self.implied_bounds[vi].1
                            } else {
                                &self.implied_bounds[vi].0
                            };
                            if let Some(ref ib) = bound_ref {
                                let ec_f64 = -(coeff.approx_f64());
                                let ib_f64 = ib.value.approx_f64();
                                let prod = ec_f64 * ib_f64;
                                if prod.is_finite() {
                                    ub_sum_f64 += prod;
                                } else {
                                    f64_ok = false;
                                    break;
                                }
                            } else {
                                f64_ok = false;
                                break;
                            }
                        }
                    }
                    if f64_ok && ub_sum_f64.is_finite() {
                        let rhs_f64 = const_f64 - ub_sum_f64;
                        let mut any_tighter = false;
                        // Basic var: eq_c=+1, UB direction → derives lower bound
                        if let Some(ref bv_ib) = self.implied_bounds[bv].1 {
                            let bv_f64 = bv_ib.value.approx_f64();
                            let bnd = rhs_f64 + bv_f64;
                            if bnd.is_finite() {
                                if let Some(ref eb) = self.implied_bounds[bv].0 {
                                    let eb_f64 = eb.value.approx_f64();
                                    let margin = (eb_f64.abs() + 1.0) * ub_prescreen_margin;
                                    if bnd > eb_f64 + margin {
                                        any_tighter = true;
                                    }
                                } else {
                                    any_tighter = true;
                                }
                            }
                        }
                        if !any_tighter {
                            for &(var, ref coeff) in &row.coeffs {
                                let vi = var as usize;
                                if vi >= num_vars {
                                    break;
                                }
                                let ec_f64 = -(coeff.approx_f64());
                                if ec_f64.abs() < 1e-15 {
                                    continue;
                                }
                                let eq_c_pos = coeff.is_negative();
                                let contrib_ref = if eq_c_pos {
                                    &self.implied_bounds[vi].1
                                } else {
                                    &self.implied_bounds[vi].0
                                };
                                if let Some(ref ib) = contrib_ref {
                                    let cf64 = ec_f64 * ib.value.approx_f64();
                                    let bnd = (rhs_f64 + cf64) / ec_f64;
                                    if bnd.is_finite() {
                                        let is_upper = ec_f64 <= 0.0;
                                        let existing = if is_upper {
                                            &self.implied_bounds[vi].1
                                        } else {
                                            &self.implied_bounds[vi].0
                                        };
                                        if let Some(ref eb) = existing {
                                            let eb_f64 = eb.value.approx_f64();
                                            let margin = (eb_f64.abs() + 1.0) * ub_prescreen_margin;
                                            let tighter = if is_upper {
                                                bnd < eb_f64 - margin
                                            } else {
                                                bnd > eb_f64 + margin
                                            };
                                            if tighter {
                                                any_tighter = true;
                                                break;
                                            }
                                        } else {
                                            any_tighter = true;
                                            break;
                                        }
                                    }
                                }
                            }
                        }
                        if !any_tighter {
                            ub_f64_skip = true;
                            self.stats.f64_rows_skipped += 1;
                        }
                    }
                }

                if ub_prescan_valid && ub_unbounded_count < 2 && !ub_f64_skip {
                    // Basic var: eq_coeff = +1, max contribution = ub(x_b)
                    let bv_eq_c_ub = Rational::one();
                    match &self.implied_bounds[bv].1 {
                        Some(ib) => {
                            // #8003: bv_eq_c == 1 for basic var, so contrib == ib.value.
                            let contrib_f64 = ib.value.approx_f64();
                            ub_total += &ib.value; // eq_c=1, so total += bound
                            ub_total_f64 += contrib_f64;
                            ub_any_strict |= ib.strict;
                            ub_contribs.push((bv, bv_eq_c_ub.clone(), ib.strict));
                            ub_contribs_f64.push(contrib_f64);
                        }
                        None => {
                            ub_contribs.push((bv, bv_eq_c_ub.clone(), false));
                            ub_contribs_f64.push(0.0);
                            ub_unbounded_idx = 0;
                        }
                    }

                    for &(var, ref coeff) in &row.coeffs {
                        let vi = var as usize;
                        if vi >= num_vars {
                            ub_valid = false;
                            break;
                        }
                        // #7973: Same sign-check optimization as LB direction.
                        let eq_c_pos = coeff.is_negative();
                        let bound_ref = if eq_c_pos {
                            &self.implied_bounds[vi].1
                        } else {
                            &self.implied_bounds[vi].0
                        };
                        match bound_ref {
                            Some(ib) => {
                                // #8406: Use neg_small fast path to avoid enum dispatch.
                                let eq_c = coeff.neg_small().unwrap_or_else(|| -coeff);
                                let eq_c_f64 = eq_c.approx_f64();
                                let ib_f64 = ib.value.approx_f64();
                                let cf64 = eq_c_f64 * ib_f64;
                                // #8406: Fused multiply-add without product return
                                // (see LB direction comment for rationale).
                                ub_total.mul_add_assign(&eq_c, &ib.value);
                                ub_any_strict |= ib.strict;
                                ub_total_f64 += cf64;
                                ub_contribs.push((vi, eq_c, ib.strict));
                                ub_contribs_f64.push(cf64);
                            }
                            None => {
                                // Exactly one unbounded (pre-scan guaranteed <=1).
                                // #8406: Use neg_small fast path.
                                let eq_c = coeff.neg_small().unwrap_or_else(|| -coeff);
                                ub_contribs.push((vi, eq_c, false));
                                ub_contribs_f64.push(0.0);
                                ub_unbounded_idx = (ub_contribs.len() - 1) as i32;
                            }
                        }
                    }
                } else {
                    ub_valid = ub_prescan_valid;
                    ub_unbounded_idx = -2; // 2+ unbounded
                }

                if ub_valid {
                    if ub_unbounded_idx == -1 {
                        // ALL bounded: derive upper bound for each variable.
                        // Strictness fix (#6242): same as lower bound direction --
                        // exclude vi's own contribution from strictness aggregation.
                        let ub_strict_count = ub_contribs.iter().filter(|c| c.2).count();
                        let rhs_base = &row.constant - &ub_total;
                        let rhs_base_f64 = row.constant.approx_f64() - ub_total_f64; // #8200
                                                                                     // #8003: Dense row optimization (symmetric with LB direction).
                        let ub_row_width = ub_contribs.len();
                        let ub_skip_eager_explanation = ub_row_width > 30;
                        let ub_f64_margin_factor = if ub_row_width > 30 { 1e-6 } else { 1e-9 };
                        // #8008: Removed BigRational rhs_base bailout (#8800) -- see LB direction.
                        for (ci, &(vi, ref eq_c, var_strict)) in ub_contribs.iter().enumerate() {
                            if eq_c.is_zero() {
                                continue;
                            }
                            // In UB direction: positive coeff -> lower bound, negative -> upper.
                            let is_upper = !eq_c.is_positive();
                            // #8200: f64 pre-screen (symmetric with LB direction).
                            let ec_f64 = eq_c.approx_f64();
                            if ec_f64.abs() > 1e-15 {
                                let cf = ub_contribs_f64[ci];
                                let bnd_f64 = (rhs_base_f64 + cf) / ec_f64;
                                if bnd_f64.is_finite() {
                                    let existing = if is_upper {
                                        &self.implied_bounds[vi].1
                                    } else {
                                        &self.implied_bounds[vi].0
                                    };
                                    if let Some(ref eb) = existing {
                                        let eb_f64 = eb.value.approx_f64();
                                        let margin = (eb_f64.abs() + 1.0) * ub_f64_margin_factor;
                                        let weaker = if is_upper {
                                            bnd_f64 >= eb_f64 + margin
                                        } else {
                                            bnd_f64 <= eb_f64 - margin
                                        };
                                        if weaker {
                                            self.stats.f64_vars_skipped += 1;
                                            continue;
                                        }
                                    }
                                }
                            }
                            // #8003: Z3-style derivation (see LB direction comment).
                            // UB direction: eq_c > 0 used ub(vi), eq_c < 0 used lb(vi).
                            // #8406: Use div_add_small to fuse division+addition in one
                            // i128 pass (see LB direction comment for rationale).
                            let bound_val = {
                                let bound_ref = if eq_c.is_positive() {
                                    &self.implied_bounds[vi].1
                                } else {
                                    &self.implied_bounds[vi].0
                                };
                                match bound_ref {
                                    Some(ib_ref) => rhs_base
                                        .div_add_small(eq_c, &ib_ref.value)
                                        .unwrap_or_else(|| &(&rhs_base / eq_c) + &ib_ref.value),
                                    None => &rhs_base / eq_c,
                                }
                            };
                            let derived_strict = if ub_strict_count >= 2 {
                                true
                            } else if ub_strict_count == 1 {
                                !var_strict
                            } else {
                                false
                            };
                            // #8422: Do NOT filter bounds at the LP derivation level.
                            // (See LB direction comment above for full rationale.)
                            let interesting =
                                self.bound_is_interesting(vi as u32, is_upper, &bound_val);
                            // #6617: Build eager explanation for UB direction.
                            // UB direction: eq_c > 0 used upper bound, eq_c < 0 used lower.
                            // #8003: Skip eager explanation for dense rows (see LB direction).
                            // #8422: Also skip explanation for non-interesting bounds
                            // (cascade-only, not directly propagation-useful).
                            let explanation = if ub_skip_eager_explanation || !interesting {
                                None
                            } else {
                                let mut contributing_vars = SmallVec::new();
                                for &(other_vi, ref other_eq_c, _) in &ub_contribs {
                                    if other_vi == vi {
                                        continue;
                                    }
                                    let used_upper = other_eq_c.is_positive();
                                    contributing_vars.push((other_vi as u32, used_upper));
                                }
                                Some(BoundExplanation { contributing_vars })
                            };
                            let ib = ImpliedBound {
                                value: bound_val,
                                strict: derived_strict,
                                row_idx,
                                explanation,
                            };
                            if eq_c.is_positive() {
                                updates.push((vi, Some(ib), None));
                            } else {
                                updates.push((vi, None, Some(ib)));
                            }
                        }
                    } else if ub_unbounded_idx >= 0 {
                        let idx = ub_unbounded_idx as usize;
                        let (target_vi, ref eq_c, _) = ub_contribs[idx];
                        if !eq_c.is_zero() {
                            let rhs = &row.constant - &ub_total;
                            let bound_val = &rhs / eq_c;
                            // #8782: Always store single-unbounded implied bounds
                            // (see LB single-unbounded path comment above).
                            {
                                let derived_strict = ub_any_strict;
                                // #6617: Build eager explanation for UB single-unbounded.
                                let mut contributing_vars = SmallVec::new();
                                for &(other_vi, ref other_eq_c, _) in &ub_contribs {
                                    if other_vi == target_vi {
                                        continue;
                                    }
                                    let used_upper = other_eq_c.is_positive();
                                    contributing_vars.push((other_vi as u32, used_upper));
                                }
                                let ib = ImpliedBound {
                                    value: bound_val,
                                    strict: derived_strict,
                                    row_idx,
                                    explanation: Some(BoundExplanation { contributing_vars }),
                                };
                                if eq_c.is_positive() {
                                    updates.push((target_vi, Some(ib), None));
                                } else {
                                    updates.push((target_vi, None, Some(ib)));
                                }
                            }
                        }
                    }
                }
                // #8003: Stamp row generation after processing so it can be skipped
                // on the next iteration if no input bound changes.
                if row_idx < self.row_computed_gen.len() {
                    self.row_computed_gen[row_idx] = self.bound_generation;
                }
            }

            // Apply deferred updates (only tighten, with strict-aware comparison).
            // Track which variables got tighter bounds THIS round for cascade.
            round_newly_bounded.clear();
            for (vi, new_lb, new_ub) in updates.drain(..) {
                let mut any_tighter = false;
                if let Some(new_ib) = new_lb {
                    let cur = &self.implied_bounds[vi].0;
                    let tighter = match cur {
                        None => true,
                        Some(cur_ib) => {
                            new_ib.value > cur_ib.value
                                || (new_ib.value == cur_ib.value && new_ib.strict && !cur_ib.strict)
                        }
                    };
                    // #8857: Zeno-cascade throttle. Replacing tightenings beyond
                    // the per-variable streak cap must cross an atom threshold.
                    if tighter
                        && self.derived_bound_worth_storing(vi as u32, false, &new_ib.value)
                        && self.accept_replacing_tighten(vi, cur.is_some(), false, &new_ib)
                    {
                        // Mark variable as dirty for interval propagation (#4919).
                        // Previously only variables with NO direct bound were marked,
                        // but tightened implied bounds can also enable new multi-variable
                        // interval propagations via compute_expr_interval().
                        newly_bounded.insert(vi as u32);
                        if self.implied_tighten_scratch[vi] == 0 {
                            self.implied_tighten_touched.push(vi as u32);
                        }
                        self.implied_tighten_scratch[vi] =
                            self.implied_tighten_scratch[vi].saturating_add(1);
                        // #inc-implied-trail: record the displaced value for
                        // O(popped) pop-restore (zero-clone move).
                        let old = self.implied_bounds[vi].0.replace(new_ib);
                        self.implied_trail.push((vi as u32, false, old));
                        // #8003: Stamp variable generation so rows containing it
                        // will be re-analyzed on the next iteration — but only
                        // within the tighten budget: over-budget re-tightenings
                        // are stored (valid) without re-triggering row analysis.
                        if self.implied_tighten_scratch[vi] <= MAX_TIGHTENS_PER_VAR {
                            round_newly_bounded.push(vi as u32);
                            self.bound_generation += 1;
                            if vi < self.var_bound_gen.len() {
                                self.var_bound_gen[vi] = self.bound_generation;
                            }
                        }
                        any_tighter = true;
                    }
                }
                if let Some(new_ib) = new_ub {
                    let cur = &self.implied_bounds[vi].1;
                    let tighter = match cur {
                        None => true,
                        Some(cur_ib) => {
                            new_ib.value < cur_ib.value
                                || (new_ib.value == cur_ib.value && new_ib.strict && !cur_ib.strict)
                        }
                    };
                    // #8857: Zeno-cascade throttle (see lower-bound arm).
                    if tighter
                        && self.derived_bound_worth_storing(vi as u32, true, &new_ib.value)
                        && self.accept_replacing_tighten(vi, cur.is_some(), true, &new_ib)
                    {
                        // Mark variable as dirty for interval propagation (#4919).
                        newly_bounded.insert(vi as u32);
                        if self.implied_tighten_scratch[vi] == 0 {
                            self.implied_tighten_touched.push(vi as u32);
                        }
                        self.implied_tighten_scratch[vi] =
                            self.implied_tighten_scratch[vi].saturating_add(1);
                        // #inc-implied-trail: see the lower-bound twin above.
                        let old = self.implied_bounds[vi].1.replace(new_ib);
                        self.implied_trail.push((vi as u32, true, old));
                        // #8003: Stamp variable generation (within the tighten
                        // budget only — see the lower-bound twin above).
                        if self.implied_tighten_scratch[vi] <= MAX_TIGHTENS_PER_VAR {
                            round_newly_bounded.push(vi as u32);
                            self.bound_generation += 1;
                            if vi < self.var_bound_gen.len() {
                                self.var_bound_gen[vi] = self.bound_generation;
                            }
                        }
                        any_tighter = true;
                    }
                }
                // #8255: Only re-check fixed-term status when a bound actually
                // tightened. Must be called AFTER both LB and UB are updated to
                // avoid intermediate states where only one bound is current.
                if any_tighter {
                    self.register_fixed_term_var(vi as u32);
                }
            }
            // #8008: Cross-negation bound propagation. For each newly-bounded
            // slack variable with a negation partner, derive the partner's
            // implied bound from the identity S1 + S2 = K:
            //   UB(S1) tightened => LB(S2) = K - UB(S1)
            //   LB(S1) tightened => UB(S2) = K - LB(S1)
            {
                cross_neg_updates.clear();
                for &vi in &newly_bounded {
                    let vi_usize = vi as usize;
                    if vi_usize >= self.negation_partners.len() {
                        continue;
                    }
                    let Some((partner, ref k_const)) = self.negation_partners[vi_usize] else {
                        continue;
                    };
                    let partner_usize = partner as usize;
                    if partner_usize >= self.implied_bounds.len() {
                        continue;
                    }
                    if let Some(ref ub) = self.implied_bounds[vi_usize].1 {
                        let partner_lb_val = k_const - &ub.value;
                        let partner_lb = ImpliedBound {
                            value: partner_lb_val,
                            strict: ub.strict,
                            row_idx: ub.row_idx,
                            explanation: None,
                        };
                        cross_neg_updates.push((partner_usize, Some(partner_lb), None));
                    }
                    if let Some(ref lb) = self.implied_bounds[vi_usize].0 {
                        let partner_ub_val = k_const - &lb.value;
                        let partner_ub = ImpliedBound {
                            value: partner_ub_val,
                            strict: lb.strict,
                            row_idx: lb.row_idx,
                            explanation: None,
                        };
                        cross_neg_updates.push((partner_usize, None, Some(partner_ub)));
                    }
                }
                for (vi, new_lb, new_ub) in cross_neg_updates.drain(..) {
                    if let Some(new_ib) = new_lb {
                        let cur = &self.implied_bounds[vi].0;
                        let tighter = match cur {
                            None => true,
                            Some(cur_ib) => {
                                new_ib.value > cur_ib.value
                                    || (new_ib.value == cur_ib.value
                                        && new_ib.strict
                                        && !cur_ib.strict)
                            }
                        };
                        // #8857: Zeno-cascade throttle (see main update loop).
                        if tighter
                            && self.derived_bound_worth_storing(vi as u32, false, &new_ib.value)
                            && self.accept_replacing_tighten(vi, cur.is_some(), false, &new_ib)
                        {
                            newly_bounded.insert(vi as u32);
                            // #inc-implied-trail: trailed for pop-restore.
                            let old = self.implied_bounds[vi].0.replace(new_ib);
                            self.implied_trail.push((vi as u32, false, old));
                            self.bound_generation += 1;
                            if vi < self.var_bound_gen.len() {
                                self.var_bound_gen[vi] = self.bound_generation;
                            }
                        }
                    }
                    if let Some(new_ib) = new_ub {
                        let cur = &self.implied_bounds[vi].1;
                        let tighter = match cur {
                            None => true,
                            Some(cur_ib) => {
                                new_ib.value < cur_ib.value
                                    || (new_ib.value == cur_ib.value
                                        && new_ib.strict
                                        && !cur_ib.strict)
                            }
                        };
                        // #8857: Zeno-cascade throttle (see main update loop).
                        if tighter
                            && self.derived_bound_worth_storing(vi as u32, true, &new_ib.value)
                            && self.accept_replacing_tighten(vi, cur.is_some(), true, &new_ib)
                        {
                            newly_bounded.insert(vi as u32);
                            // #inc-implied-trail: trailed for pop-restore.
                            let old = self.implied_bounds[vi].1.replace(new_ib);
                            self.implied_trail.push((vi as u32, true, old));
                            self.bound_generation += 1;
                            if vi < self.var_bound_gen.len() {
                                self.var_bound_gen[vi] = self.bound_generation;
                            }
                        }
                    }
                }
            }

            // #8008: Cascade bound propagation -- if this round derived new bounds,
            // look up all rows containing those variables and process them in the
            // next cascade round.
            cascade_round += 1;
            if !round_newly_bounded.is_empty() && cascade_round > 1 {
                deep_cascade_productive = true;
            }
            if round_newly_bounded.is_empty() {
                // Natural convergence: no new bounds this round.
                if cascade_round > self.stats.max_inner_cascade_depth {
                    self.stats.max_inner_cascade_depth = cascade_round;
                }
                self.stats.total_inner_cascade_rounds += u64::from(cascade_round);
                break;
            }
            round_newly_bounded.sort_unstable();
            round_newly_bounded.dedup();
            // #8255: Track whether cascade rounds beyond the first are productive.
            if cascade_round >= 2 {
                deep_cascade_productive = true;
            }
            if cascade_round >= max_cascade_depth {
                // Hit depth limit -- convergence not guaranteed.
                cascade_converged = false;
                if cascade_round > self.stats.max_inner_cascade_depth {
                    self.stats.max_inner_cascade_depth = cascade_round;
                }
                self.stats.total_inner_cascade_rounds += u64::from(cascade_round);
                break;
            }

            cascade_rows.clear();
            for &vi in &round_newly_bounded {
                let vi_usize = vi as usize;
                if vi_usize < self.col_index.len() {
                    for entry in &self.col_index[vi_usize] {
                        cascade_rows.push(entry.row_idx);
                    }
                }
                if let Some(&ri) = self.basic_var_to_row.get(&vi) {
                    cascade_rows.push(ri);
                }
            }
            cascade_rows.sort_unstable();
            cascade_rows.dedup();
            if cascade_rows.is_empty() {
                break;
            }

            row_indices.clear();
            row_indices.extend(cascade_rows.iter().copied());

            if self.debug_lra {
                safe_eprintln!(
                    "[LRA] Cascade round {}: {} newly bounded vars, {} cascade rows",
                    cascade_round,
                    round_newly_bounded.len(),
                    row_indices.len(),
                );
            }
        } // end cascade loop

        // #cib-alloc: restore the scratch buffers for the next call. Contents
        // are irrelevant (every use clears before writing); only the heap
        // allocations are retained, which is the point.
        self.ib_lb_contribs_scratch = lb_contribs;
        self.ib_ub_contribs_scratch = ub_contribs;
        self.ib_lb_contribs_f64_scratch = lb_contribs_f64;
        self.ib_ub_contribs_f64_scratch = ub_contribs_f64;
        self.ib_updates_scratch = updates;
        self.ib_row_indices_scratch = row_indices;
        self.ib_round_newly_bounded_scratch = round_newly_bounded;
        self.ib_cross_neg_updates_scratch = cross_neg_updates;
        self.ib_cascade_rows_scratch = cascade_rows;

        // #inc-cib-nodelta: this call swept every row, so the persistent
        // overlay is now complete for the current row set — repeat calls with
        // no new inputs can skip their (provably empty) full sweep.
        if was_full_sweep {
            self.ib_overlay_complete = true;
            self.rows_len_at_last_implied = self.rows.len();
        }

        // #4919: Seed touched_rows with rows containing newly-bounded
        // variables. This enables cascading across check() calls: bounds
        // derived in this fixpoint enable further derivations in the NEXT
        // compute_implied_bounds() call. Without this, the next call only
        // analyzes rows touched by new assert_var_bound calls (from BCP-fed
        // atom assertions), missing rows that could now derive bounds thanks
        // to the implied bounds we just computed.
        //
        // Clear first, then seed with cascade rows. New assert_var_bound
        // calls will add their own rows on top.
        self.touched_rows.clear();
        for &vi in &newly_bounded {
            let vi_usize = vi as usize;
            if vi_usize < self.col_index.len() {
                for entry in &self.col_index[vi_usize] {
                    self.touched_rows.insert(entry.row_idx);
                }
            }
            if let Some(&ri) = self.basic_var_to_row.get(&vi) {
                self.touched_rows.insert(ri);
            }
        }
        // #8008: Budget-break re-insertion removed (was #8257).
        ImpliedBoundsResult {
            newly_bounded,
            converged: cascade_converged,
            deep_cascade_productive,
        }
    }

    /// Decide whether a "tighter" implied-bound update may be stored (#8857).
    ///
    /// First bounds on a previously-unbounded side (`replacing == false`) are
    /// always stored and never counted: they are genuinely new information
    /// and there are at most `2 * num_vars` of them per assertion scope.
    ///
    /// Replacing tightenings are counted per variable. Beyond
    /// `IMPLIED_TIGHTEN_STREAK_CAP`, a replacing tightening is only stored
    /// when it crosses an atom threshold (`bound_is_interesting`). This
    /// breaks Zeno cascades on cyclic tableaus where each round derives an
    /// epsilon-tighter bound forever (with exponentially growing rational
    /// denominators), while preserving every propagation-relevant bound:
    /// atom thresholds are finite, so all interesting tightenings still land.
    ///
    /// Discarding a derived bound is always sound — it only weakens
    /// propagation, never changes verdicts.
    #[inline]
    fn accept_replacing_tighten(
        &mut self,
        vi: usize,
        replacing: bool,
        is_upper: bool,
        new_ib: &ImpliedBound,
    ) -> bool {
        /// Maximum replacing tightenings stored per variable (between direct
        /// bound changes) before requiring atom-threshold crossings.
        const IMPLIED_TIGHTEN_STREAK_CAP: u32 = 8;
        if !replacing {
            return true;
        }
        if vi >= self.implied_tighten_streak.len() {
            return true;
        }
        if self.implied_tighten_streak[vi] < IMPLIED_TIGHTEN_STREAK_CAP {
            self.implied_tighten_streak[vi] += 1;
            return true;
        }
        self.bound_crosses_unassigned_atom(vi as u32, is_upper, &new_ib.value)
    }

    /// Strict atom-threshold predicate for the Zeno throttle (#8857).
    ///
    /// Returns true only when the candidate bound directly implies or
    /// falsifies an UNASSIGNED atom on `var`. Unlike `bound_is_interesting`
    /// (which conservatively defaults to true for vars with no atoms and for
    /// vars whose same-direction atoms are all asserted, so that cascade-only
    /// bounds are stored per #8422), this predicate defaults to FALSE: a
    /// frozen variable's epsilon-tighter bound that crosses no threshold has
    /// no direct propagation value.
    fn bound_crosses_unassigned_atom(&self, var: u32, is_upper: bool, value: &Rational) -> bool {
        let Some(atoms) = self.atom_index.get(&var) else {
            return false;
        };
        for atom in atoms {
            if self.asserted.contains_key(&atom.term) {
                continue;
            }
            let crosses = if is_upper == atom.is_upper {
                // Same direction: bound implies atom polarity true.
                let cmp = value.cmp(&atom.bound_value);
                if atom.strict {
                    if is_upper {
                        cmp.is_lt()
                    } else {
                        cmp.is_gt()
                    }
                } else if is_upper {
                    cmp.is_le()
                } else {
                    cmp.is_ge()
                }
            } else {
                // Opposite direction: bound falsifies atom.
                let cmp = value.cmp(&atom.bound_value);
                if is_upper {
                    // Atom is lower: x > k false if ub <= k; x >= k false if ub < k.
                    if atom.strict {
                        cmp.is_le()
                    } else {
                        cmp.is_lt()
                    }
                } else {
                    // Atom is upper: x < k false if lb >= k; x <= k false if lb > k.
                    if atom.strict {
                        cmp.is_ge()
                    } else {
                        cmp.is_gt()
                    }
                }
            };
            if crosses {
                return true;
            }
        }
        false
    }

    /// Overlay a single variable's direct bounds into the implied_bounds slot.
    /// Extracted to avoid duplication between incremental and full-scan paths.
    /// True when either direct bound of `info` carries a `Rational::Big`
    /// value (#certora-bigint-fast). Feeds the sticky `big_bound_seen`
    /// heuristic that widens the f64 pre-screen to narrow rows.
    #[inline]
    fn var_has_big_direct_bound(info: &VarInfo) -> bool {
        info.lower
            .as_ref()
            .is_some_and(|b| matches!(b.value, Rational::Big(_)))
            || info
                .upper
                .as_ref()
                .is_some_and(|b| matches!(b.value, Rational::Big(_)))
    }

    fn overlay_direct_bound_for_var(
        info: &VarInfo,
        slot: &mut (Option<ImpliedBound>, Option<ImpliedBound>),
    ) {
        if let Some(b) = &info.lower {
            let direct_lb = ImpliedBound {
                value: b.value.clone(),
                strict: b.strict,
                row_idx: usize::MAX,
                explanation: None,
            };
            let replace = match &slot.0 {
                None => true,
                Some(existing) => {
                    direct_lb.value > existing.value
                        || (direct_lb.value == existing.value
                            && !existing.strict
                            && direct_lb.strict)
                }
            };
            if replace {
                slot.0 = Some(direct_lb);
            }
        }
        if let Some(b) = &info.upper {
            let direct_ub = ImpliedBound {
                value: b.value.clone(),
                strict: b.strict,
                row_idx: usize::MAX,
                explanation: None,
            };
            let replace = match &slot.1 {
                None => true,
                Some(existing) => {
                    direct_ub.value < existing.value
                        || (direct_ub.value == existing.value
                            && !existing.strict
                            && direct_ub.strict)
                }
            };
            if replace {
                slot.1 = Some(direct_ub);
            }
        }
    }
}
