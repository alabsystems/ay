// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// Global pivot budget for FULL simplex calls (check-time) across the entire
/// solve. When `full_check_pivots` exceeds this, subsequent full
/// `dual_simplex_with_max_iters` calls return Unknown immediately. This
/// prevents dense LP problems from spending all CPU time in simplex pivoting.
///
/// IMPORTANT: This budget only applies to full check-time simplex calls,
/// NOT to propagation-budget simplex calls (`dual_simplex_propagate`).
/// Propagation calls already have their own tight per-call budget
/// (max(200, 5*num_vars)) and return Sat on budget exhaustion. Counting
/// propagation pivots toward the global budget causes a death spiral on
/// combined-theory problems (UF+LIA, Seq+LIA) where the DPLL(T) loop
/// makes thousands of BCP theory checks: propagation calls exhaust the
/// global budget, then full check() can never run simplex, causing
/// Unknown on every theory check and making the solver spin without
/// progress. This was the root cause of the verification-consumer ghost_vec regression
/// (12s -> >120s timeout, #8404).
///
/// Value: 2M pivots. For reference, Z3 uses `max_number_of_iterations_with_no_improvements
/// = 2000000` (lp_settings.h:224) as a per-phase stall detector. AY's global budget
/// serves a similar purpose but across the entire solve.
///
/// At ~1us/pivot (typical for Rational64 fast path), 2M pivots ~ 2s of pure
/// simplex time, leaving headroom for the SAT solver within a 30s timeout.
const GLOBAL_PIVOT_BUDGET: u64 = 2_000_000;

/// Per-check() pivot budget. Limits the total number of simplex pivots consumed
/// within a single `check_impl()` or `check_during_propagate_impl()` invocation.
/// When exceeded, the simplex returns Unknown ("resource exhausted"), signaling
/// to the DPLL(T) layer that the theory solver cannot determine feasibility
/// within the budget. The SAT solver continues exploring other Boolean assignments.
///
/// This budget addresses dense LP problems (rand_*, vpm2-30, tsp_rand_*) where
/// the simplex runs unbounded pivots without converging. Z3 handles this via
/// `max_number_of_iterations_with_no_improvements` (lp_settings.h:224). AY uses
/// a hard per-check cap that is simpler and avoids tuning improvement detection.
///
/// Value: 10,000 pivots. For sparse SMT problems (the common case), simplex
/// typically converges in <100 pivots per check. Dense LP problems may need
/// 10K-100K pivots per call, so the budget forces early exit and lets the
/// DPLL(T) loop try different theory-variable assignments instead.
pub(crate) const CHECK_PIVOT_BUDGET: u32 = 10_000;

impl LraSolver {
    #[inline]
    pub(super) fn dual_simplex_iteration_budget(max_iters: usize, bland_mode: bool) -> usize {
        if bland_mode {
            max_iters.saturating_mul(10).min(10_000_000)
        } else {
            max_iters
        }
    }

    /// Run dual simplex to check feasibility of the current LP state.
    ///
    /// Public for LIA's tentative big-cut testing (Z3 gomory.cpp:496-503).
    pub fn dual_simplex(&mut self) -> TheoryResult {
        // Limit iterations to prevent infinite loops.
        // With Bland's rule, simplex terminates in O(2^n) worst case but typically polynomial.
        // Z3's `tableau_rows` strategy has effectively NO iteration limit — it relies on
        // Bland's rule mathematical termination guarantee. AY's Rational type uses an
        // inline i64/i64 fast path that avoids BigRational allocation in >95% of
        // operations, making per-iteration cost close to Z3's double arithmetic.
        // Scale 200 + cap 10M (#7852: was scale 20 + cap 1M, causing premature Unknown
        // on LP-family benchmarks like rand_70_300, vpm2-30, tsp_rand where Z3 solves
        // in 1-8s). For 300 rows + 370 vars: min(10000 + 670*200, 10M) = 144K iters.
        // UNSAT detection exits early regardless of cap; cap only matters for feasibility
        // search on large SAT instances.
        let base_iters = 10_000usize;
        let scale_iters = (self.rows.len() + self.vars.len()) * 200;
        let max_iters = std::cmp::min(base_iters + scale_iters, 10_000_000);

        // Float-pivot layer (--lra-float-layer, default OFF). A pure heuristic
        // f64 basis oracle proposes a candidate basis that we certify EXACTLY in
        // O(one basis solve); on any imprecision it returns None and we fall
        // through to the unchanged exact simplex below. Only reached on the
        // full-check path (never dual_simplex_propagate). Soundness is
        // structural — see simplex::float_layer.
        // SOUNDNESS (wrong-SAT fix): a pending trivial_conflict (a contradictory
        // bound found before the loop) is consumed ONLY by
        // dual_simplex_with_max_iters below. The float certified-SAT path must NOT
        // short-circuit past it, or a genuine UNSAT would be reported SAT. Skip the
        // float path when a trivial conflict is pending → fall through to the exact
        // loop, which returns the correct Unsat.
        if float_layer::float_layer_enabled() && self.trivial_conflict.is_none() {
            if let Some(result) = self.try_float_certified_sat() {
                return result;
            }
        }

        self.dual_simplex_with_max_iters(max_iters)
    }

    /// Run dual simplex with a tighter per-invocation budget for propagation-time
    /// checks (#8003 Gap 4). During BCP, a single theory check should not consume
    /// the entire timeout on degenerate problems. If the budget is exhausted, return
    /// `Sat` ("no conflict found") so the SAT solver can continue — the full check()
    /// call will run the unrestricted simplex later.
    ///
    /// Budget: `max(200, 5 * num_vars)` — enough for typical propagation but caps
    /// degenerate cases. Reduced from `max(1000, 10 * num_vars)` because profile
    /// data from sc-6 and simple_startup benchmarks shows BCP simplex calls
    /// dominate runtime: 7125 calls x 2000 iter budget = 14M iterations, while
    /// Z3 runs 0 simplex during propagation. A smaller budget catches shallow
    /// conflicts (which are most theory conflicts) while deferring deeper ones
    /// to the full check() call.
    pub fn dual_simplex_propagate(&mut self) -> TheoryResult {
        // #8003: Reduced BCP simplex budget for dense LP benchmarks. The
        // previous budget of max(200, 5 * num_vars) was 40K iterations for
        // an 8K-variable LP relaxation, causing each BCP callback to consume
        // up to 40ms. Z3's new solver doesn't run simplex during propagation
        // at all — it relies on the full check(). AY keeps a small budget to
        // catch shallow conflicts (contradictory bounds produce conflicts in
        // O(1) pivots via the pre-loop fast path), but defers deeper exploration
        // to the full check(). Budget: max(50, rows) — enough for the
        // pre-loop fast path + a few pivots, but caps at the number of tableau
        // rows which is the theoretical minimum for one full pass.
        let propagation_budget = std::cmp::max(50, self.rows.len());
        // Track pivots before the call so we can exclude propagation pivots
        // from the full-check global budget. Propagation calls have their own
        // tight per-call budget; counting them toward the global budget causes
        // budget exhaustion on combined-theory problems (#8404).
        let pivots_before = self.stats.total_pivots;
        let result = self.dual_simplex_with_max_iters(propagation_budget);
        let propagation_pivots = self.stats.total_pivots - pivots_before;
        // Undo the full_check_pivots increment from propagation pivots.
        // dual_simplex_with_max_iters increments both total_pivots and
        // full_check_pivots; we want propagation pivots in total_pivots
        // (for statistics) but NOT in full_check_pivots (for budget).
        self.stats.full_check_pivots = self
            .stats
            .full_check_pivots
            .saturating_sub(propagation_pivots);
        // Budget exhaustion during propagation is not a real Unknown — it just means
        // we didn't find a conflict within the budget. Return Sat so the SAT solver
        // continues; the final check() will run the full simplex.
        if matches!(result, TheoryResult::Unknown) {
            self.stats.propagation_budget_exhaustions += 1;
            debug!(
                target: "ay::lra",
                budget = propagation_budget,
                exhaustions = self.stats.propagation_budget_exhaustions,
                "LRA propagation simplex budget exhausted, deferring to full check"
            );
            TheoryResult::Sat
        } else {
            result
        }
    }

    pub(crate) fn dual_simplex_with_max_iters(&mut self, max_iters: usize) -> TheoryResult {
        // #inc-guard-memo: conservatively assume unverified until the one exit
        // that fully re-verifies every bound sets this true (see lib.rs).
        self.last_simplex_verified = false;
        // Global pivot budget check: if the solver has already consumed its
        // full-check pivot budget, return Unknown immediately. This prevents
        // dense LP problems from burning the entire timeout in simplex pivoting.
        // The SAT solver can still try different Boolean assignments; only the
        // arithmetic feasibility check is curtailed.
        //
        // Note: uses `full_check_pivots` (not `total_pivots`) because propagation
        // calls have their own per-call budget and are excluded from the global
        // budget. See `dual_simplex_propagate()` and #8404.
        if self.stats.full_check_pivots >= GLOBAL_PIVOT_BUDGET {
            self.stats.global_budget_exhaustions += 1;
            info!(
                target: "ay::lra",
                full_check_pivots = self.stats.full_check_pivots,
                total_pivots = self.stats.total_pivots,
                budget = GLOBAL_PIVOT_BUDGET,
                exhaustions = self.stats.global_budget_exhaustions,
                "LRA global pivot budget exhausted, returning Unknown"
            );
            return TheoryResult::Unknown;
        }

        let mut iterations_run = 0usize;
        let mut pivot_count = 0usize;
        let mut nonbasic_repair_rounds = 0usize;
        let mut leaving_fixups = 0usize;
        let summarize = |outcome: &'static str,
                         reason: &'static str,
                         iterations: usize,
                         pivots: usize,
                         repairs: usize,
                         fixups: usize,
                         rows: usize,
                         vars: usize| {
            info!(
                target: "ay::lra",
                outcome,
                reason,
                iterations,
                pivots,
                nonbasic_repair_rounds = repairs,
                leaving_fixups = fixups,
                rows,
                vars,
                max_iters,
                "LRA dual simplex summary"
            );
        };

        #[cfg(debug_assertions)]
        self.debug_assert_tableau_consistency("dual_simplex:start");

        // Check for trivial conflicts from constant constraints (e.g., `0 < 0` or `-1 >= 0`)
        if let Some(lits) = self.trivial_conflict.take() {
            summarize(
                "unsat",
                "trivial_conflict",
                iterations_run,
                pivot_count,
                nonbasic_repair_rounds,
                leaving_fixups,
                self.rows.len(),
                self.vars.len(),
            );
            return TheoryResult::Unsat(lits);
        }

        // Quick UNSAT check: contradictory bounds on a variable are immediately infeasible.
        //
        // This is important for problems that are purely a conjunction of bounds (no tableau
        // rows). The main dual-simplex loop focuses on pivoting basic variables, so we need an
        // explicit contradiction check for non-basic-only constraints.
        //
        // #8064: For small-budget BCP calls (max_iters <= 100), use a targeted scan
        // over only the variables whose bounds were tightened since the last simplex
        // run. This reduces the per-call cost from O(vars) to O(changed). For full
        // simplex (large budget), always scan all vars for correctness.
        let num_vars = self.vars.len();
        let tightened_count = self.vars_tightened_since_simplex.len();
        let mut tightened_buf = [0u32; 64];
        let use_targeted = max_iters <= 100 && tightened_count > 0 && tightened_count <= 64;
        if use_targeted {
            tightened_buf[..tightened_count]
                .copy_from_slice(&self.vars_tightened_since_simplex[..tightened_count]);
        }
        let scan_count = if use_targeted {
            tightened_count
        } else {
            num_vars
        };
        // #9061 / soundness: in FULL-scan mode (`use_targeted == false`) we MUST
        // visit every variable index `0..num_vars`. Iterating
        // `tightened_buf.iter().enumerate().take(scan_count)` silently capped the
        // full scan at the buffer length (64), so a contradictory bound on any
        // variable with index >= 64 (e.g. `lower=639 > upper=0` both asserted, or
        // `0 <= x` and `x < 0` on slack var 117) was never detected → false SAT
        // on QF_LRA, and a spurious Unknown on reified Bool-over-LIA gate problems
        // (kind2 microwave03/SYNAPSE/ticket3i, AUFLIA arrays) where, with no row
        // to pivot it (rows==0), the main loop oscillated the variable between its
        // two incompatible bounds until `max_iters`. These instances routinely
        // have hundreds of variables. Fix: iterate `0..scan_count` directly so the
        // loop index itself is the variable id in the full path; the targeted path
        // stays bounded by `scan_count <= 64`, so indexing `tightened_buf[scan_idx]`
        // is in range.
        //
        // `needless_range_loop` is suppressed deliberately: iterating
        // `tightened_buf` directly is precisely the defect being fixed — in the
        // full path `scan_count == num_vars` can exceed the 64-element buffer,
        // and the loop index itself (not a buffer element) is the variable id.
        #[allow(clippy::needless_range_loop)]
        for scan_idx in 0..scan_count {
            let var = if use_targeted {
                tightened_buf[scan_idx] as usize
            } else {
                scan_idx
            };
            let info = &self.vars[var];
            let (Some(lower), Some(upper)) = (&info.lower, &info.upper) else {
                continue;
            };

            let contradicts = lower.value > upper.value
                || (lower.value == upper.value && (lower.strict || upper.strict));
            if contradicts {
                if ay_core::sat_debug_env_flags().dump_conflicts {
                    safe_eprintln!(
                        "[CONFLICT] var={} lower={}{} upper={}{} lower_reasons={:?} upper_reasons={:?}",
                        var,
                        if lower.strict { ">" } else { ">=" },
                        lower.value,
                        if upper.strict { "<" } else { "<=" },
                        upper.value,
                        lower.reasons.iter().zip(&lower.reason_values)
                            .filter(|(r, _)| !r.is_sentinel())
                            .map(|(r, v)| format!("({r:?},{v})"))
                            .collect::<Vec<_>>(),
                        upper.reasons.iter().zip(&upper.reason_values)
                            .filter(|(r, _)| !r.is_sentinel())
                            .map(|(r, v)| format!("({r:?},{v})"))
                            .collect::<Vec<_>>(),
                    );
                }
                if debug_lra() {
                    self.debug_log_contradictory_bounds(var as u32, lower, upper);
                }
                use num_rational::Rational64;
                let mut literals = Vec::new();
                let mut coefficients = Vec::new();
                let mut all_fit = true;
                // Track whether each bound contributed real (non-sentinel) reasons.
                // Reasonless bounds must still degrade to Unknown, but sentinel-only
                // axioms can be omitted from a partial conflict just like the row-
                // based conflict builders do (#6679, #4919).
                let mut lower_has_real = false;
                let mut upper_has_real = false;
                for ((reason, reason_value), scale) in
                    lower.reasons.iter().zip(&lower.reason_values).zip(
                        lower
                            .reason_scales
                            .iter()
                            .chain(std::iter::repeat(crate::types::rational_one())),
                    )
                {
                    if !reason.is_sentinel() {
                        lower_has_real = true;
                        literals.push(TheoryLit::new(*reason, *reason_value));
                        match Self::rational_to_rational64(scale) {
                            Some(c) => coefficients.push(c),
                            None => {
                                all_fit = false;
                                coefficients.push(Rational64::from(1));
                            }
                        }
                    }
                }
                for ((reason, reason_value), scale) in
                    upper.reasons.iter().zip(&upper.reason_values).zip(
                        upper
                            .reason_scales
                            .iter()
                            .chain(std::iter::repeat(crate::types::rational_one())),
                    )
                {
                    if !reason.is_sentinel() {
                        upper_has_real = true;
                        literals.push(TheoryLit::new(*reason, *reason_value));
                        match Self::rational_to_rational64(scale) {
                            Some(c) => coefficients.push(c),
                            None => {
                                all_fit = false;
                                coefficients.push(Rational64::from(1));
                            }
                        }
                    }
                }
                let lower_is_reasonless = lower.reasons.is_empty();
                let upper_is_reasonless = upper.reasons.is_empty();
                if lower_is_reasonless || upper_is_reasonless {
                    // #8151: Provenance fallback — try to recover reasons from
                    // BoundProvenance chains before degrading to Unknown.
                    let mut provenance_recovered = false;
                    if lower_is_reasonless {
                        if let Some(prov_lits) = Self::collect_reasons_from_provenance(lower) {
                            literals.extend(prov_lits);
                            lower_has_real = true;
                            provenance_recovered = true;
                        }
                    }
                    if upper_is_reasonless {
                        if let Some(prov_lits) = Self::collect_reasons_from_provenance(upper) {
                            literals.extend(prov_lits);
                            upper_has_real = true;
                            provenance_recovered = true;
                        }
                    }
                    if !provenance_recovered
                        || (!lower_has_real && lower_is_reasonless)
                        || (!upper_has_real && upper_is_reasonless)
                    {
                        summarize(
                            "unknown",
                            "bound_conflict_without_literals",
                            iterations_run,
                            pivot_count,
                            nonbasic_repair_rounds,
                            leaving_fixups,
                            self.rows.len(),
                            self.vars.len(),
                        );
                        return TheoryResult::Unknown;
                    }
                    // Provenance recovered — continue with deduplication below.
                    // Drop Farkas metadata since provenance reasons are not
                    // paired with per-literal coefficients.
                    all_fit = false;
                }
                let has_sentinel_only_bound = !lower_has_real || !upper_has_real;
                if has_sentinel_only_bound {
                    if literals.is_empty() {
                        summarize(
                            "unknown",
                            "bound_conflict_without_literals",
                            iterations_run,
                            pivot_count,
                            nonbasic_repair_rounds,
                            leaving_fixups,
                            self.rows.len(),
                            self.vars.len(),
                        );
                        return TheoryResult::Unknown;
                    }
                    let (dedup_lits, _) = Self::deduplicate_conflict(literals, None);
                    // After contradictory-literal removal, the conflict may be
                    // empty. This happens when the only reason atoms appear with
                    // both polarities (e.g., cross-negation bound propagation
                    // tracking). Skip this variable and continue scanning for a
                    // non-degenerate conflict. (#4666)
                    if dedup_lits.is_empty() {
                        continue;
                    }
                    // #8784: Stale-reason guard. If any reason is no longer
                    // asserted, skip this variable and continue scanning —
                    // other variables may yield a live contradiction. An
                    // unconditional `return Unknown` here over-rejects valid
                    // `sat` instances where bounds derived from shared
                    // equalities / cross-sort propagations have reasons that
                    // are not direct SAT-layer assertions (seq_dense_ghost_vec
                    // repro under QF_UFLIA). The `continue` preserves the
                    // soundness intent of #8764 (never emit a stale conflict)
                    // without prematurely globally abandoning the check.
                    if !self.conflict_literals_all_asserted(&dedup_lits) {
                        self.stats.stale_conflict_rejected_count += 1;
                        continue;
                    }
                    summarize(
                        "unsat",
                        "contradictory_variable_bounds_partial",
                        iterations_run,
                        pivot_count,
                        nonbasic_repair_rounds,
                        leaving_fixups,
                        self.rows.len(),
                        self.vars.len(),
                    );
                    return TheoryResult::UnsatWithFarkas(TheoryConflict::new(dedup_lits));
                }
                let farkas_opt = if all_fit {
                    Some(FarkasAnnotation::new(coefficients))
                } else {
                    None
                };
                let (dedup_lits, dedup_coeffs) =
                    Self::deduplicate_conflict(literals, farkas_opt.as_ref());
                let farkas = if !dedup_coeffs.is_empty() {
                    Some(FarkasAnnotation::new(dedup_coeffs))
                } else if all_fit {
                    Some(FarkasAnnotation::new(
                        (0..dedup_lits.len()).map(|_| Rational64::from(1)).collect(),
                    ))
                } else {
                    None
                };
                // After contradictory-literal removal, the conflict may be
                // empty. Skip this variable and continue scanning. (#4666)
                if dedup_lits.is_empty() {
                    continue;
                }
                // #8784: Stale-reason guard. See comment above on the
                // sentinel-only branch. Use `continue` rather than
                // `return Unknown` so the outer scan keeps searching for a
                // live contradiction on another variable before giving up.
                if !self.conflict_literals_all_asserted(&dedup_lits) {
                    self.stats.stale_conflict_rejected_count += 1;
                    continue;
                }
                summarize(
                    "unsat",
                    "contradictory_variable_bounds",
                    iterations_run,
                    pivot_count,
                    nonbasic_repair_rounds,
                    leaving_fixups,
                    self.rows.len(),
                    self.vars.len(),
                );
                return TheoryResult::UnsatWithFarkas(match farkas {
                    Some(f) => TheoryConflict::with_farkas(dedup_lits, f),
                    None => TheoryConflict::new(dedup_lits),
                });
            }
        }

        // Row-level infeasibility precheck for strict bounds (#2021).
        //
        // For each row basic_var = Σ(coeff_i * nb_var_i) + constant, compute the implied
        // bounds on basic_var from the non-basic variables' bounds. If the implied lower
        // bound (considering strictness) exceeds the upper bound, or vice versa, it's UNSAT.
        //
        // This catches infeasibility without running simplex iterations (e.g., x > 0,
        // y > 0, x + y <= 0). Even with InfRational eliminating cycling, this precheck
        // provides faster UNSAT detection by examining row structure directly.
        //
        // #8256: Skip this O(rows * width) precheck during BCP calls on large tableaux.
        // For 878 rows, each call does ~878 * ~5 rational multiplications = ~4K ops.
        // During BCP, the contradictory variable bounds check (above) already catches
        // the most common conflicts (direct bound contradictions), and the simplex
        // main loop catches row-level conflicts via pivoting. The precheck is deferred
        // to the full check() where the O(rows) cost is amortized over fewer calls.
        // Threshold: max_iters <= rows identifies BCP calls (propagation budget).
        let skip_row_precheck = max_iters <= self.rows.len() && self.rows.len() >= 200;
        if !skip_row_precheck {
            if let Some(conflict) = self.check_row_strict_infeasibility() {
                summarize(
                    "unsat",
                    "row_strict_infeasibility_precheck",
                    iterations_run,
                    pivot_count,
                    nonbasic_repair_rounds,
                    leaving_fixups,
                    self.rows.len(),
                    self.vars.len(),
                );
                return conflict;
            }
        }

        let debug = debug_lra();
        if debug {
            safe_eprintln!(
                "[LRA] dual_simplex: {} rows, {} vars, max_iters={}",
                self.rows.len(),
                self.vars.len(),
                max_iters
            );
        }

        let mut last_print = 0usize;
        // Cycling detection: track basis signatures (hash of basic variable set).
        // With InfRational (#4919 RC0), degenerate cycling from strict bounds
        // is eliminated. The basis hash check serves as a safety net for any
        // remaining degenerate cases (e.g., equal non-strict bounds creating
        // zero-step pivots). When repeated bases are detected, Bland mode
        // activates to guarantee termination (#2718, #4919 Phase 2).

        // Reset Bland mode at the start of each simplex invocation (#4919 Phase 2).
        // Bland mode is activated during the run if basis repeats are detected.
        self.bland_mode = false;
        self.basis_repeat_count = 0;

        // Compute initial basis hash from all basic variables (#6221 Finding 1).
        // Use incremental XOR hashing: O(1) per pivot instead of O(rows).
        // mix_u32 provides avalanche mixing to avoid trivial XOR collisions.
        let mut basis_hash: u64 = 0;
        for row in &self.rows {
            basis_hash ^= Self::mix_u32(row.basic_var);
        }
        let mut prev_basis_hash: u64 = basis_hash;

        // Build infeasible heap before the main loop (#4919 Phase B, #8782).
        // When heap_stale is false, incremental track_var_feasibility() calls
        // during bound assertion have kept the heap current — skip the O(rows)
        // full rebuild.
        if self.heap_stale {
            self.rebuild_infeasible_heap();
        }

        // #8009: Pre-loop fast path. When the infeasible heap is empty (all basic
        // vars feasible) and we have a tightened-vars list, scan only those vars
        // for non-basic violations instead of the O(vars) full scan. On large LP
        // benchmarks (vpm2-30: 793 vars), 96% of simplex calls return SAT at
        // iteration 0 — this converts each from O(vars) to O(tightened_count).
        //
        // Reference: Z3 `lar_core_solver_def.h:85-94` — Z3 tracks ALL columns
        // (basic + non-basic) in inf_heap, enabling O(1) `current_x_is_feasible()`.
        // AY only tracks basic vars in the heap, so we use the tightened-vars list
        // as a targeted proxy for the non-basic check.
        //
        // #warm-simplex: when the persistent non-basic candidate set has
        // pending entries (e.g. from a value-restore or a self-marked snap),
        // the tightened-vars list alone does not cover them — skip this fast
        // path and let the main loop's targeted dirty-set exit handle them.
        // Flag OFF: `!self.warm.enabled` short-circuits to today's condition.
        if !self.heap_stale
            && self.infeasible_heap.is_empty()
            && !self.vars_tightened_since_simplex.is_empty()
            && (!self.warm.enabled || self.warm.nonbasic_dirty.is_empty())
        {
            // Copy to local buffer to release borrow on self before update_nonbasic.
            // Use std::mem::take to avoid heap allocation: swap with empty vec.
            let tightened = std::mem::take(&mut self.vars_tightened_since_simplex);
            // Targeted non-basic scan: only check vars whose bounds were
            // tightened since last simplex.
            let mut saw_violation = false;
            let mut did_fix = false;
            for &var in tightened.iter() {
                let vi = var as usize;
                if vi >= self.vars.len() {
                    continue;
                }
                if !matches!(self.vars[vi].status, Some(VarStatus::NonBasic)) {
                    // Basic var violations are tracked by heap — already empty.
                    continue;
                }
                if let Some(violated_type) = self.violates_bounds(var) {
                    saw_violation = true;
                    let info = &self.vars[var as usize];
                    if let Some(nv) = Self::choose_nonbasic_fix_value(info, violated_type) {
                        self.update_nonbasic(var, nv);
                        did_fix = true;
                    }
                }
            }
            // Restore the (now-consumed) vec for capacity reuse.
            self.vars_tightened_since_simplex = tightened;
            self.vars_tightened_since_simplex.clear();
            if !saw_violation && !did_fix {
                // No basic or non-basic violations — SAT without entering loop.
                summarize(
                    "sat",
                    "pre_loop_fast_path",
                    0,
                    0,
                    0,
                    0,
                    self.rows.len(),
                    self.vars.len(),
                );
                // #inc-guard-chain: this exit verified only the heap (basic)
                // and the TIGHTENED vars (targeted non-basic scan). That
                // extends the previous full verification iff every mutation
                // since it was tracked — exactly `guard_tracked_only`. Under
                // a broken chain this Sat stays unverified and the guard
                // rescans as before.
                self.last_simplex_verified = self.guard_tracked_only;
                return TheoryResult::Sat;
            }
            // If we fixed non-basic vars, their update_nonbasic calls may have
            // pushed basic vars into violation (tracked by heap). Fall through
            // to main loop to handle those.
        }
        // When vars_tightened_since_simplex is empty, fall through to the
        // main loop which does a full non-basic scan on its first iteration.
        // Previously this path returned Sat immediately ("pre_loop_no_tightened"),
        // but that was unsound: lifecycle operations (pop/reset/soft_reset) and
        // refresh_simplex_for_propagate() clear vars_tightened_since_simplex
        // while bounds may still be violated (variable values are not restored
        // by pop, creating value/bound mismatches invisible to the targeted scan).

        let bland_gated_cap = Self::dual_simplex_iteration_budget(max_iters, true);
        for iter in 0..bland_gated_cap {
            // #7852: keep the smaller budget while searching normally, but
            // once repeated bases trigger Bland mode allow up to 10x more
            // pivots (capped at 10M) so LP-family cases can finish.
            let cap = Self::dual_simplex_iteration_budget(max_iters, self.bland_mode);
            if iter >= cap {
                break;
            }
            iterations_run = iter + 1;
            trace!(
                target: "ay::lra",
                iter,
                rows = self.rows.len(),
                vars = self.vars.len(),
                "LRA dual simplex iteration start"
            );
            if debug && (iter < 20 || iter - last_print >= 10000) {
                last_print = iter;
                safe_eprintln!(
                    "[LRA] iter {} - {} rows, {} vars",
                    iter,
                    self.rows.len(),
                    self.vars.len()
                );
            }
            // Extract infeasible basic variable with greatest bound violation (#4919).
            // Greatest-error pivot reduces total pivots by attacking largest violations first.
            let violated_row = self.pop_greatest_error();

            let Some((row_idx, violated_bound)) = violated_row else {
                if debug && iter < 20 {
                    safe_eprintln!("[LRA] iter {} - no violated row, checking non-basic", iter);
                }
                // All basic variables satisfy bounds - check non-basic too.
                // Iterate in-place to avoid Vec<u32> allocation per SAT check.
                let mut saw_violation = false;
                let mut did_fix = false;
                // #9061: a non-basic variable that STILL violates a bound right
                // after being moved to its other bound has an empty feasible
                // interval (lower and upper are mutually contradictory) and no
                // pivot can repair it. Record it so we can break the oscillation
                // instead of flipping the variable between its two bounds until
                // `max_iters` (a spurious Unknown).
                let mut stuck_var: Option<u32> = None;
                // #warm-simplex: when the persistent candidate set's coverage
                // invariant holds, only the enqueued non-basic vars can be
                // violated — scan O(dirty) instead of O(vars). The full scan
                // below remains the fallback and is what re-arms the
                // invariant on a clean pass.
                let warm_targeted = self.warm.enabled && self.warm.nonbasic_valid;
                if warm_targeted {
                    // Process only the entries present at round start; a snap
                    // that leaves its target violated re-enqueues it (via
                    // update_nonbasic) past `n0`, and the `continue` below
                    // re-enters this branch for the appended tail — with the
                    // same-round stuck detection breaking #9061 oscillations.
                    let n0 = self.warm.nonbasic_dirty.len();
                    for k in 0..n0 {
                        let var = self.warm.nonbasic_dirty[k];
                        let vi = var as usize;
                        if vi < self.warm.nonbasic_stamp.len() {
                            self.warm.nonbasic_stamp[vi] = 0;
                        }
                        if vi >= self.vars.len() {
                            continue;
                        }
                        if !matches!(self.vars[vi].status, Some(VarStatus::NonBasic)) {
                            continue;
                        }
                        if let Some(violated_type) = self.violates_bounds(var) {
                            saw_violation = true;
                            let info = &self.vars[vi];
                            if let Some(nv) = Self::choose_nonbasic_fix_value(info, violated_type) {
                                self.update_nonbasic(var, nv);
                                did_fix = true;
                                if stuck_var.is_none() && self.violates_bounds(var).is_some() {
                                    stuck_var = Some(var);
                                }
                            }
                        }
                    }
                    self.warm.nonbasic_dirty.drain(..n0);
                } else {
                    for i in 0..self.vars.len() {
                        if !matches!(self.vars[i].status, Some(VarStatus::NonBasic)) {
                            continue;
                        }
                        let var = i as u32;
                        if let Some(violated_type) = self.violates_bounds(var) {
                            saw_violation = true;
                            let info = &self.vars[var as usize];
                            if let Some(nv) = Self::choose_nonbasic_fix_value(info, violated_type) {
                                self.update_nonbasic(var, nv);
                                did_fix = true;
                                if stuck_var.is_none() && self.violates_bounds(var).is_some() {
                                    stuck_var = Some(var);
                                }
                            }
                        }
                    }
                }

                // #9061: Break the repair oscillation on a contradictory non-basic
                // variable. The full early contradiction scan already returns
                // UNSAT when such a variable's bounds are justified, so reaching
                // here means at least one offending bound is unjustified (its
                // reason atoms are no longer asserted). Retract those bounds to
                // relax the LP and keep solving (A2-consistent: relaxation is
                // sound; later UNSAT verdicts rest on the remaining justified
                // bounds and Sat models are re-validated downstream). If nothing
                // can be retracted, stop with Unknown rather than spinning.
                if let Some(var) = stuck_var {
                    if self.retract_unjustified_var_bounds(var) > 0 {
                        // #warm-simplex: the retraction may leave the var
                        // still violated on the remaining (justified) side —
                        // keep it in the candidate set so the next targeted
                        // round re-validates it.
                        if self.warm.enabled {
                            self.warm_mark_nonbasic_dirty(var);
                        }
                        nonbasic_repair_rounds += 1;
                        continue;
                    }
                    summarize(
                        "unknown",
                        "nonbasic_repair_stuck",
                        iterations_run,
                        pivot_count,
                        nonbasic_repair_rounds,
                        leaving_fixups,
                        self.rows.len(),
                        self.vars.len(),
                    );
                    return TheoryResult::Unknown;
                }

                // If we changed any non-basic assignments (or observed a strict-at-bound
                // violation we didn't resolve here), re-enter the main loop so we can
                // pivot on any newly violated basic variables.
                if did_fix || saw_violation {
                    nonbasic_repair_rounds += 1;
                    debug!(
                        target: "ay::lra",
                        iter,
                        saw_violation,
                        did_fix,
                        "LRA non-basic repair round before continuing"
                    );
                    if debug && iter < 20 {
                        safe_eprintln!("[LRA] iter {} - fixed non-basic, continuing", iter);
                    }
                    continue;
                }

                if debug {
                    safe_eprintln!("[LRA] Returning Sat at iter {}", iter);
                    for (i, info) in self.vars.iter().enumerate() {
                        let status = match &info.status {
                            Some(VarStatus::Basic(r)) => format!("B(row{r})"),
                            Some(VarStatus::NonBasic) => "NB".to_string(),
                            None => "?".to_string(),
                        };
                        safe_eprintln!("[LRA]   var {} = {} ({})", i, info.value, status);
                    }
                }
                if warm_targeted {
                    // #warm-simplex targeted exit: heap empty (all basic vars
                    // feasible — the heap invariant is maintained at every
                    // value write and repaired across pops) + candidate set
                    // drained clean. This verified only the TRACKED non-basic
                    // vars, so it may claim a verified Sat only under the
                    // #inc-guard-chain (same rule as the pre-loop fast path);
                    // final Sat verdicts are additionally re-validated by the
                    // unconditional guard scan in check_impl.
                    summarize(
                        "sat",
                        "warm_targeted_nonbasic",
                        iterations_run,
                        pivot_count,
                        nonbasic_repair_rounds,
                        leaving_fixups,
                        self.rows.len(),
                        self.vars.len(),
                    );
                    self.last_simplex_verified = self.guard_tracked_only;
                    return TheoryResult::Sat;
                }
                summarize(
                    "sat",
                    "all_bounds_satisfied",
                    iterations_run,
                    pivot_count,
                    nonbasic_repair_rounds,
                    leaving_fixups,
                    self.rows.len(),
                    self.vars.len(),
                );
                // #inc-guard-memo: this exit verified EVERY bound (heap empty
                // for basic vars + full non-basic `violates_bounds` scan) —
                // a full verification, so it also restores the tracked-only
                // chain (#inc-guard-chain).
                self.last_simplex_verified = true;
                self.guard_tracked_only = true;
                // #warm-simplex: a clean FULL non-basic scan re-arms the
                // candidate-set coverage invariant (and empties the set).
                if self.warm.enabled {
                    self.warm_clear_nonbasic_dirty();
                    self.warm.nonbasic_valid = true;
                }
                return TheoryResult::Sat;
            };

            if debug && iter < 20 {
                let row = &self.rows[row_idx];
                let basic_var = row.basic_var;
                let basic_info = &self.vars[basic_var as usize];
                let lb = basic_info
                    .lower
                    .as_ref()
                    .map(|b| format!("{}({})", b.value, if b.strict { "<" } else { "<=" }))
                    .unwrap_or_default();
                let ub = basic_info
                    .upper
                    .as_ref()
                    .map(|b| format!("{}({})", b.value, if b.strict { ">" } else { ">=" }))
                    .unwrap_or_default();
                safe_eprintln!("[LRA] iter {} - violated row {}, basic_var={}, val={}, lb={}, ub={}, bound {:?}",
                    iter, row_idx, basic_var, basic_info.value, lb, ub, violated_bound);
            }

            // Find a suitable pivot candidate using cost-benefit heuristic (#4919 Phase 2).
            // Prefers entering variables with smaller column size (cheaper pivot).
            // Falls back to Bland's rule after BLAND_THRESHOLD repeated bases to
            // guarantee termination on degenerate LPs (#2718).
            let chosen: Option<(u32, InfRational)> =
                if let Some((entering_var, _direction, coeff_pos)) =
                    self.find_beneficial_entering(row_idx, violated_bound)
                {
                    // #8003 TL87: Use cached coefficient position from find_beneficial_entering
                    // to avoid redundant O(log w) binary search in compute_update_amount.
                    let coeff_ref = &self.rows[row_idx].coeffs[coeff_pos].1;
                    debug_assert_eq!(
                        self.rows[row_idx].coeffs[coeff_pos].0, entering_var,
                        "BUG: coeff_pos mismatch in find_beneficial_entering"
                    );
                    let new_val = self.compute_update_amount_with_coeff(
                        row_idx,
                        entering_var,
                        violated_bound,
                        coeff_ref,
                    );
                    Some((entering_var, new_val))
                } else {
                    None
                };

            let Some((entering_var, new_val)) = chosen else {
                // #warm-simplex: `pop_greatest_error` removed this basic var's
                // heap membership on extraction. On the pivot path the
                // subsequent `update_nonbasic`/`track_var_feasibility` calls
                // re-establish it, but on this no-pivot path we return (or
                // retract-and-continue) without a pivot — re-track it so the
                // still-violated var stays in the persistent candidate heap
                // across the conflict/pop cycle (heap coverage invariant).
                if self.warm.enabled {
                    let bv = self.rows[row_idx].basic_var;
                    self.track_var_feasibility(bv);
                }
                let conflict = self.build_conflict_with_farkas(row_idx);
                if conflict.literals.is_empty() {
                    // #A2: an empty conflict here means the explanation
                    // referenced bounds whose reason atoms are not currently
                    // asserted (e.g. NIA model-patch cuts justified by the
                    // monomial term itself, or bounds orphaned by a pop).
                    // Returning Unknown re-creates the identical infeasible
                    // tableau on the next theory check and livelocks the
                    // outer DPLL(T)/PDR loop. Retract the unjustified bounds
                    // (sound: only relaxes the LP; see
                    // retract_unjustified_row_bounds) and keep solving.
                    if self.retract_unjustified_row_bounds(row_idx) > 0 {
                        debug!(
                            target: "ay::lra",
                            iter,
                            row_idx,
                            "retracted unjustified bounds after empty conflict; continuing simplex"
                        );
                        continue;
                    }
                    summarize(
                        "unknown",
                        "conflict_without_literals",
                        iterations_run,
                        pivot_count,
                        nonbasic_repair_rounds,
                        leaving_fixups,
                        self.rows.len(),
                        self.vars.len(),
                    );
                    return TheoryResult::Unknown;
                }
                summarize(
                    "unsat",
                    "no_pivot_candidate_conflict",
                    iterations_run,
                    pivot_count,
                    nonbasic_repair_rounds,
                    leaving_fixups,
                    self.rows.len(),
                    self.vars.len(),
                );
                // Soundness check: conflict clause must be non-empty when
                // returning UNSAT (empty conflicts degrade to Unknown above).
                debug_assert!(
                    !conflict.literals.is_empty(),
                    "BUG: simplex returning UnsatWithFarkas with empty conflict clause"
                );
                return TheoryResult::UnsatWithFarkas(conflict);
            };

            debug!(
                target: "ay::lra",
                iter,
                row_idx,
                entering_var,
                new_value = %new_val,
                "LRA pivot candidate selected"
            );

            if debug && iter < 20 {
                let nb_info = &self.vars[entering_var as usize];
                let nb_lb = nb_info
                    .lower
                    .as_ref()
                    .map(|b| format!("{}({})", b.value, if b.strict { "<" } else { "<=" }))
                    .unwrap_or_default();
                let nb_ub = nb_info
                    .upper
                    .as_ref()
                    .map(|b| format!("{}({})", b.value, if b.strict { ">" } else { ">=" }))
                    .unwrap_or_default();
                safe_eprintln!(
                    "[LRA] iter {} - pivot: entering_var={}, old_val={}, new_val={}, lb={}, ub={}",
                    iter,
                    entering_var,
                    nb_info.value,
                    new_val,
                    nb_lb,
                    nb_ub
                );
            }

            // Capture leaving variable before pivot
            let leaving_var = self.rows[row_idx].basic_var;

            // Update the non-basic variable
            self.update_nonbasic(entering_var, new_val);

            if debug && iter < 20 {
                let row = &self.rows[row_idx];
                let basic_info = &self.vars[row.basic_var as usize];
                safe_eprintln!(
                    "[LRA] iter {} - after update: basic_var={} val={}",
                    iter,
                    row.basic_var,
                    basic_info.value
                );
            }

            // Pivot to swap basic/non-basic
            self.pivot(row_idx, entering_var);
            pivot_count += 1;
            self.stats.total_pivots += 1;
            self.stats.full_check_pivots += 1;
            self.stats.check_pivot_count = self.stats.check_pivot_count.saturating_add(1);

            // Per-check pivot budget: if the current check() has consumed too
            // many pivots, bail out early with Unknown. This prevents a single
            // check() call on a dense LP from burning unbounded CPU time (#8003).
            if self.stats.check_pivot_count >= self.check_pivot_budget() {
                self.stats.check_pivot_budget_exhaustions += 1;
                summarize(
                    "unknown",
                    "check_pivot_budget_exhausted",
                    iterations_run,
                    pivot_count,
                    nonbasic_repair_rounds,
                    leaving_fixups,
                    self.rows.len(),
                    self.vars.len(),
                );
                return TheoryResult::Unknown;
            }

            // After pivot: entering_var is now basic, leaving_var is now non-basic.
            // Update heap membership for both (#4919 Phase B).
            self.track_var_feasibility(entering_var);
            self.track_var_feasibility(leaving_var);

            // Track basis hash for cycling detection → Bland mode activation (#4919 Phase 2).
            // Incremental O(1) update (#6221 Finding 1): XOR out leaving, XOR in entering.
            if !self.bland_mode {
                basis_hash ^= Self::mix_u32(leaving_var) ^ Self::mix_u32(entering_var);
                if basis_hash == prev_basis_hash {
                    self.basis_repeat_count += 1;
                    if self.basis_repeat_count >= BLAND_THRESHOLD {
                        self.bland_mode = true;
                        // Rebuild heap with smallest-index keys for anti-cycling
                        self.rebuild_infeasible_heap();
                        debug!(
                            target: "ay::lra",
                            iter,
                            repeat_count = self.basis_repeat_count,
                            "LRA activating Bland's rule after repeated bases"
                        );
                    }
                } else {
                    self.basis_repeat_count = 0;
                    prev_basis_hash = basis_hash;
                }
            }

            // After pivot, the leaving variable is now non-basic. Ensure it
            // sits at its nearest feasible bound. The update_nonbasic + pivot
            // sequence can leave it at an intermediate value when the entering
            // variable was clamped to its own bounds. Non-basic variables must
            // be at bounds for the simplex invariant (and Bland's rule
            // termination guarantee) to hold (#2718).
            {
                let violated = self.violates_bounds(leaving_var);
                if let Some(violated_type) = violated {
                    let info = &self.vars[leaving_var as usize];
                    if let Some(fix_val) = Self::choose_nonbasic_fix_value(info, violated_type) {
                        self.update_nonbasic(leaving_var, fix_val);
                        leaving_fixups += 1;
                    }
                }
            }

            #[cfg(debug_assertions)]
            self.debug_assert_tableau_consistency("dual_simplex:post_pivot");

            // Periodically re-check strict bound infeasibility (#2665).
            // After pivots transform the tableau, strict bound contradictions
            // may become detectable that weren't visible before the loop.
            // This is a fast UNSAT shortcut — detects row-level contradictions
            // involving strict bounds without waiting for the simplex to exhaust
            // all pivot candidates.
            if (iter + 1) % 64 == 0 {
                if let Some(conflict) = self.check_row_strict_infeasibility() {
                    summarize(
                        "unsat",
                        "row_strict_infeasibility_iterative",
                        iterations_run,
                        pivot_count,
                        nonbasic_repair_rounds,
                        leaving_fixups,
                        self.rows.len(),
                        self.vars.len(),
                    );
                    return conflict;
                }
            }
        }

        // Too many iterations - return unknown
        self.stats.simplex_budget_exhaustions += 1;
        summarize(
            "unknown",
            "max_iterations_reached",
            iterations_run,
            pivot_count,
            nonbasic_repair_rounds,
            leaving_fixups,
            self.rows.len(),
            self.vars.len(),
        );
        TheoryResult::Unknown
    }
}

impl LraSolver {
    /// Per-check pivot budget (#uc-lia-unknown).
    ///
    /// The historical value was a FIXED 10,000 (`CHECK_PIVOT_BUDGET`), justified by
    /// "let the DPLL(T) loop try different theory-variable assignments instead". That
    /// premise holds on the plain check-sat path, where an early `Unknown` is recoverable.
    /// **It fails in the assumption lane**, where a theory `Unknown` is TERMINAL: the
    /// assume-arm split loop breaks immediately
    /// (`pipeline_incremental_split_assume_macros.rs:378-382`), the caller falls back to a
    /// conjoined re-solve, and in the UnsatCore track that fallback destroys assumption
    /// provenance — emitting a 100%-of-assertions core worth zero reduction on instances
    /// AY can otherwise answer.
    ///
    /// Measured 2026-07-27 on UC/QF_LinearIntArith `RwMutex-PT-r0010w1000/RF-10`
    /// (25,091 assertions): the first assumption-lane check exhausts the fixed budget and
    /// returns `Unknown` after ~8 s of a 1200 s budget, while the conjoined re-solve of the
    /// identical formula returns `UnsatWithFarkas` immediately.
    ///
    /// So scale the budget with the problem: this file's own documentation notes dense LPs
    /// need 10K-100K pivots per call. Bounded above so a pathological instance still cannot
    /// burn unbounded CPU — the wall-clock deadline remains the outer guard.
    #[inline]
    pub(crate) fn check_pivot_budget(&self) -> u32 {
        const MAX_CHECK_PIVOT_BUDGET: u64 = 1_000_000;
        // (B16: the AY_LRA_CHECK_PIVOT_BUDGET per-process override nothing
        // set is deleted; the scaled formula below IS the budget, and probing
        // a different one means editing it.)
        let scaled = (self.rows.len() as u64)
            .saturating_mul(4)
            .max(CHECK_PIVOT_BUDGET as u64)
            .min(MAX_CHECK_PIVOT_BUDGET);
        scaled as u32
    }
}
