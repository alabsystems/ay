// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl LraSolver {
    /// Find a suitable non-basic variable to pivot with (using Bland's rule)
    /// Returns (non_basic_var, direction) where direction is +1 or -1
    ///
    /// Bland's rule: to prevent cycling, always choose the eligible variable with
    /// the smallest index when there are ties. This guarantees termination.
    fn find_pivot_candidate(
        &self,
        row_idx: usize,
        violated_bound: BoundType,
    ) -> Option<(u32, i32)> {
        let row = &self.rows[row_idx];

        // Collect all eligible candidates, then pick smallest index (Bland's rule)
        let mut best: Option<(u32, i32)> = None;

        for &(nb_var, ref coeff) in &row.coeffs {
            if coeff.is_zero() {
                continue;
            }

            let info = &self.vars[nb_var as usize];

            // Skip basic variables that appear in coefficient lists (#4842).
            // After pivots rearrange the basis, incrementally-asserted rows
            // can reference variables that are now basic. Selecting a basic
            // variable as the entering pivot would violate the simplex invariant.
            if !matches!(info.status, Some(VarStatus::NonBasic)) {
                continue;
            }

            // Determine if we can increase or decrease this non-basic variable
            // based on its bounds. We can move if there's room (not at the bound).
            // Note: For strict bounds, being at the bound value is already a violation,
            // so we check if there's any room to move.
            let can_increase = match &info.upper {
                None => true,
                Some(b) => info.value.lt_bound(&b.value, b.strict, BoundType::Upper),
            };

            let can_decrease = match &info.lower {
                None => true,
                Some(b) => info.value.gt_bound(&b.value, b.strict, BoundType::Lower),
            };

            let direction = match violated_bound {
                BoundType::Lower => {
                    // Basic var is too small, need to increase it
                    // If coeff > 0: increase nb_var
                    // If coeff < 0: decrease nb_var
                    if coeff.is_positive() && can_increase {
                        Some(1)
                    } else if coeff.is_negative() && can_decrease {
                        Some(-1)
                    } else {
                        None
                    }
                }
                BoundType::Upper => {
                    // Basic var is too large, need to decrease it
                    // If coeff > 0: decrease nb_var
                    // If coeff < 0: increase nb_var
                    if coeff.is_positive() && can_decrease {
                        Some(-1)
                    } else if coeff.is_negative() && can_increase {
                        Some(1)
                    } else {
                        None
                    }
                }
            };

            if let Some(dir) = direction {
                // Bland's rule: keep the candidate with smallest variable index
                match &best {
                    None => best = Some((nb_var, dir)),
                    Some((best_var, _)) if nb_var < *best_var => best = Some((nb_var, dir)),
                    _ => {}
                }
            }
        }

        best
    }

    /// Find a beneficial entering variable using Z3's perturbation-minimizing
    /// heuristic for DPLL(T) feasibility search.
    ///
    /// Primary criterion: minimize `not_free_basic_dependent_vars` — the number
    /// of non-free basic variables in other rows that reference this column.
    /// This reduces cascading infeasibility from the pivot.
    /// Secondary: smallest column size (cheaper pivot update).
    /// Tiebreak: smallest variable index for determinism.
    ///
    /// Falls back to Bland when `bland_mode` is active (after repeated bases).
    ///
    /// #8003 TL87: Also returns the coefficient position within the row, enabling
    /// O(1) coefficient lookup in `compute_update_amount_with_coeff` instead of
    /// a redundant O(log w) binary search.
    ///
    /// Reference: Z3 `find_beneficial_entering_tableau_rows` in
    /// `lp_primal_core_solver.h:187-232`, `get_num_of_not_free_basic_dependent_vars`.
    pub(super) fn find_beneficial_entering(
        &mut self,
        row_idx: usize,
        violated_bound: BoundType,
    ) -> Option<(u32, i32, usize)> {
        if self.bland_mode {
            return self
                .find_pivot_candidate(row_idx, violated_bound)
                .map(|(var, dir)| {
                    // Bland path: find coefficient position via binary search.
                    let pos = self.rows[row_idx]
                        .coeffs
                        .binary_search_by_key(&var, |(v, _)| *v)
                        .unwrap_or(0);
                    (var, dir, pos)
                });
        }

        let row = &self.rows[row_idx];
        let basic_var = row.basic_var;

        // Score: (not_free_deps, col_size) — all minimized.
        // `tie_count` tracks how many candidates share the current best score,
        // for reservoir sampling tiebreak (Z3 simplex_def.h:575-580).
        // #8003 TL87: Track coeff_pos (index into row.coeffs) for the best
        // candidate, enabling O(1) coefficient access after selection.
        let mut best: Option<(u32, i32, usize, usize, usize)> = None; // (var, dir, nf_deps, col_sz, coeff_pos)
        let mut tie_count: u32 = 0;

        for (coeff_pos, &(nb_var, ref coeff)) in row.coeffs.iter().enumerate() {
            if coeff.is_zero() {
                continue;
            }

            let info = &self.vars[nb_var as usize];

            // Skip basic variables (#4842) — same guard as find_pivot_candidate.
            if !matches!(info.status, Some(VarStatus::NonBasic)) {
                continue;
            }

            let can_increase = match &info.upper {
                None => true,
                Some(b) => info.value.lt_bound(&b.value, b.strict, BoundType::Upper),
            };
            let can_decrease = match &info.lower {
                None => true,
                Some(b) => info.value.gt_bound(&b.value, b.strict, BoundType::Lower),
            };

            let direction = match violated_bound {
                BoundType::Lower => {
                    if coeff.is_positive() && can_increase {
                        Some(1)
                    } else if coeff.is_negative() && can_decrease {
                        Some(-1)
                    } else {
                        None
                    }
                }
                BoundType::Upper => {
                    if coeff.is_positive() && can_decrease {
                        Some(-1)
                    } else if coeff.is_negative() && can_increase {
                        Some(1)
                    } else {
                        None
                    }
                }
            };

            if let Some(dir) = direction {
                // Count non-free basic variables that depend on this column.
                // Z3: get_num_of_not_free_basic_dependent_vars (lp_primal_core_solver.h:147-160).
                // Use column index for O(col_size); fall back to 0 if unavailable.
                let best_nf = best.as_ref().map_or(usize::MAX, |b| b.2);
                let not_free_deps = self.count_not_free_basic_deps(nb_var, basic_var, best_nf);
                let col_sz = self.col_size(nb_var);

                let is_strictly_better = match &best {
                    None => true,
                    Some((_, _, best_nfd, best_csz, _)) => {
                        not_free_deps < *best_nfd
                            || (not_free_deps == *best_nfd && col_sz < *best_csz)
                    }
                };
                if is_strictly_better {
                    best = Some((nb_var, dir, not_free_deps, col_sz, coeff_pos));
                    tie_count = 1;
                } else if let Some((_, _, best_nfd, best_csz, _)) = &best {
                    // Tie: same (not_free_deps, col_size). Use reservoir sampling
                    // to pick uniformly at random among tied candidates.
                    // Reference: Z3 simplex_def.h:575-580.
                    if not_free_deps == *best_nfd && col_sz == *best_csz {
                        tie_count += 1;
                        let r = Self::pivot_xorshift32(&mut self.pivot_rng) % tie_count;
                        if r == 0 {
                            best = Some((nb_var, dir, not_free_deps, col_sz, coeff_pos));
                        }
                    }
                }
            }
        }

        best.map(|(var, dir, _, _, coeff_pos)| (var, dir, coeff_pos))
    }

    /// Xorshift32 PRNG for pivot tiebreaking. Fast, minimal state.
    #[inline]
    fn pivot_xorshift32(state: &mut u32) -> u32 {
        let mut x = *state;
        x ^= x << 13;
        x ^= x >> 17;
        x ^= x << 5;
        *state = x;
        x
    }

    /// Count non-free basic variables in other rows that depend on column `nb_var`,
    /// excluding the row containing `excluded_basic`. Stops early when count
    /// exceeds `bound` (the current best), avoiding full column scan.
    ///
    /// Reference: Z3 `get_num_of_not_free_basic_dependent_vars`
    /// (lp_primal_core_solver.h:147-160).
    fn count_not_free_basic_deps(&self, nb_var: u32, excluded_basic: u32, bound: usize) -> usize {
        let vi = nb_var as usize;
        if vi >= self.col_index.len() || self.col_index[vi].is_empty() {
            // No column index: conservative estimate — treat as expensive.
            return bound;
        }
        let mut count = 0usize;
        for entry in &self.col_index[vi] {
            let basic = self.rows[entry.row_idx].basic_var;
            if basic == excluded_basic {
                continue;
            }
            let bi = basic as usize;
            if bi < self.vars.len() {
                let basic_info = &self.vars[bi];
                let is_free = basic_info.lower.is_none() && basic_info.upper.is_none();
                if !is_free {
                    count += 1;
                    if count > bound {
                        return count; // early exit
                    }
                }
            }
        }
        count
    }

    /// Ensure column index is large enough for variable `var`.
    fn ensure_col_index(&mut self, var: u32) {
        let vi = var as usize;
        if vi >= self.col_index.len() {
            self.col_index.resize(vi + 1, Vec::new());
        }
    }

    /// Remove the entry for `row_idx` from `col_index[var]`.
    fn col_index_remove(&mut self, var: u32, row_idx: usize) {
        let vi = var as usize;
        if vi < self.col_index.len() {
            if let Some(pos) = self.col_index[vi].iter().position(|e| e.row_idx == row_idx) {
                self.col_index[vi].swap_remove(pos);
            }
        }
    }

    /// Add `row_idx` to `col_index[var]` with the coefficient position (#8066).
    /// Computes `row_pos` via binary search on the row's sorted coefficient vector.
    pub(crate) fn col_index_add(&mut self, var: u32, row_idx: usize) {
        self.ensure_col_index(var);
        let vi = var as usize;
        debug_assert!(
            !self.col_index[vi].iter().any(|e| e.row_idx == row_idx),
            "BUG: col_index[{var}] already contains row {row_idx}"
        );
        // Compute the position of `var` in the row's coefficient vector.
        let row_pos = self.rows[row_idx]
            .coeffs
            .binary_search_by_key(&var, |(v, _)| *v)
            .unwrap_or_else(|_| {
                // Production soundness gate: col_index references a variable
                // that is not in the row. Use position 0 as a fallback — the
                // index will be stale but the solver will detect inconsistency
                // on the next pivot and recover.
                safe_eprintln!(
                    "BUG: col_index_add({var}, row {row_idx}) but var not in row coeffs"
                );
                0
            });
        self.col_index[vi].push(ColEntry::new(row_idx, row_pos));
    }

    /// Rebuild all col_index row_pos values for a given row in one pass (#8465).
    /// Called after substitution modifies the coefficient vector. Uses O(row_width)
    /// total work by iterating the row once and doing O(1) amortized update per
    /// column entry (scanning only entries for columns that appear in this row).
    ///
    /// #8003 TL87: No longer called during pivot — stale row_pos values are
    /// handled by O(log w) binary-search fallbacks in consumers, which is cheaper
    /// than the O(w * col_size) per-row cost of this function on dense LPs.
    /// Retained for use in non-pivot row modifications (e.g., row addition).
    #[allow(dead_code)]
    fn update_col_index_positions_for_row(&mut self, row_idx: usize) {
        // Single pass over the row's coefficients to update all column index entries.
        let num_coeffs = self.rows[row_idx].coeffs.len();
        for pos in 0..num_coeffs {
            let var = self.rows[row_idx].coeffs[pos].0;
            let vi = var as usize;
            if vi < self.col_index.len() {
                for entry in &mut self.col_index[vi] {
                    if entry.row_idx == row_idx {
                        entry.row_pos = pos;
                        break;
                    }
                }
            }
        }
    }

    /// Get the column size (number of rows containing this variable).
    /// Returns 0 if the variable has no column index entry.
    fn col_size(&self, var: u32) -> usize {
        let vi = var as usize;
        if vi < self.col_index.len() {
            self.col_index[vi].len()
        } else {
            0
        }
    }

    /// Pop the last row and clean up column index entries.
    /// Used by optimization.rs for temporary objective rows.
    pub(crate) fn pop_row_with_col_cleanup(&mut self) {
        if let Some(row) = self.rows.pop() {
            let popped_idx = self.rows.len(); // index of the removed row
            for (v, _) in &row.coeffs {
                self.col_index_remove(*v, popped_idx);
            }
        }
    }

    /// Perform a pivot operation
    pub(crate) fn pivot(&mut self, row_idx: usize, entering_var: u32) {
        debug_assert!(
            row_idx < self.rows.len(),
            "BUG: pivot row {} out of bounds (rows={})",
            row_idx,
            self.rows.len()
        );
        debug_assert!(
            (entering_var as usize) < self.vars.len(),
            "BUG: pivot entering var {} out of bounds (vars={})",
            entering_var,
            self.vars.len()
        );
        debug_assert!(
            matches!(
                self.vars[entering_var as usize].status,
                Some(VarStatus::NonBasic)
            ),
            "BUG: pivot entering var {} must be non-basic, got {:?}",
            entering_var,
            self.vars[entering_var as usize].status
        );
        let leaving_var = self.rows[row_idx].basic_var;
        trace!(
            target: "ay::lra",
            row_idx,
            entering_var,
            leaving_var,
            "LRA pivot start"
        );

        if self.pivot_row_cache.has_pending_background_work() {
            let _ = self.pivot_row_cache.install_ready_results();
        }

        // Get coefficient of entering variable in the row via coeff_ref + clone
        // to avoid redundant binary search in coeff().
        let entering_coeff = self.rows[row_idx]
            .coeff_ref(entering_var)
            .cloned()
            .unwrap_or_else(Rational::zero);

        // Invariant: caller should only select entering variables with non-zero coefficient.
        // Keep this as a hard assertion so release builds do not silently continue
        // with invalid tableau state.
        assert!(
            !entering_coeff.is_zero(),
            "BUG: pivot called with zero coefficient for entering variable {entering_var} in row {row_idx}"
        );

        // Capture old row variables for column index update (only if col_index is populated)
        let use_col_index = !self.col_index.is_empty();
        let old_pivot_row_vars: Vec<u32> = if use_col_index {
            self.rows[row_idx].coeffs.iter().map(|(v, _)| *v).collect()
        } else {
            Vec::new()
        };

        // Rearrange: leaving_var = ... + entering_coeff * entering_var + ...
        // => entering_var = (leaving_var - ... - ...) / entering_coeff

        // Build new row for entering_var: use recip() to avoid Rational::one()
        // allocation + division overhead.
        let inv_coeff = entering_coeff.recip();
        let neg_inv_coeff = -inv_coeff.clone();

        let mut new_coeffs: Vec<(u32, Rational)> =
            Vec::with_capacity(self.rows[row_idx].coeffs.len() + 1);

        // Add leaving_var with coefficient 1/entering_coeff
        new_coeffs.push((leaving_var, inv_coeff));

        // Add other variables with negated scaled coefficients
        for &(v, ref c) in &self.rows[row_idx].coeffs {
            if v != entering_var {
                let new_c = c * &neg_inv_coeff;
                if !new_c.is_zero() {
                    new_coeffs.push((v, new_c));
                }
            }
        }

        let new_constant = &self.rows[row_idx].constant * &neg_inv_coeff;

        // Update the row
        self.rows[row_idx] = TableauRow::new_rat(entering_var, new_coeffs, new_constant);

        // Update column index for the pivot row itself:
        // Remove old variable entries, add new ones (#8465: use direct pos instead of binary search)
        if use_col_index {
            for &v in &old_pivot_row_vars {
                self.col_index_remove(v, row_idx);
            }
            // Collect new vars + positions to break the borrow on self.rows
            let new_row_entries: Vec<(u32, usize)> = self.rows[row_idx]
                .coeffs
                .iter()
                .enumerate()
                .map(|(pos, &(v, _))| (v, pos))
                .collect();
            for (v, pos) in new_row_entries {
                self.ensure_col_index(v);
                self.col_index[v as usize].push(ColEntry::new(row_idx, pos));
            }
        }

        // Update variable statuses
        self.vars[leaving_var as usize].status = Some(VarStatus::NonBasic);
        self.vars[entering_var as usize].status = Some(VarStatus::Basic(row_idx));

        // Update basic_var_to_row: leaving_var is no longer basic, entering_var takes the row
        self.basic_var_to_row.remove(&leaving_var);
        self.basic_var_to_row.insert(entering_var, row_idx);
        self.advance_lra_basis_region_basis_epoch();

        // Track pivot row reuse for JIT compilation (#8276).
        // Use per-row precision tracking (#8185) for integer coefficient extraction.
        // Must run BEFORE taking the row data out.
        {
            let int_coeffs = if self.rows[row_idx].is_all_i64() {
                self.rows[row_idx].extract_i64_coeffs()
            } else {
                None
            };
            self.pivot_row_cache
                .record_pivot(row_idx, int_coeffs.as_deref());
        }

        // Take pivot row data out temporarily to avoid O(w) clone per pivot (#8003 TL65).
        // The pivot row coefficients are needed for substitution in all affected rows,
        // but the pivot row itself (row_idx) is excluded from substitution targets.
        // Using take+restore avoids heap allocation; the Vec capacity is preserved.
        let new_row_coeffs = std::mem::take(&mut self.rows[row_idx].coeffs);
        let new_row_constant = std::mem::take(&mut self.rows[row_idx].constant);

        // Substitute in all other rows that contain entering_var.
        // Use column index for O(nnz) instead of O(rows) scan (#4919 Phase 1).
        // Fall back to full scan if column index is not populated.
        let evi = entering_var as usize;
        let use_col_index = !self.col_index.is_empty();
        // Carry Option<row_pos> for O(1) coefficient access in affected rows (#8066).
        let affected_rows: Vec<(usize, Option<usize>)> =
            if use_col_index && evi < self.col_index.len() {
                self.col_index[evi]
                    .iter()
                    .filter(|e| e.row_idx != row_idx)
                    .map(|e| (e.row_idx, Some(e.row_pos)))
                    .collect()
            } else if use_col_index {
                // Column index exists but entering_var has no entry — no rows affected
                Vec::new()
            } else {
                // No column index — fall back to scanning all rows
                (0..self.rows.len())
                    .filter(|&i| i != row_idx)
                    .map(|i| (i, None))
                    .collect()
            };
        self.remember_lra_basis_region_candidate(row_idx, entering_var, &affected_rows);

        if self.pivot_row_cache.has_pending_background_work() {
            let _ = self.pivot_row_cache.install_ready_results();
        }

        // Approach D (#4919): track pivot-affected rows for bound propagation.
        // Z3's pivot_column_tableau inserts every modified row into m_touched_rows
        // (lp_core_solver_base_def.h:285). This feeds compute_implied_bounds with
        // rows where the bound analyzer may now succeed after pivoting.
        self.touched_rows.insert(row_idx);

        // Reusable scratch buffers for column-index deltas (#8003).
        // substitute_var_with_col_deltas tracks additions/removals during the
        // sorted merge itself, eliminating O(new_row_width * log(row_width))
        // post-hoc binary searches per affected row.
        let mut col_added: Vec<u32> = Vec::new();
        let mut col_removed: Vec<u32> = Vec::new();
        // Work-vector: O(1) coefficient lookup (#8003 Gap 2).
        let max_var = self.next_var as usize + 1;
        let mut wv = std::mem::take(&mut self.pivot_work_vec);
        let mut wd = std::mem::take(&mut self.pivot_work_dirty);
        if wv.len() < max_var {
            wv.resize(max_var, -1);
        }

        // Pre-compute i128 substitution terms once per pivot (#8003 TL65).
        // When all pivot row coefficients fit in i64, compute (var, i128_coeff)
        // pairs ONCE and reuse across all affected rows. This eliminates
        // per-row Vec<(u32, i128)> allocation in substitute_var_i64_with_col_deltas.
        // The i128 values are UNSCALED (scale=1); per-row scaling is applied inside
        // substitute_var_i64_precomputed.
        // Pre-compute i128 substitution terms from taken-out pivot row data.
        // Try to extract all pivot row coefficients as i64 in a single pass.
        // If any coefficient doesn't fit, fall back to per-row allocation.
        let mut precomputed_i128 = std::mem::take(&mut self.pivot_subst_i64_buf);
        precomputed_i128.clear();
        let have_precomputed = {
            let mut ok = true;
            for &(v, ref c) in new_row_coeffs.iter() {
                if v == entering_var {
                    continue;
                }
                match c.to_i64() {
                    Some(n) if n != 0 => precomputed_i128.push((v, i128::from(n))),
                    Some(_) => {} // zero coefficient, skip
                    None => {
                        ok = false;
                        break;
                    }
                }
            }
            ok
        };

        let batch_substitute_applied = false;

        const JIT_INSTALL_POLL_STRIDE: usize = 32;
        if !batch_substitute_applied {
            for (affected_idx, (i, maybe_pos)) in affected_rows.into_iter().enumerate() {
                if affected_idx != 0
                    && affected_idx % JIT_INSTALL_POLL_STRIDE == 0
                    && self.pivot_row_cache.has_pending_background_work()
                {
                    let _ = self.pivot_row_cache.install_ready_results();
                }

                // O(1) coefficient access via cached row_pos when available (#8066).
                let old_coeff = if let Some(pos) = maybe_pos {
                    // O(1) path: use cached position from column index
                    if pos < self.rows[i].coeffs.len() && self.rows[i].coeffs[pos].0 == entering_var
                    {
                        let c = &self.rows[i].coeffs[pos].1;
                        if c.is_zero() {
                            continue;
                        }
                        c.clone()
                    } else {
                        // Fallback: position stale, use binary search
                        match self.rows[i].coeff_ref(entering_var) {
                            Some(c) if !c.is_zero() => c.clone(),
                            _ => continue,
                        }
                    }
                } else {
                    // No column index — use binary search
                    match self.rows[i].coeff_ref(entering_var) {
                        Some(c) if !c.is_zero() => c.clone(),
                        _ => continue,
                    }
                };
                // Track this row as pivot-modified (#4919 Approach D).
                self.touched_rows.insert(i);

                // #8003 TL87: Track whether work-vec substitution was used, so we
                // can use work_vec positions for O(1) col_index position updates
                // instead of the O(w * col_size) update_col_index_positions_for_row.
                let mut used_work_vec = false;

                let used_compiled_substitute = false;

                if use_col_index {
                    // Substitution fast-path cascade for col-index pivot (#8257):
                    // 1. external code generation compiled substitute (fastest, when available)
                    // 2. i64/i128 sorted-merge with col deltas (no Rational dispatch)
                    // 3. Work-vector enhanced Rational substitute (general fallback)
                    //
                    // The dense batch-pivot ABI is intentionally not used here yet:
                    // it mutates dense coefficient arrays in place, while this sparse
                    // hot path must also remove `entering_var`, preserve sorted sparse
                    // rows, compute column-index deltas, and update constants.
                    // See external_codegen_pivot::test_dense_batch_abi_missing_sparse_adapter.
                    let mut used_fast = false;

                    // #8257/#8003 TL65: i64/i128 fast path with col deltas.
                    // Avoids Rational enum dispatch entirely for integer-coefficient rows.
                    // When precomputed_i128 is available, uses the zero-alloc path that
                    // reuses pre-scaled terms from the pivot row across all affected rows.
                    if !used_fast && self.rows[i].is_all_i64() && old_coeff.is_integer_i64() {
                        if have_precomputed {
                            let scale = old_coeff.to_i64().unwrap_or(0);
                            if scale != 0 {
                                used_fast = self.rows[i].substitute_var_i64_precomputed(
                                    entering_var,
                                    &precomputed_i128,
                                    scale,
                                    &mut col_added,
                                    &mut col_removed,
                                );
                            }
                        }
                        if !used_fast {
                            used_fast = self.rows[i].substitute_var_i64_with_col_deltas(
                                entering_var,
                                &new_row_coeffs,
                                &old_coeff,
                                &mut col_added,
                                &mut col_removed,
                            );
                        }
                    }

                    // General Rational fallback with work-vector O(1) lookup.
                    if !used_fast {
                        self.rows[i].substitute_var_work_vec(
                            entering_var,
                            &new_row_coeffs,
                            &old_coeff,
                            &mut wv,
                            &mut wd,
                            &mut col_added,
                            &mut col_removed,
                        );
                        // #8003 TL87: Use work_vec positions to update col_index
                        // entries in O(1) per variable, replacing the O(w * col_size)
                        // update_col_index_positions_for_row call below.
                        used_work_vec = true;
                        // Don't reset work_vec yet — positions are consumed below.
                    }
                } else {
                    // No column index — try compiled external code generation substitute (#8380), then i64
                    // fast path (#8185), fall back to generic Rational path.
                    let mut used_fast = false;

                    if !used_fast {
                        used_fast = self.rows[i].is_all_i64()
                            && old_coeff.is_integer_i64()
                            && self.rows[i].substitute_var_i64(
                                entering_var,
                                &new_row_coeffs,
                                &old_coeff,
                            );
                    }
                    if !used_fast {
                        self.rows[i].substitute_var(entering_var, &new_row_coeffs, &old_coeff);
                    }
                }

                if !used_compiled_substitute {
                    self.pivot_row_cache.record_substitute_fallback_apply();
                }

                // Update constant: fast-path for ±1 old_coeff (common in sparse LRA).
                // #8406: use fused add_product when both are Small to avoid intermediate alloc.
                if old_coeff.is_one() {
                    self.rows[i].constant += &new_row_constant;
                } else if old_coeff.is_neg_one() {
                    self.rows[i].constant -= &new_row_constant;
                } else {
                    self.rows[i]
                        .constant
                        .add_product(&old_coeff, &new_row_constant);
                }

                // Apply column-index deltas computed during the merge (#8003).
                if use_col_index {
                    for &v in &col_removed {
                        self.col_index_remove(v, i);
                    }
                    for &v in &col_added {
                        self.col_index_add(v, i);
                    }
                    // #8003 TL87: Skip update_col_index_positions_for_row entirely.
                    // The old code called update_col_index_positions_for_row(i) which
                    // is O(w * col_size) — for each variable in the row, it linearly
                    // scans the column index entries to find the matching row. On dense
                    // LPs (w ~ 300, col_size ~ 300), this is O(90K) per affected row,
                    // totaling O(R^3) per pivot — catastrophic for dense problems.
                    //
                    // Instead, we accept that row_pos values in ColEntry may become
                    // stale after substitution shifts coefficient positions. All
                    // consumers of row_pos (update_nonbasic, pivot coefficient access)
                    // already have O(log w) binary-search fallbacks when the cached
                    // position doesn't match (entry.row_pos is validated before use).
                    // For dense LPs, O(w * log w) fallback << O(w * col_size) update.
                    // For sparse LPs, most positions are stable (few removals), so
                    // stale rate is low and the fallback is rarely triggered.
                    //
                    // New entries from col_index_add get correct positions at creation.
                    // Surviving entries may have stale positions if intervening entries
                    // were removed, but the fallback handles this correctly.
                }

                // Reset work_vec if it was used (#8003 Gap 2).
                if used_work_vec {
                    for &var in &wd {
                        wv[var as usize] = -1;
                    }
                    wd.clear();
                }

                // Recompute precision for the modified row (#8185).
                self.rows[i].recompute_precision();
                match self.rows[i].precision() {
                    RowPrecision::I64 => self.stats.precision_i64_rows += 1,
                    RowPrecision::I128 => self.stats.precision_i128_rows += 1,
                    RowPrecision::Big => self.stats.precision_big_rows += 1,
                }
            }
        }

        // Restore work vector (#8003 Gap 2).
        self.pivot_work_vec = wv;
        self.pivot_work_dirty = wd;

        // Restore precomputed i128 buffer (#8003 TL65).
        self.pivot_subst_i64_buf = precomputed_i128;

        // Restore pivot row coefficients and constant (#8003 TL65).
        // They were taken out to avoid cloning; put them back now.
        self.rows[row_idx].coeffs = new_row_coeffs;
        self.rows[row_idx].constant = new_row_constant;

        // entering_var is now basic (in its own row) — remove it from col_index
        // entries of other rows (should already be handled above), and remove
        // row_idx from entering_var's column (it's the basic var, not a coefficient)
        if use_col_index {
            self.col_index_remove(entering_var, row_idx);
        }

        // Recompute precision for the pivot row and all affected rows (#8185).
        self.rows[row_idx].recompute_precision();
        match self.rows[row_idx].precision() {
            RowPrecision::I64 => self.stats.precision_i64_rows += 1,
            RowPrecision::I128 => self.stats.precision_i128_rows += 1,
            RowPrecision::Big => self.stats.precision_big_rows += 1,
        }

        debug_assert_eq!(
            self.rows[row_idx].basic_var, entering_var,
            "BUG: pivot did not install entering var {entering_var} as row {row_idx} basic var"
        );
        debug_assert!(
            self.rows[row_idx].coeff(entering_var).is_zero(),
            "BUG: pivot row {row_idx} still has entering var {entering_var} coefficient"
        );
        #[cfg(debug_assertions)]
        self.debug_assert_tableau_consistency("pivot");
        #[cfg(debug_assertions)]
        if use_col_index {
            self.debug_assert_col_index_consistency("pivot");
        }
        debug!(
            target: "ay::lra",
            row_idx,
            entering_var,
            leaving_var,
            row_non_basic_terms = self.rows[row_idx].coeffs.len(),
            "LRA pivot complete"
        );
    }
}
