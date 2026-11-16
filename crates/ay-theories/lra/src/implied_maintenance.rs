// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Incremental bookkeeping for the implied-bound overlay.
//!
//! `compute_implied_bounds` analyzes only rows whose inputs or content
//! changed since their last analysis. This module owns the invariant that
//! makes that complete: the touched-row set is the full record of such rows
//! — bound assertions and pops seed the rows of every variable whose bound
//! changed (`stamp_var_for_rederivation`, `note_direct_bound_widened`),
//! pivots mark every row they rewrite (`mark_row_content_changed`), new
//! rows are seeded at creation, the cascade reseeds the rows of newly
//! bounded variables — and the row-selection rule that consumes it
//! (`take_rows_to_analyze`) and the direct-bound overlay it depends on
//! (`overlay_direct_bounds`). It also captures the value-carrying
//! derivation-time explanation of a row-derived bound
//! (`explanation_from_contribs`).

use super::*;

impl LraSolver {
    /// Overlay the current DIRECT bounds into the `implied_bounds` slots
    /// and report whether EVERY variable was re-overlaid.
    ///
    /// A direct bound always replaces a missing implied bound; when both
    /// exist the tighter one is kept (direct bounds are always valid;
    /// implied bounds may be tighter from previous fixpoint passes). Direct
    /// bounds are marked in the slot by the sentinel `row_idx == usize::MAX`.
    ///
    /// Nothing is done when no direct bound changed since the last call
    /// (`direct_bounds_changed_since_implied == false`): the overlay would
    /// recompute the same comparisons. Skipping that O(num_vars) loop
    /// eliminates the dominant per-BCP cost when the theory callback fires
    /// on cascade rows without new bound assertions.
    ///
    /// `need_resize` (new variables since the last call) forces the full
    /// scan; otherwise a non-empty `direct_bounds_changed_vars` selects the
    /// incremental path (#8782), which overlays and stamps only those
    /// variables. The return value is `true` only for the full scan — that
    /// is what makes an empty touched-row set in `compute_implied_bounds`
    /// mean "sweep every row" rather than "nothing changed"
    /// (`take_rows_to_analyze`).
    pub(crate) fn overlay_direct_bounds(&mut self, num_vars: usize, need_resize: bool) -> bool {
        let mut did_full_overlay = false;
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
                // A u64 bumped at most once per call cannot reach `u64::MAX`.
                self.bound_generation = self.bound_generation.saturating_add(1);
                let cur_gen = self.bound_generation;
                for &var in &changed {
                    let i = var as usize;
                    if i >= self.vars.len() {
                        continue;
                    }
                    self.big_bound_seen |= Self::var_has_big_direct_bound(&self.vars[i]);
                    let changed = Self::overlay_direct_bound_for_var(
                        &self.vars[i],
                        &mut self.implied_bounds[i],
                    );
                    self.register_fixed_term_var(var);
                    // Stamp variable so rows containing it are re-analyzed —
                    // only when the overlay actually changed the slot, as
                    // the full-scan path below already does. Row arithmetic
                    // reads only slot values/strictness, so stamping an
                    // unchanged slot (a direct bound weaker than the stored
                    // derived bound) only re-analyzes its rows to identical
                    // results, defeating the generation skip.
                    if changed && i < self.var_bound_gen.len() {
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
                self.stats.implied_full_overlays =
                    self.stats.implied_full_overlays.saturating_add(1);
                did_full_overlay = true;
                // #8857: Full-scan overlay is a lattice rebuild — reset all
                // Zeno-throttle streaks.
                self.implied_tighten_streak.fill(0);
                // #8003: Full scan — bump generation and stamp all vars.
                self.bound_generation = self.bound_generation.saturating_add(1);
                let cur_gen = self.bound_generation;
                let mut fixed_vars = std::mem::take(&mut self.ib_fixed_vars_scratch);
                fixed_vars.clear();
                // Capacity hint only: if the reservation fails, `push` grows
                // the scratch vector as variables are visited.
                let _ = fixed_vars.try_reserve(num_vars);
                let mut any_big = false;
                for (i, info) in self.vars.iter().enumerate() {
                    any_big |= Self::var_has_big_direct_bound(info);
                    // Stamp only variables whose slot actually changed.
                    // Restamping every variable made the generation skip
                    // useless after any full overlay (resize/pop rebuild):
                    // every row then looked newer than its last analysis
                    // (measured on Gcd: 4,040 full overlays, 35M rows
                    // re-analyzed in 20 s for 72k delivered propagations).
                    // The skip compares only stamps, and row arithmetic
                    // reads only slot values/strictness, so an unchanged
                    // slot needs no new generation.
                    let changed =
                        Self::overlay_direct_bound_for_var(info, &mut self.implied_bounds[i]);
                    fixed_vars.push(i as u32);
                    if changed && i < self.var_bound_gen.len() {
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
        did_full_overlay
    }

    /// Rows the current `compute_implied_bounds` call analyzes.
    ///
    /// `Some(rows)` restricts the sweep to those rows (possibly none);
    /// `None` sweeps every row. An EMPTY touched set means nothing to
    /// analyze — unless this call re-overlaid every variable (new variables,
    /// resets: `did_full_overlay`) or no complete sweep has happened yet
    /// (`ib_overlay_complete` false); only then is a full sweep warranted.
    /// Previously an empty set always meant a full sweep, and every pop
    /// forced one (measured: 11,267 full sweeps of 1,123 rows in 163,957
    /// calls on sc-34, 38% of all rows scanned).
    pub(crate) fn take_rows_to_analyze(&mut self, did_full_overlay: bool) -> Option<DenseIdxSet> {
        if !self.touched_rows.is_empty() {
            Some(std::mem::take(&mut self.touched_rows))
        } else if did_full_overlay || !self.ib_overlay_complete {
            None
        } else {
            Some(DenseIdxSet::default())
        }
    }

    /// Build the derivation-time explanation of a row-derived bound from the
    /// contribution list of one row direction (#6617, value-carrying).
    ///
    /// `contribs` holds `(var, eq_coeff, strict)` for every variable of the
    /// row equation `sum(eq_coeff_i * x_i) = constant` whose bound was
    /// consumed; `ub_direction` selects which side each coefficient sign
    /// consumed (LB direction: `eq_c > 0` used the lower bound; UB
    /// direction: `eq_c > 0` used the upper bound). The target variable is
    /// excluded. The consumed bound is read from the `implied_bounds` slot,
    /// which is exactly what the accumulation loop read: slots are not
    /// written while a cascade round analyzes rows (updates are deferred to
    /// the end of the round). Returns `None` if any antecedent slot is
    /// unexpectedly empty — an explanation must be complete or absent, never
    /// partial.
    pub(crate) fn explanation_from_contribs(
        &self,
        contribs: &[(usize, Rational, bool)],
        target_vi: usize,
        ub_direction: bool,
    ) -> Option<BoundExplanation> {
        // Every contribution but the target's own lands here: size the buffer
        // once instead of growing it push by push past the inline capacity.
        let mut contributing_vars: SmallVec<[Antecedent; 3]> =
            SmallVec::with_capacity(contribs.len().saturating_sub(1));
        for &(other_vi, ref other_eq_c, _) in contribs {
            if other_vi == target_vi {
                continue;
            }
            let used_upper = if ub_direction {
                other_eq_c.is_positive()
            } else {
                other_eq_c.is_negative()
            };
            let slot = self.implied_bounds.get(other_vi)?;
            let ib = if used_upper {
                slot.1.as_ref()?
            } else {
                slot.0.as_ref()?
            };
            contributing_vars.push(Antecedent {
                var: other_vi as u32,
                used_upper,
                strict: ib.strict,
                value: ib.value.clone(),
            });
        }
        Some(BoundExplanation { contributing_vars })
    }

    /// The equation stored at `row_idx` changed (pivot substitution, new
    /// row): clear its analysis stamp so the generation skip — which assumes
    /// a row's content is immutable between analyses and compares only its
    /// variables' bound stamps — cannot skip it. The row must also be in
    /// `touched_rows` (the callers insert it).
    #[inline]
    pub(crate) fn mark_row_content_changed(&mut self, row_idx: usize) {
        if let Some(stamp) = self.row_computed_gen.get_mut(row_idx) {
            *stamp = 0;
        }
    }

    /// Stamp `var` so every row containing it is re-analyzed by the next
    /// `compute_implied_bounds`: bump its bound generation (the generation
    /// skip compares row stamps against variable stamps), reset its Zeno
    /// streak, and seed `touched_rows` with its column and defining row.
    /// O(column size).
    pub(crate) fn stamp_var_for_rederivation(&mut self, var: u32) {
        let vi = var as usize;
        // A u64 bumped once per call cannot reach `u64::MAX`.
        self.bound_generation = self.bound_generation.saturating_add(1);
        if vi < self.var_bound_gen.len() {
            self.var_bound_gen[vi] = self.bound_generation;
        }
        if vi < self.implied_tighten_streak.len() {
            self.implied_tighten_streak[vi] = 0;
        }
        if vi < self.col_index.len() {
            for entry in &self.col_index[vi] {
                self.touched_rows.insert(entry.row_idx);
            }
        }
        if let Some(&ri) = self.basic_var_to_row.get(&var) {
            self.touched_rows.insert(ri);
        }
    }

    /// A direct bound on `var` was WIDENED: a scope pop restored an outer
    /// bound, or an unjustified bound was retracted.
    ///
    /// Direct-bound overlays into `implied_bounds` are not trailed, so the
    /// slot may still hold the retracted (tighter) value. Drop any
    /// direct-overlay entry (`row_idx == usize::MAX`) on either side — the
    /// next `compute_implied_bounds` re-overlays whatever direct bound the
    /// variable carries now, incrementally — but KEEP row-derived entries:
    /// those are trailed (`implied_trail`), so whatever the slot holds after
    /// the rewind was derived at a scope that is still open and remains
    /// valid. Then stamp the variable so its rows re-derive. Replaces the
    /// former `(None, None)` reset plus forced full overlay and full sweep,
    /// which re-derived the whole tableau after every backtrack.
    pub(crate) fn note_direct_bound_widened(&mut self, var: u32) {
        let vi = var as usize;
        if let Some(slot) = self.implied_bounds.get_mut(vi) {
            if slot.0.as_ref().is_some_and(|b| b.row_idx == usize::MAX) {
                slot.0 = None;
            }
            if slot.1.as_ref().is_some_and(|b| b.row_idx == usize::MAX) {
                slot.1 = None;
            }
        }
        self.direct_bounds_changed_since_implied = true;
        self.direct_bounds_changed_vars.push(var);
        self.stamp_var_for_rederivation(var);
    }
}
