// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl LraSolver {
    /// Compute how much to change a non-basic variable to fix a basic variable's bound violation.
    /// Returns the new value for the non-basic variable.
    #[allow(dead_code)]
    pub(super) fn compute_update_amount(
        &self,
        row_idx: usize,
        nb_var: u32,
        violated_bound: BoundType,
    ) -> InfRational {
        let coeff_ref = match self.rows[row_idx].coeff_ref(nb_var) {
            Some(c) if !c.is_zero() => c,
            _ => return InfRational::default(),
        };
        self.compute_update_amount_with_coeff(row_idx, nb_var, violated_bound, coeff_ref)
    }

    /// Like `compute_update_amount` but takes a pre-fetched coefficient reference,
    /// avoiding a redundant O(log w) binary search when the caller (e.g.,
    /// `find_beneficial_entering`) already has the coefficient (#8003 TL87).
    pub(super) fn compute_update_amount_with_coeff(
        &self,
        row_idx: usize,
        nb_var: u32,
        violated_bound: BoundType,
        coeff_ref: &Rational,
    ) -> InfRational {
        let row = &self.rows[row_idx];
        let basic_var = row.basic_var;
        let basic_info = &self.vars[basic_var as usize];
        let nb_info = &self.vars[nb_var as usize];

        let target_basic = match violated_bound {
            BoundType::Lower => match &basic_info.lower {
                Some(b) => b.as_inf(BoundType::Lower),
                None => InfRational::default(),
            },
            BoundType::Upper => match &basic_info.upper {
                Some(b) => b.as_inf(BoundType::Upper),
                None => InfRational::default(),
            },
        };

        let basic_delta = &target_basic - &basic_info.value;
        // #8406: i64 fast path for reciprocal multiplication. When coeff is
        // Small(n, d), its reciprocal is (d, n) with sign adjustment.
        let nb_target = if let Rational::Small(cn, cd) = coeff_ref {
            let (inv_n, inv_d) = if *cn > 0 {
                (*cd, *cn)
            } else if *cn < 0 {
                (cd.wrapping_neg(), cn.wrapping_neg())
            } else {
                let inv_coeff = coeff_ref.recip();
                return &nb_info.value + &basic_delta.mul_rat(&inv_coeff);
            };
            &nb_info.value + &basic_delta.mul_rat_i64(inv_n, inv_d)
        } else {
            let inv_coeff = coeff_ref.recip();
            &nb_info.value + &basic_delta.mul_rat(&inv_coeff)
        };

        // Clamp to nb_var's bounds
        let clamped = if let Some(ref lb) = nb_info.lower {
            let lb_inf = lb.as_inf(BoundType::Lower);
            if nb_target < lb_inf {
                lb_inf
            } else {
                nb_target
            }
        } else {
            nb_target
        };
        if let Some(ref ub) = nb_info.upper {
            let ub_inf = ub.as_inf(BoundType::Upper);
            if clamped > ub_inf {
                ub_inf
            } else {
                clamped
            }
        } else {
            clamped
        }
    }
    /// Update a non-basic variable's value and propagate to basic variables.
    /// Uses column index when available for O(nnz) instead of O(rows) (#4919 Phase 1).
    /// After value propagation, updates the infeasible heap for affected basic vars
    /// (#4919 Phase B).
    ///
    /// #8406: Monomorphic i64 fast path. When the coefficient is `Small(n, d)`,
    /// uses `add_assign_mul_i64` which computes the product in pure i128
    /// arithmetic, bypassing Rational enum matching overhead.
    pub(crate) fn update_nonbasic(&mut self, var: u32, new_val: InfRational) {
        let delta = &new_val - &self.vars[var as usize].value;
        if delta.is_zero() {
            return;
        }
        // #inc-guard-memo: values are about to change (this var + every basic
        // var in its column) — the guard's clean memo no longer holds. This is
        // the single value-mutation chokepoint for simplex/assert paths.
        self.guard_clean_valid = false;
        // #warm-simplex: first-write-wins log of the pre-change values (this
        // var + every basic var in its column, below) so the last-feasible
        // assignment can be restored on conflict. No-op unless the flag is on
        // and the delta log is armed (`warm_log_value` checks `delta_valid`).
        let warm_log = self.warm.enabled && self.warm.delta_valid;
        if warm_log {
            self.warm_log_value(var);
        }
        self.vars[var as usize].value = new_val;
        let vi = var as usize;
        // #8471: the fallback below exists for the case where no column index has been
        // built at all. When the index IS populated it lists every row containing a
        // var (rows index all their coefficients on creation, atom_assertion.rs:128-134,
        // resizing as needed), so an absent/empty entry means `var` occurs in no row and
        // the all-rows scan provably finds nothing. `pivot` already takes exactly this
        // view (its `else if use_col_index { Vec::new() }` arm, "column index exists but
        // entering_var has no entry — no rows affected"); `update_nonbasic` instead used
        // a per-column emptiness test and fell into an O(rows x width) scan plus a Vec
        // allocation on every value write to a row-free variable.
        let col_index_populated = !self.col_index.is_empty();
        if vi < self.col_index.len() && !self.col_index[vi].is_empty() {
            // Use column index: only visit rows containing `var`.
            let n = self.col_index[vi].len();
            for idx in 0..n {
                let entry = self.col_index[vi][idx];
                // O(1) coefficient access via cached row_pos (#8066).
                let coeff = if entry.row_pos < self.rows[entry.row_idx].coeffs.len()
                    && self.rows[entry.row_idx].coeffs[entry.row_pos].0 == var
                {
                    &self.rows[entry.row_idx].coeffs[entry.row_pos].1
                } else {
                    match self.rows[entry.row_idx].coeff_ref(var) {
                        Some(c) => c,
                        None => continue,
                    }
                };
                if coeff.is_zero() {
                    continue;
                }
                let basic_var = self.rows[entry.row_idx].basic_var;
                // #8406: i64 fast path — pure i128 multiply-add when Small.
                if let Rational::Small(cn, cd) = coeff {
                    let (cn, cd) = (*cn, *cd);
                    if warm_log {
                        self.warm_log_value(basic_var);
                    }
                    self.vars[basic_var as usize]
                        .value
                        .add_assign_mul_i64(&delta, cn, cd);
                } else {
                    let adj = delta.mul_rat(coeff);
                    if warm_log {
                        self.warm_log_value(basic_var);
                    }
                    self.vars[basic_var as usize].value += &adj;
                }
                self.track_var_feasibility(basic_var);
            }
        } else if col_index_populated {
            // #8471: index populated but `var` is in no row — nothing to propagate.
            // Behaviour-identical to running the scan below, which would match no row.
            // This is the ONLY branch that acts on "col_index[var] empty => var in no
            // row", and the only other check of that invariant,
            // `debug_assert_col_index_consistency` (simplex/debug.rs), runs from exactly
            // one place — after a pivot (gated on `use_col_index`). A solver that repairs
            // by non-basic snapping never pivots and would never check it. So assert at
            // the point of use, size-bounded so the scan cannot re-impose on large debug
            // runs the cost this edit removes.
            debug_assert!(
                self.rows.len() > 256 || !self.rows.iter().any(|row| row.coeff_ref(var).is_some()),
                "BUG: col_index[{var}] empty but a row still carries the variable"
            );
        } else {
            // Fallback: scan all rows (no column index has been built).
            let updates: Vec<(u32, InfRational)> = self
                .rows
                .iter()
                .filter_map(|row| {
                    let coeff = row.coeff_ref(var)?;
                    // #8406: i64 fast path for row scan.
                    if let Rational::Small(cn, cd) = coeff {
                        Some((row.basic_var, delta.mul_rat_i64(*cn, *cd)))
                    } else {
                        Some((row.basic_var, delta.mul_rat(coeff)))
                    }
                })
                .collect();
            for &(basic_var, ref adj) in &updates {
                if warm_log {
                    self.warm_log_value(basic_var);
                }
                self.vars[basic_var as usize].value += adj;
            }
            for &(basic_var, _) in &updates {
                self.track_var_feasibility(basic_var);
            }
        }
        // #warm-simplex: keep the non-basic candidate-set invariant — an
        // update that leaves its target violated (possible only when the
        // var's feasible interval is empty and the caller snapped it to one
        // of two contradictory bounds) must stay discoverable without the
        // O(vars) scan.
        if self.warm.enabled
            && matches!(self.vars[vi].status, Some(VarStatus::NonBasic))
            && self.violates_bounds(var).is_some()
        {
            self.warm_mark_nonbasic_dirty(var);
        }
    }

    pub(super) fn choose_nonbasic_fix_value(
        info: &VarInfo,
        violated_type: BoundType,
    ) -> Option<InfRational> {
        match violated_type {
            BoundType::Lower => Some(info.lower.as_ref()?.as_inf(BoundType::Lower)),
            BoundType::Upper => Some(info.upper.as_ref()?.as_inf(BoundType::Upper)),
        }
    }

    /// Convert a `BigRational` to `Rational64` if it fits, otherwise return `None`.
    pub(crate) fn bigrational_to_rational64(r: &BigRational) -> Option<num_rational::Rational64> {
        use num_traits::ToPrimitive;

        let numer = r.numer().to_i64()?;
        let denom = r.denom().to_i64()?;
        if denom == 0 {
            return None;
        }
        Some(num_rational::Rational64::new(numer, denom))
    }

    /// Convert a `Rational` to `Rational64` if it fits, otherwise return `None`.
    ///
    /// #8406: Fast path for Farkas certificate construction. When the scale is
    /// Small(n, d), extraction is O(1) with no allocation. Falls back to
    /// `bigrational_to_rational64` for Big variants.
    pub(crate) fn rational_to_rational64(r: &Rational) -> Option<num_rational::Rational64> {
        match r {
            Rational::Small(n, d) => {
                if *d == 0 {
                    return None;
                }
                Some(num_rational::Rational64::new(*n, *d))
            }
            Rational::Big(_) => Self::bigrational_to_rational64(&r.to_big()),
        }
    }
}
