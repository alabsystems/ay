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
        self.vars[var as usize].value = new_val;
        let vi = var as usize;
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
                    self.vars[basic_var as usize]
                        .value
                        .add_assign_mul_i64(&delta, *cn, *cd);
                } else {
                    let adj = delta.mul_rat(coeff);
                    self.vars[basic_var as usize].value += &adj;
                }
                self.track_var_feasibility(basic_var);
            }
        } else {
            // Fallback: scan all rows (column index not yet populated).
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
                self.vars[basic_var as usize].value += adj;
            }
            for &(basic_var, _) in &updates {
                self.track_var_feasibility(basic_var);
            }
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
