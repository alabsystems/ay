// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Speculative f64 simplex with continuous error tracking (Tier 0).
//!
//! Runs the simplex inner loop in IEEE 754 f64 with per-variable error bounds
//! following Higham (2002) running error analysis. Produces three-way decisions:
//! - Feasible: certified by error bounds (gap exceeds accumulated error)
//! - Infeasible: certified by error bounds (violation exceeds accumulated error)
//! - Uncertain: promote to exact arithmetic (Tier 1+)
//!
//! No prior SMT solver has shipped FP-accelerated simplex. Faure et al. (2008)
//! studied it academically; LP solvers (SoPlex/Gleixner) use iterative refinement
//! for non-incremental LP. Z3's LP module contains vestigial artifacts suggesting
//! a double-precision design that was never completed.
//!
//! Reference: papers/ay-lra-precision/ay-lra-precision.tex Section 4
//! Reference: Higham, "Accuracy and Stability of Numerical Algorithms" (2002), Ch. 3

#![allow(dead_code)]

use crate::types::{BoundType, ColEntry};
use crate::{TableauRow, VarInfo};

/// IEEE 754 double-precision unit roundoff: u = 2^{-53}.
#[allow(dead_code)]
const UNIT_ROUNDOFF: f64 = 1.1102230246251565e-16;

/// Safety factor applied to error bounds (2x for compounding).
const ERROR_SAFETY_FACTOR: f64 = 2.0;

/// Sliding window size for acceptance-rate monitoring.
const ACCEPTANCE_WINDOW_SIZE: u32 = 1000;

/// Minimum acceptance rate. Below this, Tier 0 is disabled.
const ACCEPTANCE_RATE_THRESHOLD: f64 = 0.50;

/// Three-way decision from speculative f64 feasibility check.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum FloatDecision {
    Feasible,
    Infeasible(BoundType),
    Uncertain,
}

/// Speculative f64 simplex shadow state with Higham error tracking.
pub(crate) struct FloatSimplex {
    values: Vec<f64>,
    errors: Vec<f64>,
    disabled: bool,
    ops_attempted: u32,
    ops_accepted: u32,
}

impl FloatSimplex {
    pub(crate) fn new() -> Self {
        Self {
            values: Vec::new(),
            errors: Vec::new(),
            disabled: false,
            ops_attempted: 0,
            ops_accepted: 0,
        }
    }

    #[inline]
    pub(crate) fn is_active(&self) -> bool {
        !self.disabled
    }

    pub(crate) fn sync_from_exact(&mut self, var_count: usize, approx_values: &[f64]) {
        self.values.clear();
        self.errors.clear();
        self.values.extend_from_slice(&approx_values[..var_count]);
        self.errors.resize(var_count, 0.0);
    }

    #[allow(dead_code)]
    pub(crate) fn reset_errors(&mut self) {
        for e in self.errors.iter_mut() {
            *e = 0.0;
        }
    }

    pub(crate) fn check_feasibility(
        &mut self,
        var: u32,
        lower_f64: Option<f64>,
        upper_f64: Option<f64>,
    ) -> FloatDecision {
        if self.disabled {
            return FloatDecision::Uncertain;
        }
        let vi = var as usize;
        if vi >= self.values.len() {
            return FloatDecision::Uncertain;
        }
        let val = self.values[vi];
        let eps = self.errors[vi] * ERROR_SAFETY_FACTOR;
        if !eps.is_finite() || !val.is_finite() {
            self.record_decision(false);
            return FloatDecision::Uncertain;
        }
        if let Some(lb) = lower_f64 {
            if !lb.is_finite() {
                self.record_decision(false);
                return FloatDecision::Uncertain;
            }
            if val + eps < lb {
                self.record_decision(true);
                return FloatDecision::Infeasible(BoundType::Lower);
            }
            if val - eps < lb {
                self.record_decision(false);
                return FloatDecision::Uncertain;
            }
        }
        if let Some(ub) = upper_f64 {
            if !ub.is_finite() {
                self.record_decision(false);
                return FloatDecision::Uncertain;
            }
            if val - eps > ub {
                self.record_decision(true);
                return FloatDecision::Infeasible(BoundType::Upper);
            }
            if val + eps > ub {
                self.record_decision(false);
                return FloatDecision::Uncertain;
            }
        }
        self.record_decision(true);
        FloatDecision::Feasible
    }

    #[allow(dead_code)]
    pub(crate) fn update_nonbasic_f64(
        &mut self,
        var: u32,
        new_val_f64: f64,
        rows: &[TableauRow],
        col_index: &[Vec<ColEntry>],
    ) {
        let vi = var as usize;
        if vi >= self.values.len() || self.disabled {
            return;
        }
        let old_val = self.values[vi];
        let delta = new_val_f64 - old_val;
        if delta == 0.0 {
            return;
        }
        self.values[vi] = new_val_f64;
        self.errors[vi] += old_val.abs() * UNIT_ROUNDOFF;

        if vi < col_index.len() && !col_index[vi].is_empty() {
            let n = col_index[vi].len();
            for &entry in col_index[vi].iter().take(n) {
                if entry.row_idx >= rows.len() {
                    continue;
                }
                let coeff_f64 = if entry.row_pos < rows[entry.row_idx].coeffs.len()
                    && rows[entry.row_idx].coeffs[entry.row_pos].0 == var
                {
                    rows[entry.row_idx].coeffs[entry.row_pos].1.approx_f64()
                } else {
                    match rows[entry.row_idx].coeff_ref(var) {
                        Some(c) => c.approx_f64(),
                        None => continue,
                    }
                };
                if coeff_f64 == 0.0 {
                    continue;
                }
                let basic_var = rows[entry.row_idx].basic_var as usize;
                if basic_var >= self.values.len() {
                    continue;
                }
                let product = delta * coeff_f64;
                self.values[basic_var] += product;
                self.errors[basic_var] +=
                    (product.abs() + self.values[basic_var].abs()) * UNIT_ROUNDOFF;
            }
        } else {
            for row in rows {
                let coeff_f64 = match row.coeff_ref(var) {
                    Some(c) => c.approx_f64(),
                    None => continue,
                };
                if coeff_f64 == 0.0 {
                    continue;
                }
                let basic_var = row.basic_var as usize;
                if basic_var >= self.values.len() {
                    continue;
                }
                let product = delta * coeff_f64;
                self.values[basic_var] += product;
                self.errors[basic_var] +=
                    (product.abs() + self.values[basic_var].abs()) * UNIT_ROUNDOFF;
            }
        }
    }

    pub(crate) fn speculative_all_feasible(
        &mut self,
        var_count: usize,
        lower_f64: impl Fn(usize) -> Option<f64>,
        upper_f64: impl Fn(usize) -> Option<f64>,
    ) -> Option<FloatDecision> {
        if self.disabled {
            return None;
        }
        for vi in 0..var_count.min(self.values.len()) {
            let decision = self.check_feasibility(vi as u32, lower_f64(vi), upper_f64(vi));
            match decision {
                FloatDecision::Feasible => continue,
                FloatDecision::Infeasible(_) => return Some(decision),
                FloatDecision::Uncertain => return None,
            }
        }
        Some(FloatDecision::Feasible)
    }

    pub(crate) fn find_greatest_violation(
        &mut self,
        var_count: usize,
        lower_f64: impl Fn(usize) -> Option<f64>,
        upper_f64: impl Fn(usize) -> Option<f64>,
    ) -> Option<(u32, BoundType)> {
        if self.disabled {
            return None;
        }
        let mut best: Option<(u32, BoundType, f64)> = None;
        for vi in 0..var_count.min(self.values.len()) {
            let val = self.values[vi];
            let eps = self.errors[vi] * ERROR_SAFETY_FACTOR;
            if !val.is_finite() || !eps.is_finite() {
                continue;
            }
            if let Some(lb) = lower_f64(vi) {
                if lb.is_finite() && val + eps < lb {
                    let violation = lb - val;
                    if best.as_ref().is_none_or(|(_, _, v)| violation > *v) {
                        best = Some((vi as u32, BoundType::Lower, violation));
                    }
                }
            }
            if let Some(ub) = upper_f64(vi) {
                if ub.is_finite() && val - eps > ub {
                    let violation = val - ub;
                    if best.as_ref().is_none_or(|(_, _, v)| violation > *v) {
                        best = Some((vi as u32, BoundType::Upper, violation));
                    }
                }
            }
        }
        best.map(|(var, bt, _)| (var, bt))
    }

    fn record_decision(&mut self, accepted: bool) {
        self.ops_attempted += 1;
        if accepted {
            self.ops_accepted += 1;
        }
        if self.ops_attempted >= ACCEPTANCE_WINDOW_SIZE {
            let rate = f64::from(self.ops_accepted) / f64::from(self.ops_attempted);
            if rate < ACCEPTANCE_RATE_THRESHOLD {
                self.disabled = true;
            }
            self.ops_attempted = 0;
            self.ops_accepted = 0;
        }
    }

    pub(crate) fn stats(&self) -> (u32, u32, bool) {
        (self.ops_attempted, self.ops_accepted, self.disabled)
    }
}

// ===========================================================================
// Float pivot layer (AY_LRA_FLOAT_LAYER) — heuristic f64 basis oracle.
//
// `float_find_basis` runs a REAL f64 dual-simplex-style feasibility search over
// a shadow copy of the current reduced tableau and returns a CANDIDATE basis
// `B*` plus, for every non-basic variable, which bound it rests at. It emits NO
// verdict: the exact certification path (`simplex::float_layer`) independently
// re-checks the resulting assignment against every tableau row equation and
// every bound in exact arithmetic before any Sat is returned. The search is
// therefore free to be approximate, non-terminating-in-theory (it is hard
// iteration-capped), or simply wrong — the worst outcome is a fallback to the
// exact simplex, never an unsound answer.
// ===========================================================================

/// Where a non-basic variable rests in the candidate basis.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum NbPos {
    /// At its lower bound (exact value = `lower.as_inf(Lower)`, +eps if strict).
    Lower,
    /// At its upper bound (exact value = `upper.as_inf(Upper)`, -eps if strict).
    Upper,
    /// Free (no active bound used): exact value = 0.
    Free,
}

/// A candidate basis proposed by the f64 shadow simplex.
pub(crate) struct FloatBasis {
    /// One entry per tableau row: the variable that is basic in that row.
    pub(crate) basic: Vec<u32>,
    /// Indexed by variable id: true iff the variable is basic in `B*`.
    pub(crate) is_basic: Vec<bool>,
    /// Indexed by variable id: resting bound for non-basic variables.
    pub(crate) nb_pos: Vec<NbPos>,
}

/// The terminal reached by the f64 shadow search.
///
/// Both variants carry a candidate basis `B*`; the exact certification layer
/// (`simplex::float_layer`) turns each into an EXACTLY-checked verdict:
/// - `Feasible` → candidate SAT basis (exact feasibility certificate), or None.
/// - `Infeasible` → candidate UNSAT witness: the basic var `bstar` violates
///   its bound `violated` with no entering candidate. The exact layer solves
///   `y^T A_{B*} = e_{bstar}` for exact Farkas multipliers, verifies the reduced
///   conflict row is a genuine tableau identity + a genuine bound violation, and
///   only then emits Unsat. Either terminal may be rejected → exact fallback.
pub(crate) enum FloatOutcome {
    Feasible(FloatBasis),
    Infeasible {
        basis: FloatBasis,
        /// The basic variable that violates its bound with no entering pivot.
        bstar: u32,
        /// Which of `bstar`'s bounds is violated (Lower = too small).
        violated: BoundType,
    },
}

/// A single f64 shadow tableau row: `basic = constant + Σ coeff·nonbasic`.
struct FRow {
    basic_var: u32,
    coeffs: Vec<(u32, f64)>,
    constant: f64,
}

impl FRow {
    #[inline]
    fn coeff(&self, var: u32) -> f64 {
        match self.coeffs.binary_search_by_key(&var, |(v, _)| *v) {
            Ok(i) => self.coeffs[i].1,
            Err(_) => 0.0,
        }
    }
    #[inline]
    fn remove(&mut self, var: u32) {
        if let Ok(i) = self.coeffs.binary_search_by_key(&var, |(v, _)| *v) {
            self.coeffs.remove(i);
        }
    }
    #[inline]
    fn add(&mut self, var: u32, delta: f64) {
        if delta == 0.0 {
            return;
        }
        match self.coeffs.binary_search_by_key(&var, |(v, _)| *v) {
            Ok(i) => {
                self.coeffs[i].1 += delta;
                if self.coeffs[i].1 == 0.0 {
                    self.coeffs.remove(i);
                }
            }
            Err(i) => self.coeffs.insert(i, (var, delta)),
        }
    }
}

/// Minimum |pivot coefficient| the f64 search will accept, to avoid dividing by
/// a near-zero and blowing up the shadow tableau. A rejected candidate just
/// makes the search give up (→ exact fallback), never a wrong answer.
const MIN_PIVOT_MAG: f64 = 1e-9;

/// Backward-compatible wrapper: return only the FEASIBLE candidate basis (as
/// before Increment 2). Infeasible terminals collapse to `None`. Used by the
/// SAT certification path and existing tests.
///
/// This function is a pure function of the passed-in tableau/vars: it never
/// mutates solver state.
pub(crate) fn float_find_basis(
    rows: &[TableauRow],
    vars: &[VarInfo],
    max_iters: usize,
) -> Option<FloatBasis> {
    match float_solve(rows, vars, max_iters)? {
        FloatOutcome::Feasible(b) => Some(b),
        FloatOutcome::Infeasible { .. } => None,
    }
}

/// Run the f64 shadow dual simplex and return its terminal outcome:
/// - `Some(Feasible(B*))` when no basic var violates its bound;
/// - `Some(Infeasible{..})` when a basic var violates a bound with no entering
///   pivot candidate (a shadow dual-infeasibility proof to be exactly certified);
/// - `None` on a non-finite value, iteration-cap exhaustion, or a non-finite
///   active bound (the search gives up → exact fallback).
///
/// This function is a pure function of the passed-in tableau/vars: it never
/// mutates solver state.
pub(crate) fn float_solve(
    rows: &[TableauRow],
    vars: &[VarInfo],
    max_iters: usize,
) -> Option<FloatOutcome> {
    let n = vars.len();
    let m = rows.len();

    // --- Read finite f64 bounds. Any non-finite active bound disqualifies. ---
    let mut lb: Vec<Option<f64>> = vec![None; n];
    let mut ub: Vec<Option<f64>> = vec![None; n];
    for (v, info) in vars.iter().enumerate() {
        if let Some(b) = &info.lower {
            let f = b.value.approx_f64();
            if !f.is_finite() {
                return None;
            }
            lb[v] = Some(f);
        }
        if let Some(b) = &info.upper {
            let f = b.value.approx_f64();
            if !f.is_finite() {
                return None;
            }
            ub[v] = Some(f);
        }
    }

    // --- Seed the shadow tableau from the current reduced rows. ---
    let mut is_basic = vec![false; n];
    let mut frows: Vec<FRow> = Vec::with_capacity(m);
    for row in rows {
        let bv = row.basic_var as usize;
        if bv >= n {
            return None;
        }
        is_basic[bv] = true;
        let mut coeffs = Vec::with_capacity(row.coeffs.len());
        for (v, c) in &row.coeffs {
            let f = c.approx_f64();
            if !f.is_finite() {
                return None;
            }
            coeffs.push((*v, f));
        }
        let k = row.constant.approx_f64();
        if !k.is_finite() {
            return None;
        }
        frows.push(FRow {
            basic_var: row.basic_var,
            coeffs,
            constant: k,
        });
    }

    // --- Non-basic resting positions and values. ---
    let mut pos = vec![NbPos::Free; n];
    let mut val = vec![0.0f64; n];
    for v in 0..n {
        if is_basic[v] {
            continue;
        }
        if let Some(l) = lb[v] {
            pos[v] = NbPos::Lower;
            val[v] = l;
        } else if let Some(u) = ub[v] {
            pos[v] = NbPos::Upper;
            val[v] = u;
        } else {
            pos[v] = NbPos::Free;
            val[v] = 0.0;
        }
    }
    recompute_basics(&frows, &mut val)?;

    // --- Dual-simplex-style feasibility loop (Bland-ordered, hard capped). ---
    for _ in 0..max_iters {
        // Leaving: smallest-index basic var that violates a bound.
        let mut leaving: Option<(usize, u32, i32, f64)> = None; // (row, var, dir, bound)
        for (ri, fr) in frows.iter().enumerate() {
            let b = fr.basic_var as usize;
            let x = val[b];
            if !x.is_finite() {
                return None;
            }
            let tol = 1e-9 * (1.0 + x.abs());
            if let Some(l) = lb[b] {
                if x < l - tol {
                    if leaving.is_none_or(|(_, cur, _, _)| (b as u32) < cur) {
                        leaving = Some((ri, b as u32, 1, l));
                    }
                    continue;
                }
            }
            if let Some(u) = ub[b] {
                if x > u + tol && leaving.is_none_or(|(_, cur, _, _)| (b as u32) < cur) {
                    leaving = Some((ri, b as u32, -1, u));
                }
            }
        }
        let Some((ri, bvar, dir, bound_val)) = leaving else {
            // No violated basic var → shadow-feasible. Propose this basis.
            let basic: Vec<u32> = frows.iter().map(|r| r.basic_var).collect();
            return Some(FloatOutcome::Feasible(FloatBasis {
                basic,
                is_basic,
                nb_pos: pos,
            }));
        };

        // Entering: smallest-index non-basic in this row that can move `bvar`
        // in direction `dir` and whose |coeff| is not degenerate.
        let mut entering: Option<u32> = None;
        for &(j, a) in &frows[ri].coeffs {
            if a.abs() < MIN_PIVOT_MAG {
                continue;
            }
            let can_inc = pos[j as usize] != NbPos::Upper; // at lower or free
            let can_dec = pos[j as usize] != NbPos::Lower; // at upper or free
            let sign_pos = a > 0.0;
            let dir_pos = dir > 0;
            // δ>0 moves x_b by a·δ (sign = sign(a)); δ<0 by -a (opposite sign).
            let eligible = (sign_pos == dir_pos && can_inc) || (sign_pos != dir_pos && can_dec);
            if eligible {
                entering = Some(j);
                break;
            }
        }
        let Some(j) = entering else {
            // No entering candidate → shadow dual-infeasibility proof: `bvar` is
            // basic and violates its bound, and no non-basic can move to relieve
            // it. Increment 2 certifies this EXACTLY (solve y^T A_{B*}=e_{bvar},
            // check the reduced conflict row is a genuine tableau identity + a
            // genuine bound violation) before emitting Unsat; any mismatch →
            // exact fallback. Surface the witness rather than discarding it.
            let basic: Vec<u32> = frows.iter().map(|r| r.basic_var).collect();
            let violated = if dir > 0 {
                BoundType::Lower
            } else {
                BoundType::Upper
            };
            return Some(FloatOutcome::Infeasible {
                basis: FloatBasis {
                    basic,
                    is_basic,
                    nb_pos: pos,
                },
                bstar: bvar,
                violated,
            });
        };

        pivot_f64(&mut frows, ri, j, bvar, &mut is_basic)?;
        // Leaving var now rests at the bound it violated.
        pos[bvar as usize] = if dir > 0 { NbPos::Lower } else { NbPos::Upper };
        val[bvar as usize] = bound_val;
        recompute_basics(&frows, &mut val)?;
    }
    None
}

/// Recompute every basic variable's value from the current non-basic values.
/// Returns `None` if any value becomes non-finite.
fn recompute_basics(frows: &[FRow], val: &mut [f64]) -> Option<()> {
    for fr in frows {
        let mut acc = fr.constant;
        for &(v, c) in &fr.coeffs {
            acc += c * val[v as usize];
        }
        if !acc.is_finite() {
            return None;
        }
        val[fr.basic_var as usize] = acc;
    }
    Some(())
}

/// Pivot the shadow tableau: `entering` enters the basis in row `ri`, `leaving`
/// leaves. Maintains the reduced-form invariant (rows reference only non-basic
/// variables). Returns `None` on a non-finite result.
fn pivot_f64(
    frows: &mut [FRow],
    ri: usize,
    entering: u32,
    leaving: u32,
    is_basic: &mut [bool],
) -> Option<()> {
    let a = frows[ri].coeff(entering);
    if a.abs() < MIN_PIVOT_MAG {
        return None;
    }
    let inv = 1.0 / a;
    if !inv.is_finite() {
        return None;
    }
    // Row expressing `entering`: x_e = inv·x_leaving - Σ_{k≠e} (c_k·inv)·x_k - const·inv
    let mut newc: Vec<(u32, f64)> = Vec::with_capacity(frows[ri].coeffs.len());
    for &(k, ck) in &frows[ri].coeffs {
        if k == entering {
            continue;
        }
        let c = -ck * inv;
        if c != 0.0 && c.is_finite() {
            newc.push((k, c));
        } else if !c.is_finite() {
            return None;
        }
    }
    newc.push((leaving, inv));
    newc.sort_by_key(|(v, _)| *v);
    let newconst = -frows[ri].constant * inv;
    if !newconst.is_finite() {
        return None;
    }

    // Substitute `entering` out of every other row.
    for (si, row) in frows.iter_mut().enumerate() {
        if si == ri {
            continue;
        }
        let asj = row.coeff(entering);
        if asj == 0.0 {
            continue;
        }
        row.remove(entering);
        for &(k, nc) in &newc {
            row.add(k, asj * nc);
        }
        row.constant += asj * newconst;
        if !row.constant.is_finite() {
            return None;
        }
    }

    frows[ri].basic_var = entering;
    frows[ri].coeffs = newc;
    frows[ri].constant = newconst;
    is_basic[leaving as usize] = false;
    is_basic[entering as usize] = true;
    Some(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_float_simplex_feasible() {
        let mut fs = FloatSimplex::new();
        assert!(fs.is_active());
        fs.sync_from_exact(1, &[5.0]);
        let decision = fs.check_feasibility(0, Some(2.0), Some(8.0));
        assert_eq!(decision, FloatDecision::Feasible);
    }

    #[test]
    fn test_float_simplex_infeasible_lower() {
        let mut fs = FloatSimplex::new();
        fs.sync_from_exact(1, &[1.0]);
        let decision = fs.check_feasibility(0, Some(3.0), Some(10.0));
        assert_eq!(decision, FloatDecision::Infeasible(BoundType::Lower));
    }

    #[test]
    fn test_float_simplex_infeasible_upper() {
        let mut fs = FloatSimplex::new();
        fs.sync_from_exact(1, &[10.0]);
        let decision = fs.check_feasibility(0, Some(0.0), Some(5.0));
        assert_eq!(decision, FloatDecision::Infeasible(BoundType::Upper));
    }

    #[test]
    fn test_float_simplex_uncertain_near_boundary() {
        let mut fs = FloatSimplex::new();
        fs.sync_from_exact(1, &[5.0]);
        fs.errors[0] = 3.0;
        let decision = fs.check_feasibility(0, Some(2.0), Some(8.0));
        assert_eq!(decision, FloatDecision::Uncertain);
    }

    #[test]
    fn test_acceptance_tracking() {
        let mut fs = FloatSimplex::new();
        fs.sync_from_exact(1, &[5.0]);
        fs.errors[0] = 100.0;
        for _ in 0..ACCEPTANCE_WINDOW_SIZE {
            let _ = fs.check_feasibility(0, Some(4.0), Some(6.0));
        }
        assert!(!fs.is_active());
    }

    #[test]
    fn test_disabled_returns_uncertain() {
        let mut fs = FloatSimplex::new();
        fs.disabled = true;
        fs.sync_from_exact(1, &[5.0]);
        let decision = fs.check_feasibility(0, Some(0.0), Some(10.0));
        assert_eq!(decision, FloatDecision::Uncertain);
    }

    #[test]
    fn test_no_bounds_feasible() {
        let mut fs = FloatSimplex::new();
        fs.sync_from_exact(1, &[5.0]);
        let decision = fs.check_feasibility(0, None, None);
        assert_eq!(decision, FloatDecision::Feasible);
    }

    #[test]
    fn test_nan_handling() {
        let mut fs = FloatSimplex::new();
        fs.sync_from_exact(1, &[f64::NAN]);
        let decision = fs.check_feasibility(0, Some(0.0), Some(10.0));
        assert_eq!(decision, FloatDecision::Uncertain);
    }

    #[test]
    fn test_large_error_promotes_to_uncertain() {
        let mut fs = FloatSimplex::new();
        fs.sync_from_exact(1, &[5.0]);
        fs.errors[0] = 1e10;
        let decision = fs.check_feasibility(0, Some(0.0), Some(10.0));
        assert_eq!(decision, FloatDecision::Uncertain);
    }

    #[test]
    fn test_speculative_all_feasible() {
        let mut fs = FloatSimplex::new();
        fs.sync_from_exact(3, &[5.0, 3.0, 7.0]);
        let result = fs.speculative_all_feasible(
            3,
            |vi| if vi < 3 { Some(0.0) } else { None },
            |vi| if vi < 3 { Some(10.0) } else { None },
        );
        assert_eq!(result, Some(FloatDecision::Feasible));
    }

    #[test]
    fn test_speculative_infeasible() {
        let mut fs = FloatSimplex::new();
        fs.sync_from_exact(3, &[5.0, 15.0, 7.0]);
        let result = fs.speculative_all_feasible(
            3,
            |_| Some(0.0),
            |vi| if vi == 1 { Some(10.0) } else { Some(20.0) },
        );
        assert_eq!(result, Some(FloatDecision::Infeasible(BoundType::Upper)));
    }

    #[test]
    fn test_find_greatest_violation() {
        let mut fs = FloatSimplex::new();
        fs.sync_from_exact(3, &[1.0, 20.0, -5.0]);
        let result = fs.find_greatest_violation(3, |_| Some(0.0), |_| Some(10.0));
        assert_eq!(result, Some((1, BoundType::Upper)));
    }

    #[test]
    fn test_stats() {
        let mut fs = FloatSimplex::new();
        fs.sync_from_exact(1, &[5.0]);
        let _ = fs.check_feasibility(0, Some(0.0), Some(10.0));
        let _ = fs.check_feasibility(0, Some(0.0), Some(10.0));
        let (attempted, accepted, disabled) = fs.stats();
        assert_eq!(attempted, 2);
        assert_eq!(accepted, 2);
        assert!(!disabled);
    }
}
