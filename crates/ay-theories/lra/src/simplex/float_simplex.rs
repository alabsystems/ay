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
use crate::TableauRow;

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
