// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Linear inequality propagator.
//!
//! Propagates bounds for constraints of the form:
//!   `a1*x1 + a2*x2 + ... + an*xn <= rhs`
//!
//! # Algorithm
//!
//! For each variable xi with coefficient ai:
//! - If ai > 0: `xi <= (rhs - sum_min_others) / ai` where sum_min_others uses
//!   lb for positive coefficients, ub for negative coefficients (excluding xi)
//! - If ai < 0: `xi >= (rhs - sum_min_others) / ai` (direction flips)
//!
//! This is O(n) per propagation round.
//!
//! # Explanation
//!
//! When propagating `xi <= v`, the explanation is the conjunction of current
//! bounds on all other variables: `[xj >= lb_j] ∧ [xj <= ub_j] ∧ ... → [xi <= v]`

use crate::encoder::IntegerEncoder;
use crate::propagator::{PropagationResult, Propagator, PropagatorPriority};
use crate::trail::IntegerTrail;
use crate::variable::IntVarId;

/// Linear inequality propagator: `sum(coeffs[i] * vars[i]) <= rhs`.
///
/// Propagation algorithm (from Pumpkin/OR-Tools):
/// 1. Compute `sum_lb = sum(a_i * best_bound(x_i))` where best_bound uses
///    lb for positive coefficients, ub for negative.
/// 2. If `sum_lb > rhs` → conflict.
/// 3. For each variable x_i:
///    - Compute slack excluding x_i: `slack_i = rhs - (sum_lb - a_i * best_bound(x_i))`
///    - If a_i > 0: new upper bound = floor(slack_i / a_i)
///    - If a_i < 0: new lower bound = ceil(slack_i / a_i) (since a_i < 0, direction flips)
#[derive(Debug)]
pub struct LinearLe {
    /// Coefficients
    coeffs: Vec<i64>,
    /// Variables
    vars: Vec<IntVarId>,
    /// Right-hand side
    rhs: i64,
    /// Pre-allocated workspace: reason literals (one per variable).
    ws_reasons: Vec<Option<ay_sat::Literal>>,
}

impl LinearLe {
    /// Create a new linear inequality propagator.
    pub fn new(coeffs: Vec<i64>, vars: Vec<IntVarId>, rhs: i64) -> Self {
        assert_eq!(coeffs.len(), vars.len());
        let n = vars.len();
        Self {
            coeffs,
            vars,
            rhs,
            ws_reasons: vec![None; n],
        }
    }
}

impl LinearLe {
    /// Compute the minimum possible value of `sum(coeffs[i] * vars[i])`.
    fn compute_sum_min(&self, trail: &IntegerTrail) -> i64 {
        let mut sum_min: i64 = 0;
        for (&coeff, &var) in self.coeffs.iter().zip(&self.vars) {
            if coeff > 0 {
                sum_min = sum_min.saturating_add(coeff.saturating_mul(trail.lb(var)));
            } else {
                sum_min = sum_min.saturating_add(coeff.saturating_mul(trail.ub(var)));
            }
        }
        sum_min
    }

    /// Precompute all reason literals for the current trail bounds into
    /// `ws_reasons` workspace. Returns false if any required literal is
    /// missing from the encoder.
    ///
    /// Each entry is `Some(lit)` for non-zero coefficients, `None` for zero.
    /// Precomputing avoids O(n) hash lookups per derived bound (O(n^2) → O(n)).
    fn precompute_reasons(&mut self, trail: &IntegerTrail, encoder: &IntegerEncoder) -> bool {
        for (i, (&coeff, &var)) in self.coeffs.iter().zip(&self.vars).enumerate() {
            if coeff > 0 {
                let lit = encoder.lookup_ge(var, trail.lb(var));
                debug_assert!(
                    lit.is_some(),
                    "BUG: encoder missing [x{} >= {}] (lb) — incomplete explanation \
                     would produce over-strong conflict clause (#5910)",
                    var.0,
                    trail.lb(var),
                );
                match lit {
                    Some(l) => self.ws_reasons[i] = Some(l),
                    None => return false,
                }
            } else if coeff < 0 {
                let lit = encoder.lookup_le(var, trail.ub(var));
                debug_assert!(
                    lit.is_some(),
                    "BUG: encoder missing [x{} <= {}] (ub) — incomplete explanation \
                     would produce over-strong conflict clause (#5910)",
                    var.0,
                    trail.ub(var),
                );
                match lit {
                    Some(l) => self.ws_reasons[i] = Some(l),
                    None => return false,
                }
            } else {
                self.ws_reasons[i] = None;
            }
        }
        true
    }

    /// Build a clause from precomputed reasons, excluding variable at `skip_idx`.
    fn clause_from_reasons(
        all_reasons: &[Option<ay_sat::Literal>],
        skip_idx: usize,
        conclusion: ay_sat::Literal,
    ) -> Vec<ay_sat::Literal> {
        let mut clause = Vec::with_capacity(all_reasons.len());
        clause.push(conclusion);
        for (j, reason) in all_reasons.iter().enumerate() {
            if j == skip_idx {
                continue;
            }
            if let Some(lit) = reason {
                clause.push(lit.negated());
            }
        }
        clause
    }

    /// Derive a tighter bound for variable at index `i` given the minimum sum.
    /// Uses `ws_reasons` workspace (populated by `precompute_reasons`).
    fn derive_bound(
        &self,
        i: usize,
        sum_min: i64,
        trail: &IntegerTrail,
        encoder: &IntegerEncoder,
    ) -> Option<Vec<ay_sat::Literal>> {
        let var = self.vars[i];
        let coeff = self.coeffs[i];

        let my_contrib = if coeff > 0 {
            coeff.saturating_mul(trail.lb(var))
        } else {
            coeff.saturating_mul(trail.ub(var))
        };

        let others_min = sum_min.saturating_sub(my_contrib);
        let slack = self.rhs.saturating_sub(others_min);

        if coeff > 0 {
            let new_ub = if slack >= 0 {
                slack / coeff
            } else {
                (slack - coeff + 1) / coeff
            };
            if new_ub < trail.ub(var) {
                if let Some(conclusion) = encoder.lookup_le(var, new_ub) {
                    return Some(Self::clause_from_reasons(&self.ws_reasons, i, conclusion));
                }
            }
        } else {
            let abs_coeff = -coeff;
            let new_lb = if slack <= 0 {
                (-slack + abs_coeff - 1) / abs_coeff
            } else {
                -(slack / abs_coeff)
            };
            if new_lb > trail.lb(var) {
                if let Some(conclusion) = encoder.lookup_ge(var, new_lb) {
                    return Some(Self::clause_from_reasons(&self.ws_reasons, i, conclusion));
                }
            }
        }
        None
    }
}

impl Propagator for LinearLe {
    fn variables(&self) -> &[IntVarId] {
        &self.vars
    }

    fn priority(&self) -> PropagatorPriority {
        PropagatorPriority::Linear
    }

    fn propagate(&mut self, trail: &IntegerTrail, encoder: &IntegerEncoder) -> PropagationResult {
        let sum_min = self.compute_sum_min(trail);

        // Precompute all reason literals once into ws_reasons — O(n) lookups
        // total instead of O(n) per derived bound (O(n^2) → O(n)).
        if !self.precompute_reasons(trail, encoder) {
            // Explanation incomplete — cannot safely produce clauses.
            // The SAT solver will discover any conflict via BCP instead.
            return PropagationResult::NoChange;
        }

        if sum_min > self.rhs {
            // Conflict: all variables at their best bounds already exceed rhs.
            // Build conflict clause from all reason literals.
            let clause: Vec<_> = self
                .ws_reasons
                .iter()
                .filter_map(|opt| opt.map(ay_sat::Literal::negated))
                .collect();
            return PropagationResult::Conflict(clause);
        }

        let mut clauses = Vec::new();
        for i in 0..self.vars.len() {
            if self.coeffs[i] == 0 {
                continue;
            }
            if let Some(clause) = self.derive_bound(i, sum_min, trail, encoder) {
                clauses.push(clause);
            }
        }

        if clauses.is_empty() {
            PropagationResult::NoChange
        } else {
            PropagationResult::Propagated(clauses)
        }
    }

    fn name(&self) -> &'static str {
        "linear_le"
    }
}

#[cfg(test)]
#[path = "linear_tests.rs"]
mod tests;
