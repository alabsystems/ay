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
use num_bigint::{BigInt, Sign};
use num_traits::{ToPrimitive, Zero};

/// An exact integer that keeps the common case allocation-free and promotes
/// to arbitrary precision only if an `i128` accumulation overflows.
#[derive(Debug, Clone)]
pub(super) enum ExactInteger {
    Small(i128),
    Big(BigInt),
}

impl ExactInteger {
    pub(super) fn zero() -> Self {
        Self::Small(0)
    }

    pub(super) fn add_product(&mut self, coeff: i128, value: i64) {
        let Some(product) = coeff.checked_mul(i128::from(value)) else {
            let product = BigInt::from(coeff) * value;
            match self {
                Self::Small(sum) => *self = Self::Big(BigInt::from(*sum) + product),
                Self::Big(sum) => *sum += product,
            }
            return;
        };
        match self {
            Self::Small(sum) => {
                if let Some(next) = sum.checked_add(product) {
                    *sum = next;
                } else {
                    *self = Self::Big(BigInt::from(*sum) + product);
                }
            }
            Self::Big(sum) => *sum += product,
        }
    }

    pub(super) fn equals_i128(&self, rhs: i128) -> bool {
        match self {
            Self::Small(value) => *value == rhs,
            Self::Big(value) => value == &BigInt::from(rhs),
        }
    }

    fn greater_than_i128(&self, rhs: i128) -> bool {
        match self {
            Self::Small(value) => *value > rhs,
            Self::Big(value) => value > &BigInt::from(rhs),
        }
    }

    /// Compute `rhs - self + contribution` without losing precision.
    fn slack(&self, rhs: i128, contribution: i128) -> Self {
        match self {
            Self::Small(sum) => rhs
                .checked_sub(*sum)
                .and_then(|value| value.checked_add(contribution))
                .map_or_else(
                    || Self::Big(BigInt::from(rhs) - sum + contribution),
                    Self::Small,
                ),
            Self::Big(sum) => Self::Big(BigInt::from(rhs) - sum + contribution),
        }
    }

    /// Compute `lhs - self` without losing precision.
    pub(super) fn subtract_from(&self, lhs: i128) -> Self {
        match self {
            Self::Small(value) => lhs
                .checked_sub(*value)
                .map_or_else(|| Self::Big(BigInt::from(lhs) - value), Self::Small),
            Self::Big(value) => Self::Big(BigInt::from(lhs) - value),
        }
    }

    /// Return the exact quotient when divisible and representable as i64.
    pub(super) fn exact_quotient_i64(&self, divisor: i128) -> Option<i64> {
        if divisor == 0 {
            return None;
        }
        match self {
            Self::Small(value) => {
                if value.checked_rem(divisor)? != 0 {
                    return None;
                }
                value.checked_div(divisor)?.try_into().ok()
            }
            Self::Big(value) => {
                let divisor = BigInt::from(divisor);
                if (value % &divisor).is_zero() {
                    (value / divisor).to_i64()
                } else {
                    None
                }
            }
        }
    }

    /// Divide a linear slack by its coefficient with the inequality's
    /// required rounding, then clamp to the representable variable range.
    fn linear_bound(&self, coeff: i128) -> i64 {
        debug_assert_ne!(coeff, 0);
        match self {
            Self::Small(value) => value.checked_div_euclid(coeff).map_or_else(
                || clamp_bigint_to_i64(rounded_linear_div(&BigInt::from(*value), coeff)),
                clamp_i128_to_i64,
            ),
            Self::Big(value) => clamp_bigint_to_i64(rounded_linear_div(value, coeff)),
        }
    }
}

fn clamp_i128_to_i64(value: i128) -> i64 {
    value.clamp(i128::from(i64::MIN), i128::from(i64::MAX)) as i64
}

fn clamp_bigint_to_i64(value: BigInt) -> i64 {
    value.to_i64().unwrap_or_else(|| match value.sign() {
        Sign::Minus => i64::MIN,
        Sign::NoSign | Sign::Plus => i64::MAX,
    })
}

/// Apply the same directed rounding as `i128::div_euclid`, including for the
/// exceptional mathematical quotient `i128::MIN / -1`.
fn rounded_linear_div(value: &BigInt, coeff: i128) -> BigInt {
    debug_assert_ne!(coeff, 0);
    if coeff > 0 {
        floor_div_positive(value, &BigInt::from(coeff))
    } else {
        -floor_div_positive(value, &-BigInt::from(coeff))
    }
}

/// Floor division by a strictly positive divisor. `BigInt` division truncates
/// toward zero, so negative non-integral quotients need one extra decrement.
fn floor_div_positive(value: &BigInt, divisor: &BigInt) -> BigInt {
    debug_assert!(matches!(divisor.sign(), Sign::Plus));
    let quotient = value / divisor;
    let remainder = value % divisor;
    if value.sign() == Sign::Minus && !remainder.is_zero() {
        quotient - 1
    } else {
        quotient
    }
}

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
    coeffs: Vec<i128>,
    /// Variables
    vars: Vec<IntVarId>,
    /// Right-hand side
    rhs: i128,
    /// Pre-allocated workspace: reason literals (one per variable).
    ws_reasons: Vec<Option<ay_sat::Literal>>,
}

impl LinearLe {
    /// Create a new linear inequality propagator.
    pub fn new(coeffs: Vec<i64>, vars: Vec<IntVarId>, rhs: i64) -> Self {
        Self::new_wide(
            coeffs.into_iter().map(i128::from).collect(),
            vars,
            i128::from(rhs),
        )
    }

    /// Construct a constraint after an exact sign reversal in i128.
    pub(crate) fn new_wide(coeffs: Vec<i128>, vars: Vec<IntVarId>, rhs: i128) -> Self {
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
    fn compute_sum_min(&self, trail: &IntegerTrail) -> ExactInteger {
        let mut sum_min = ExactInteger::zero();
        for (&coeff, &var) in self.coeffs.iter().zip(&self.vars) {
            let value = if coeff > 0 {
                trail.lb(var)
            } else {
                trail.ub(var)
            };
            sum_min.add_product(coeff, value);
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
        sum_min: &ExactInteger,
        trail: &IntegerTrail,
        encoder: &IntegerEncoder,
    ) -> Option<Vec<ay_sat::Literal>> {
        let var = self.vars[i];
        let coeff = self.coeffs[i];

        let my_contrib = if coeff > 0 {
            coeff * i128::from(trail.lb(var))
        } else {
            coeff * i128::from(trail.ub(var))
        };

        let slack = sum_min.slack(self.rhs, my_contrib);

        if coeff > 0 {
            let new_ub = slack.linear_bound(coeff);
            if new_ub < trail.ub(var) {
                if let Some(conclusion) = encoder.lookup_le(var, new_ub) {
                    return Some(Self::clause_from_reasons(&self.ws_reasons, i, conclusion));
                }
            }
        } else {
            let new_lb = slack.linear_bound(coeff);
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

        if sum_min.greater_than_i128(self.rhs) {
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
            if let Some(clause) = self.derive_bound(i, &sum_min, trail, encoder) {
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
