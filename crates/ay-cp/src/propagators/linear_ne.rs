// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Linear not-equal propagator.
//!
//! Propagates for constraints of the form:
//!   `a1*x1 + a2*x2 + ... + an*xn != rhs`
//!
//! # Algorithm (from Pumpkin/Chuffed)
//!
//! Only propagates when exactly one variable remains unfixed:
//! 1. Count fixed variables (lb == ub), accumulate their weighted sum.
//! 2. When n-1 are fixed: compute the single forbidden value for the
//!    remaining variable and emit a blocking clause excluding it.
//! 3. When all n are fixed: check if sum == rhs → conflict.
//! 4. Otherwise: no propagation (inherent to `!=`).
//!
//! # Explanation (order-encoding clauses)
//!
//! For each fixed variable x_i = v_i, the reason is the pair:
//!   `[x_i >= v_i] ∧ [x_i <= v_i]`  (i.e., x_i is pinned to v_i)
//!
//! The blocking clause negates these reasons and adds the conclusion
//! `x_k != forbidden`:
//!   `¬[x_1>=v_1] ∨ [x_1>=v_1+1] ∨ ... ∨ ¬[x_k>=f] ∨ [x_k>=f+1]`
//!
//! # Reference
//!
//! - Pumpkin: `propagators/arithmetic/linear_not_equal.rs`
//! - Chuffed: `primitives/linear.cpp:189-311`

use crate::encoder::IntegerEncoder;
use crate::propagator::{PropagationResult, Propagator, PropagatorPriority};
use crate::trail::IntegerTrail;
use crate::variable::IntVarId;

/// Linear not-equal propagator: `sum(coeffs[i] * vars[i]) != rhs`.
#[derive(Debug)]
pub struct LinearNotEqual {
    coeffs: Vec<i64>,
    vars: Vec<IntVarId>,
    rhs: i64,
}

impl LinearNotEqual {
    pub fn new(coeffs: Vec<i64>, vars: Vec<IntVarId>, rhs: i64) -> Self {
        assert_eq!(coeffs.len(), vars.len());
        Self { coeffs, vars, rhs }
    }
}

impl Propagator for LinearNotEqual {
    fn variables(&self) -> &[IntVarId] {
        &self.vars
    }

    fn priority(&self) -> PropagatorPriority {
        PropagatorPriority::Binary
    }

    fn propagate(&mut self, trail: &IntegerTrail, encoder: &IntegerEncoder) -> PropagationResult {
        let n = self.vars.len();
        let mut num_fixed: usize = 0;
        let mut partial_sum: i64 = 0;
        let mut unfixed_idx: usize = 0;

        for i in 0..n {
            if trail.is_fixed(self.vars[i]) {
                num_fixed += 1;
                partial_sum = partial_sum
                    .saturating_add(self.coeffs[i].saturating_mul(trail.lb(self.vars[i])));
            } else {
                unfixed_idx = i;
            }
        }

        if num_fixed < n.saturating_sub(1) {
            // Fewer than n-1 fixed: no propagation possible for !=
            return PropagationResult::NoChange;
        }

        if num_fixed == n {
            // All fixed: check if constraint is violated
            if partial_sum == self.rhs {
                // Conflict: build clause from all fixed-var reasons
                let clause = self.build_conflict_clause(trail, encoder);
                return match clause {
                    Some(c) => PropagationResult::Conflict(c),
                    None => PropagationResult::NoChange,
                };
            }
            return PropagationResult::NoChange;
        }

        // Exactly n-1 fixed, one unfixed at unfixed_idx
        let c_k = self.coeffs[unfixed_idx];
        if c_k == 0 {
            // Zero coefficient: this variable is irrelevant
            if partial_sum == self.rhs {
                // Conflict regardless of x_k's value
                let clause = self.build_conflict_clause_excluding(trail, encoder, unfixed_idx);
                return match clause {
                    Some(c) => PropagationResult::Conflict(c),
                    None => PropagationResult::NoChange,
                };
            }
            return PropagationResult::NoChange;
        }

        let remainder = self.rhs.saturating_sub(partial_sum);

        // Check divisibility: if remainder not divisible by c_k,
        // the forbidden value is non-integer → constraint always satisfied
        if remainder % c_k != 0 {
            return PropagationResult::NoChange;
        }

        let forbidden = remainder / c_k;
        let var_k = self.vars[unfixed_idx];

        // Check if forbidden is in domain
        if forbidden < trail.lb(var_k) || forbidden > trail.ub(var_k) {
            return PropagationResult::NoChange;
        }

        // Build blocking clause via helper (returns None if literals missing)
        let clause = self.build_blocking_clause(unfixed_idx, forbidden, trail, encoder);
        match clause {
            Some(c) => PropagationResult::Propagated(vec![c]),
            None => PropagationResult::NoChange,
        }
    }

    fn name(&self) -> &'static str {
        "linear_ne"
    }
}

impl LinearNotEqual {
    /// Build a blocking clause when n-1 vars are fixed and one is unfixed.
    /// Reasons for each fixed var + conclusion excluding the forbidden value.
    fn build_blocking_clause(
        &self,
        unfixed_idx: usize,
        forbidden: i64,
        trail: &IntegerTrail,
        encoder: &IntegerEncoder,
    ) -> Option<Vec<ay_sat::Literal>> {
        let n = self.vars.len();
        let mut clause = Vec::with_capacity(2 * n);

        for i in 0..n {
            if i == unfixed_idx {
                continue;
            }
            let v_i = trail.lb(self.vars[i]);
            let ge_vi = encoder.lookup_ge(self.vars[i], v_i)?;
            let ge_vi1 = encoder.lookup_ge(self.vars[i], v_i + 1)?;
            clause.push(ge_vi.negated());
            clause.push(ge_vi1);
        }

        // Conclusion: x_k != forbidden → ¬[x_k>=f] ∨ [x_k>=f+1]
        let var_k = self.vars[unfixed_idx];
        let ge_f = encoder.lookup_ge(var_k, forbidden)?;
        let ge_f1 = encoder.lookup_ge(var_k, forbidden + 1)?;
        clause.push(ge_f.negated());
        clause.push(ge_f1);

        Some(clause)
    }

    /// Build a conflict clause when all variables are fixed and sum == rhs.
    /// Each fixed var x_i=v_i contributes: ¬[x_i>=v_i] ∨ [x_i>=v_i+1]
    fn build_conflict_clause(
        &self,
        trail: &IntegerTrail,
        encoder: &IntegerEncoder,
    ) -> Option<Vec<ay_sat::Literal>> {
        let n = self.vars.len();
        let mut clause = Vec::with_capacity(2 * n);
        for i in 0..n {
            let v_i = trail.lb(self.vars[i]);
            let ge_vi = encoder.lookup_ge(self.vars[i], v_i)?;
            let ge_vi1 = encoder.lookup_ge(self.vars[i], v_i + 1)?;
            clause.push(ge_vi.negated());
            clause.push(ge_vi1);
        }
        Some(clause)
    }

    /// Build a conflict clause excluding one variable (for zero-coefficient case).
    fn build_conflict_clause_excluding(
        &self,
        trail: &IntegerTrail,
        encoder: &IntegerEncoder,
        exclude: usize,
    ) -> Option<Vec<ay_sat::Literal>> {
        let n = self.vars.len();
        let mut clause = Vec::with_capacity(2 * n);
        for i in 0..n {
            if i == exclude {
                continue;
            }
            let v_i = trail.lb(self.vars[i]);
            let ge_vi = encoder.lookup_ge(self.vars[i], v_i)?;
            let ge_vi1 = encoder.lookup_ge(self.vars[i], v_i + 1)?;
            clause.push(ge_vi.negated());
            clause.push(ge_vi1);
        }
        Some(clause)
    }
}

#[cfg(test)]
#[path = "linear_ne_tests.rs"]
mod tests;
