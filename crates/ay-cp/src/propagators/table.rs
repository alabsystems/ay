// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Table constraint propagator.
//!
//! Enforces `(x1, x2, ..., xn) ∈ tuples` where `tuples` is an explicit
//! list of allowed value combinations. This is the extensional (GAC) constraint.
//!
//! # Algorithm
//!
//! Simple tuple-filtering approach:
//! 1. Filter tuples to those consistent with current variable domains
//!    (exact sparse-domain membership, not just interval bounds).
//! 2. For each variable, compute the min and max values across remaining tuples.
//! 3. Tighten bounds accordingly.
//! 4. If no tuples remain → conflict.
//!
//! This is O(|tuples| × arity) per propagation round. For large tables,
//! compact-table or MDD representations would be more efficient, but this
//! simple approach is correct and sufficient for Phase 2.
//!
//! # Explanation
//!
//! When tightening variable x_i's bound, the explanation consists of all
//! other variables' current bounds (which eliminated the tuples that would
//! have supported the old bound for x_i).
//!
//! # References
//!
//! - Gent, Jefferson, Miguel. "Watched Literals for Constraint Propagation in MiniZinc" (CP 2006)
//! - Demeulenaere et al. "Compact-Table: Efficiently Filtering Table Constraints with Reversible Sparse Bit-Sets" (CP 2016)
//! - OR-Tools CP-SAT: `ortools/sat/table.h`
//! - Chuffed: `chuffed/globals/table.c`

use crate::encoder::IntegerEncoder;
use crate::propagator::{Explanation, PropagationResult, Propagator, PropagatorPriority};
use crate::trail::IntegerTrail;
use crate::variable::IntVarId;

/// Table constraint propagator: `(vars[0], vars[1], ...) ∈ tuples`.
///
/// Each tuple is a vector of values, one per variable. A tuple is
/// "supported" if every value is present in the corresponding variable's
/// current domain (exact sparse-domain membership).
#[derive(Debug)]
pub struct Table {
    /// The constrained variables
    vars: Vec<IntVarId>,
    /// Allowed tuples (each tuple has one value per variable)
    tuples: Vec<Vec<i64>>,
    /// Pre-allocated workspace: indices of supported tuples (cleared each call).
    ws_supported: Vec<usize>,
}

impl Table {
    /// Create a new table constraint propagator.
    pub fn new(vars: Vec<IntVarId>, tuples: Vec<Vec<i64>>) -> Self {
        assert!(
            !vars.is_empty(),
            "table constraint needs at least 1 variable"
        );
        assert!(
            tuples.iter().all(|t| t.len() == vars.len()),
            "all tuples must have same arity as vars"
        );
        let n_tuples = tuples.len();
        Self {
            vars,
            tuples,
            ws_supported: Vec::with_capacity(n_tuples),
        }
    }

    /// Filter tuples to those consistent with current domains.
    ///
    /// Uses exact sparse-domain membership (`trail.contains`) rather than
    /// interval bounds, so interior holes from other propagators (e.g.,
    /// `AllDifferentAc`) correctly eliminate unsupported tuples.
    ///
    /// Results stored in `ws_supported` workspace to avoid per-call allocation.
    fn compute_supported(&mut self, trail: &IntegerTrail) {
        self.ws_supported.clear();
        for t_idx in 0..self.tuples.len() {
            let tuple = &self.tuples[t_idx];
            if self
                .vars
                .iter()
                .zip(tuple.iter())
                .all(|(&var, &val)| trail.contains(var, val))
            {
                self.ws_supported.push(t_idx);
            }
        }
    }

    /// Build explanation reasons from all variables' current bounds and
    /// domain holes (excluding var at `skip_idx`).
    ///
    /// For each variable, includes `[var >= lb]`, `[var <= ub]`, and for each
    /// hole value `w` in `[lb, ub]` where `!trail.contains(var, w)`, includes
    /// `[var >= w+1]` as a reason. The hole literals are necessary for
    /// soundness: `supported_tuples()` uses exact domain membership via
    /// `trail.contains()`, so the explanation must also account for holes,
    /// not just bounds.
    ///
    /// Returns `None` if any required literal lookup fails, indicating the
    /// encoder is missing pre-allocated literals for the current trail bounds.
    /// Callers must handle the `None` case conservatively (#5910, #5986).
    fn build_reasons(
        &self,
        trail: &IntegerTrail,
        encoder: &IntegerEncoder,
        skip_idx: usize,
    ) -> Option<Vec<ay_sat::Literal>> {
        let mut reasons = Vec::new();
        for (j, &var) in self.vars.iter().enumerate() {
            if j == skip_idx {
                continue;
            }
            let lb = trail.lb(var);
            let ub = trail.ub(var);
            reasons.push(encoder.lookup_ge(var, lb)?);
            reasons.push(encoder.lookup_le(var, ub)?);
            // Include domain hole reasons (same pattern as AllDifferentAc).
            for w in lb..=ub {
                if !trail.contains(var, w) {
                    reasons.push(encoder.lookup_ge(var, w + 1)?);
                }
            }
        }
        Some(reasons)
    }
}

impl Propagator for Table {
    fn variables(&self) -> &[IntVarId] {
        &self.vars
    }

    fn priority(&self) -> PropagatorPriority {
        PropagatorPriority::Linear
    }

    fn propagate(&mut self, trail: &IntegerTrail, encoder: &IntegerEncoder) -> PropagationResult {
        self.compute_supported(trail);

        if self.ws_supported.is_empty() {
            // No tuple is consistent — conflict.
            // If explanation is incomplete, skip conflict (#5986).
            if let Some(reasons) = self.build_reasons(trail, encoder, usize::MAX) {
                let expl = Explanation::new(reasons);
                return PropagationResult::Conflict(expl.into_conflict_clause());
            }
            return PropagationResult::NoChange;
        }

        let mut clauses = Vec::new();
        let arity = self.vars.len();

        for i in 0..arity {
            let var = self.vars[i];

            // Compute min and max of variable i across supported tuples
            let mut min_val = i64::MAX;
            let mut max_val = i64::MIN;
            for &t_idx in &self.ws_supported {
                let val = self.tuples[t_idx][i];
                min_val = min_val.min(val);
                max_val = max_val.max(val);
            }

            // Tighten lower bound
            if min_val > trail.lb(var) {
                if let Some(conclusion) = encoder.lookup_ge(var, min_val) {
                    if let Some(reasons) = self.build_reasons(trail, encoder, usize::MAX) {
                        clauses.push(Explanation::new(reasons).into_clause(conclusion));
                    }
                }
            }

            // Tighten upper bound
            if max_val < trail.ub(var) {
                if let Some(conclusion) = encoder.lookup_le(var, max_val) {
                    if let Some(reasons) = self.build_reasons(trail, encoder, usize::MAX) {
                        clauses.push(Explanation::new(reasons).into_clause(conclusion));
                    }
                }
            }
        }

        if clauses.is_empty() {
            PropagationResult::NoChange
        } else {
            PropagationResult::Propagated(clauses)
        }
    }

    fn name(&self) -> &'static str {
        "table"
    }
}

#[cfg(test)]
#[path = "table_tests.rs"]
mod tests;
