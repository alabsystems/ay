// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Public interpolation API for `SmtContext`.
//!
//! Exposes the ay-chc interpolation infrastructure through a clean
//! `get_interpolant(a, b) -> InterpolationResult` API for consumers
//! such as CEGAR, PDR, and abstraction-refinement engines.

use super::context::SmtContext;
use crate::interpolation::{interpolating_sat_constraints, InterpolatingSatResult};
use crate::ChcExpr;
use ay_core::kani_compat::DetHashSet as FxHashSet;

/// Result of an interpolation query.
///
/// When `A /\ B` is UNSAT, a Craig interpolant `I` satisfies:
/// - `A |= I` (I is implied by A)
/// - `I /\ B` is UNSAT (I is inconsistent with B)
/// - `I` mentions only variables shared between A and B (locality)
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum InterpolationResult {
    /// `A /\ B` is UNSAT and a valid Craig interpolant was found.
    ///
    /// The interpolant satisfies all three Craig properties:
    /// implication by A, inconsistency with B, and shared-variable locality.
    Unsat(ChcExpr),

    /// No interpolant could be computed.
    ///
    /// This may occur because:
    /// - `A /\ B` is actually satisfiable
    /// - The constraint forms are outside the scope of available strategies
    /// - Interpolant candidates failed Craig property validation
    ///
    /// This is not an error -- the caller should fall back to other methods.
    Unknown,
}

impl SmtContext {
    /// Compute a Craig interpolant from two sets of constraints.
    ///
    /// Given constraint sets A and B where `A /\ B` is UNSAT, computes an
    /// interpolant `I` such that:
    /// - `A |= I` (I is implied by A)
    /// - `I /\ B` is UNSAT (I blocks B)
    /// - `I` uses only variables shared between A and B
    ///
    /// Uses a cascade of 7 interpolation strategies:
    /// 1. Farkas lemma (linear arithmetic)
    /// 2. Bound analysis (simple variable bounds)
    /// 3. Transitivity (difference constraints)
    /// 4. ITE-normalized Farkas (case-splitting on ITE conditions)
    /// 5. Dual MBP (model-based projection for mixed Bool+LIA)
    /// 6. UNSAT core extraction (fallback)
    /// 7. Disjunction splitting (recursive case analysis)
    ///
    /// # Arguments
    ///
    /// * `a_assertions` - The A-partition constraints (e.g., transition relation)
    /// * `b_assertions` - The B-partition constraints (e.g., bad states)
    ///
    /// # Returns
    ///
    /// [`InterpolationResult::Unsat`] with the interpolant if A /\ B is UNSAT
    /// and an interpolant was found, or [`InterpolationResult::Unknown`] if no
    /// interpolant could be computed.
    ///
    /// # Example
    ///
    /// ```ignore
    /// use ay_chc::{SmtContext, ChcExpr, ChcVar, ChcSort, InterpolationResult};
    ///
    /// let mut smt = SmtContext::new();
    ///
    /// let x = ChcVar::new("x", ChcSort::Int);
    /// let a = vec![ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::Int(10))];
    /// let b = vec![ChcExpr::le(ChcExpr::var(x), ChcExpr::Int(5))];
    ///
    /// match smt.get_interpolant(&a, &b) {
    ///     InterpolationResult::Unsat(interpolant) => {
    ///         // interpolant is valid: A |= I and I /\ B is UNSAT
    ///         let _ = interpolant;
    ///     }
    ///     InterpolationResult::Unknown => {
    ///         // No interpolant found; fall back to other methods
    ///     }
    ///     _ => {}
    /// }
    /// ```
    pub fn get_interpolant(
        &mut self,
        a_assertions: &[ChcExpr],
        b_assertions: &[ChcExpr],
    ) -> InterpolationResult {
        // Compute the set of shared variables between A and B
        let a_vars: FxHashSet<String> = a_assertions
            .iter()
            .flat_map(|e| e.vars().into_iter().map(|v| v.name))
            .collect();
        let b_vars: FxHashSet<String> = b_assertions
            .iter()
            .flat_map(|e| e.vars().into_iter().map(|v| v.name))
            .collect();
        let shared_vars: FxHashSet<String> = a_vars.intersection(&b_vars).cloned().collect();

        match interpolating_sat_constraints(a_assertions, b_assertions, &shared_vars) {
            InterpolatingSatResult::Unsat(interpolant) => InterpolationResult::Unsat(interpolant),
            InterpolatingSatResult::Unknown => InterpolationResult::Unknown,
        }
    }

    /// Compute a Craig interpolant with explicit shared variables.
    ///
    /// Like [`get_interpolant`](Self::get_interpolant), but the caller provides
    /// the set of shared variables instead of computing them from the constraints.
    /// This is useful when the caller knows the interface variables (e.g., from
    /// a transition system where state variables are the shared interface).
    ///
    /// # Arguments
    ///
    /// * `a_assertions` - The A-partition constraints
    /// * `b_assertions` - The B-partition constraints
    /// * `shared_vars` - Variable names that may appear in the interpolant
    pub fn get_interpolant_with_shared_vars(
        &mut self,
        a_assertions: &[ChcExpr],
        b_assertions: &[ChcExpr],
        shared_vars: &FxHashSet<String>,
    ) -> InterpolationResult {
        match interpolating_sat_constraints(a_assertions, b_assertions, shared_vars) {
            InterpolatingSatResult::Unsat(interpolant) => InterpolationResult::Unsat(interpolant),
            InterpolatingSatResult::Unknown => InterpolationResult::Unknown,
        }
    }
}

#[allow(clippy::unwrap_used, clippy::panic)]
#[cfg(test)]
#[path = "interpolation_api_tests.rs"]
mod tests;
