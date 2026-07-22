// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Conjunctive Variable Projection (CVP)
//!
//! CVP extracts a conjunction of literals from a formula that:
//! 1. Is satisfied by the model
//! 2. Implies the original formula (under existential projection of eliminated vars)
//! 3. Only mentions specified variables
//!
//! Used in TRL for generating blocking clauses.
//!
//! # Algorithm
//!
//! 1. **SIP (Syntactic Implicant Projection)**: Extract literals from formula
//!    that are true under model
//! 2. **Disequality refinement**: Convert `x != c` to `x < c` or `x > c` based
//!    on which is true under model
//! 3. **Variable filtering**: Keep only literals mentioning specified variables
//!
//! # Properties (from TRL paper Definition 2)
//!
//! - σ |= cvp(τ, σ, X) — Model satisfies result
//! - cvp(τ, σ, X) |= ∃(V(τ)\X).τ — Result implies existentially projected formula
//! - {cvp(τ, θ, X) | θ |= τ} is finite — Finite distinct outputs
//! - V(cvp(τ, σ, X)) ⊆ X ∩ V(τ) — Only requested variables
//! - cvp(τ, σ, X) ∈ conjunctions only — Always a cube
//!
//! Note: After variable filtering, CVP does NOT directly imply the original formula τ.
//! The implication holds only under existential projection of eliminated variables.
//!
//! # References
//!
//! - LoAT `syntacticImplicant()`: `reference/loat-src/src/lib/expr/model.cpp:61-120`
//! - LoAT `specialize()`: `reference/loat-src/src/trputil.cpp:212-226`
//! - TRL paper: `papers/CADE2025-Infinite-State-Model-Checking-by-Learning-Transitive-Relations.pdf`

use crate::mbp::{Literal, Mbp};
use crate::{ChcExpr, ChcOp, ChcVar, SmtValue};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};

/// Conjunctive Variable Projection
///
/// Given a formula φ, model M, and variables X to keep:
/// - Returns a conjunction ψ such that:
///   1. M |= ψ (model satisfies result)
///   2. ψ |= ∃(V(φ)\X).φ (result implies existentially projected formula)
///   3. vars(ψ) ⊆ X ∩ vars(φ) (only specified variables)
///   4. ψ is a conjunction of literals (cube form)
///
/// # Panics
///
/// Does not panic. Returns `ChcExpr::Bool(true)` if no literals match.
///
/// # Example
///
/// ```text
/// Formula: x > 0 AND y < 10
/// Model: {x: 5, y: 3}
/// vars_to_keep: {x}
/// Result: x > 0 (y < 10 filtered out)
/// ```
///
/// REQUIRES: M |= φ (model satisfies formula)
pub(crate) fn cvp(
    formula: &ChcExpr,
    model: &FxHashMap<String, SmtValue>,
    vars_to_keep: &FxHashSet<ChcVar>,
) -> ChcExpr {
    let mbp = Mbp::new();

    // Step 1: Get syntactic implicant (SIP)
    let implicant = mbp.get_implicant(formula, model);

    // Step 2: Refine disequalities (x != c -> x < c or x > c)
    let refined: Vec<Literal> = implicant
        .into_iter()
        .flat_map(|lit| refine_disequality(lit, &mbp, model))
        .collect();

    // Step 3: Filter to keep only literals mentioning vars_to_keep
    let filtered: Vec<Literal> = refined
        .into_iter()
        .filter(|lit| {
            lit.atom
                .vars()
                .into_iter()
                .any(|v| vars_to_keep.contains(&v))
        })
        .collect();

    // Step 4: Convert back to formula
    mbp.implicant_to_formula(&filtered)
}

/// Syntactic Implicant Projection (SIP)
///
/// Like CVP but without variable filtering. Extracts a conjunction
/// of literals from formula that are true under model.
///
/// This is the base operation - CVP adds variable filtering on top.
///
/// # Example
///
/// ```text
/// Formula: (x > 0 AND y < 10) OR z = 5
/// Model: {x: 3, y: 7, z: 5}
/// Result: x > 0 AND y < 10 (picked satisfied branch)
/// ```
pub(crate) fn sip(formula: &ChcExpr, model: &FxHashMap<String, SmtValue>) -> ChcExpr {
    let mbp = Mbp::new();
    mbp.implicant_cube(formula, model)
}

/// Refine a disequality literal based on model
///
/// Converts `x != c` to either `x < c` or `x > c` based on
/// which inequality is true under the model.
///
/// Reference: LoAT model.cpp:83-95
fn refine_disequality(
    lit: Literal,
    mbp: &Mbp,
    model: &FxHashMap<String, SmtValue>,
) -> Vec<Literal> {
    // Only refine positive atoms
    if !lit.positive {
        return vec![lit];
    }

    match &lit.atom {
        ChcExpr::Op(ChcOp::Ne, args) if args.len() == 2 => {
            let (lhs, rhs) = (&args[0], &args[1]);

            // Try lhs < rhs
            let lt = ChcExpr::lt((**lhs).clone(), (**rhs).clone());
            if mbp.eval_bool(&lt, model) == Some(true) {
                return vec![Literal::new(lt, true)];
            }

            // Try lhs > rhs
            let gt = ChcExpr::gt((**lhs).clone(), (**rhs).clone());
            if mbp.eval_bool(&gt, model) == Some(true) {
                return vec![Literal::new(gt, true)];
            }

            // Couldn't refine, keep as-is
            vec![lit]
        }
        _ => vec![lit],
    }
}

#[allow(clippy::unwrap_used, clippy::panic)]
#[cfg(test)]
mod tests;
