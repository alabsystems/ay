// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Parity (modular) invariant helpers for PDR solver.
//!
//! This module contains helper functions for parity/modular invariant discovery
//! and verification. The main discovery methods (`discover_parity_invariants`, etc.)
//! remain in `solver.rs` for now as they heavily depend on PdrSolver state.
//!
//! ## Parity Invariants
//!
//! A parity invariant has the form `(var mod k) = c` where:
//! - `k` is the modulus (typically 2, 3, 4, 6, 8, or 16)
//! - `c` is the remainder (0 <= c < k)
//!
//! These invariants capture patterns like:
//! - Even/odd counters: `(counter mod 2) = 0`
//! - Stride patterns: `(idx mod 4) = 0` (aligned access)
//! - Phase tracking: `(phase mod 3) = 1`

use crate::{ChcExpr, ChcOp};
#[cfg(test)]
use crate::{ChcSort, ChcVar};

/// Generate a blocking formula for parity that excludes the OPPOSITE parity of init.
///
/// Given a variable with initial value `init_val`, this generates a blocking formula
/// that excludes states where the variable has the opposite parity (mod 2).
///
/// For example:
/// - init_val=1 (odd) → blocks `(mod var 2) = 0` → establishes "var is odd"
/// - init_val=0 (even) → blocks `(mod var 2) = 1` → establishes "var is even"
///
/// Returns `None` if the variable is not an integer.
/// Returns `Some((blocking_formula, opposite_parity))` if applicable.
///
/// Note: The `val` parameter (current counterexample value) is not used in the
/// blocking formula - what matters is establishing the init parity as an invariant.
#[cfg(test)]
pub(crate) fn parity_mod2_opposite_blocking(
    var: &ChcVar,
    val: i128,
    init_val: i128,
) -> Option<(ChcExpr, i128)> {
    if !matches!(var.sort, ChcSort::Int) {
        return None;
    }

    let init_mod2 = init_val.rem_euclid(2);

    // The blocking formula excludes states with the OPPOSITE parity of init.
    // This produces the lemma: "var has init parity", i.e., NOT (mod var 2) = opposite.
    //
    // The counterexample value is not directly relevant - what matters is that
    // we want to establish "var maintains init parity" as an invariant.
    //
    // E.g., init=1 (odd) -> block (mod var 2) = 0 (even) -> lemma: var is odd
    // E.g., init=0 (even) -> block (mod var 2) = 1 (odd) -> lemma: var is even
    //
    // The caller checks if this blocking is inductive (safe to add as a lemma).
    // If the invariant truly preserves init parity, this will be inductive.
    //
    // #1472 fix: Previously we only generated this when cex had same parity as init.
    // But this pattern should be tried regardless - if the invariant IS "maintains
    // init parity", the inductiveness check will confirm it.
    let _ = val; // val is passed but not needed for the blocking formula
    let opposite_parity = 1 - init_mod2;
    let mod_expr = ChcExpr::mod_op(ChcExpr::var(var.clone()), ChcExpr::int(2));
    Some((
        ChcExpr::eq(mod_expr, ChcExpr::Int(opposite_parity)),
        opposite_parity,
    ))
}

/// Extract a parity constraint from an expression: `(= (mod var k) r)`
///
/// Returns `(var_name, modulus, remainder)` if the expression matches the pattern.
pub(crate) fn extract_parity_constraint(expr: &ChcExpr) -> Option<(String, i128, i128)> {
    if let ChcExpr::Op(ChcOp::Eq, args) = expr {
        if args.len() == 2 {
            // Check (= (mod var k) r) pattern
            if let (ChcExpr::Op(ChcOp::Mod, mod_args), ChcExpr::Int(remainder)) =
                (args[0].as_ref(), args[1].as_ref())
            {
                if mod_args.len() == 2 {
                    if let (ChcExpr::Var(var), ChcExpr::Int(modulus)) =
                        (mod_args[0].as_ref(), mod_args[1].as_ref())
                    {
                        return Some((var.name.clone(), *modulus, *remainder));
                    }
                }
            }
            // Check (= r (mod var k)) pattern
            if let (ChcExpr::Int(remainder), ChcExpr::Op(ChcOp::Mod, mod_args)) =
                (args[0].as_ref(), args[1].as_ref())
            {
                if mod_args.len() == 2 {
                    if let (ChcExpr::Var(var), ChcExpr::Int(modulus)) =
                        (mod_args[0].as_ref(), mod_args[1].as_ref())
                    {
                        return Some((var.name.clone(), *modulus, *remainder));
                    }
                }
            }
        }
    }
    None
}

/// Extract a negated parity constraint: `(not (= (mod var k) r))`
///
/// Returns `(var_name, modulus, remainder)` if the expression matches the pattern.
pub(crate) fn extract_negated_parity_constraint(expr: &ChcExpr) -> Option<(String, i128, i128)> {
    if let ChcExpr::Op(ChcOp::Not, args) = expr {
        if args.len() == 1 {
            return extract_parity_constraint(&args[0]);
        }
    }
    None
}

#[allow(clippy::unwrap_used)]
#[cfg(test)]
#[path = "parity_tests.rs"]
mod tests;
