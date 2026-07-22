// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Sample-based divisibility inference for invariant discovery.
//!
//! This module implements Phase 1 of the parity-aware affine synthesis design:
//! discovering modular constraints `(var mod m) = r` from sampled model values.
//!
//! Unlike the existing parity invariant discovery (which requires constant init
//! values), this approach works on sampled data points:
//!
//! 1. Sample N models from fact constraint
//! 2. For each variable, collect its values across all samples
//! 3. Check if all values share a common remainder for moduli 2, 3, 4, 5, 6
//! 4. Verify the modular constraint is preserved by transitions
//! 5. Add as level-1 lemma if inductive
//!
//! ## Reference
//!
//! Port of Z3 Spacer's `infer_div_pred` from `spacer_convex_closure.cpp:254-291`.
//!
//! ## Part of
//!
//! #1615 - CHC regression fix
//! the development design notes

use crate::{ChcExpr, ChcSort, ChcVar};
use ay_core::kani_compat::DetHashMap as FxHashMap;

/// Check if all values share a common remainder when divided by the given divisor.
///
/// Returns `Some(remainder)` if all values have the same `v.rem_euclid(divisor)`,
/// otherwise returns `None`.
///
/// Uses Euclidean remainder (always non-negative) for consistency with SMT semantics.
pub(super) fn infer_divisibility(values: &[i128], divisor: i128) -> Option<i128> {
    if values.is_empty() || divisor <= 0 {
        return None;
    }
    let remainder = values[0].rem_euclid(divisor);
    if values.iter().all(|&v| v.rem_euclid(divisor) == remainder) {
        Some(remainder)
    } else {
        None
    }
}

/// Common moduli to check for divisibility patterns.
///
/// Includes:
/// - 2: Even/odd patterns (most common)
/// - 3, 5: Small primes
/// - 4, 6, 8, 10: Small composites covering common init coefficients
///
/// The extended range (8, 10) catches benchmarks where init expressions
/// use larger coefficients (e.g., `D = 10*A` in s_mutants_21 requires mod 10).
/// False positive risk is low: sampled values must ALL share the same remainder,
/// which is unlikely by chance for larger moduli with diverse samples.
///
/// Note: Order matters for redundancy filtering - smaller moduli first.
const DIVISIBILITY_MODULI: &[i128] = &[2, 3, 4, 5, 6, 8, 10];

/// Extract per-variable values from sampled models for divisibility analysis.
///
/// Given a list of sampled models and integer variables, returns a map from
/// variable name to the collected values across all samples.
pub(crate) fn extract_variable_values(
    models: &[FxHashMap<String, i128>],
    int_vars: &[ChcVar],
) -> FxHashMap<String, Vec<i128>> {
    let mut values_per_var: FxHashMap<String, Vec<i128>> = FxHashMap::default();

    for var in int_vars {
        if !matches!(var.sort, ChcSort::Int) {
            continue;
        }
        let values: Vec<i128> = models
            .iter()
            .filter_map(|m| m.get(&var.name).copied())
            .collect();

        if !values.is_empty() {
            values_per_var.insert(var.name.clone(), values);
        }
    }

    values_per_var
}

/// Discovered divisibility constraint from sampled data.
#[derive(Debug, Clone)]
pub(crate) struct DivisibilityConstraint {
    /// Variable name
    pub var_name: String,
    /// Modulus (e.g., 2 for even/odd)
    pub modulus: i128,
    /// Remainder (e.g., 0 for even, 1 for odd)
    pub remainder: i128,
}

impl DivisibilityConstraint {
    /// Convert to CHC expression: `(= (mod var modulus) remainder)`
    pub(crate) fn to_expr(&self, var: &ChcVar) -> ChcExpr {
        let mod_expr = ChcExpr::mod_op(ChcExpr::var(var.clone()), ChcExpr::Int(self.modulus));
        ChcExpr::eq(mod_expr, ChcExpr::Int(self.remainder))
    }
}

/// Discover divisibility patterns from sampled values.
///
/// For each variable and each modulus in `DIVISIBILITY_MODULI`, checks if
/// all sampled values share a common remainder. Returns all discovered
/// constraints (caller must verify they are preserved by transitions).
///
/// Filters redundant constraints: if `var mod 2 = 0` is found, we skip
/// `var mod 4 = 0` since mod 4 is implied by mod 2 when remainder is 0.
pub(crate) fn discover_divisibility_patterns(
    values_per_var: &FxHashMap<String, Vec<i128>>,
) -> Vec<DivisibilityConstraint> {
    let mut constraints = Vec::new();

    for (var_name, values) in values_per_var {
        // Need at least 2 samples to have any confidence
        if values.len() < 2 {
            continue;
        }

        // Check if all values are the same - skip divisibility check for constants
        // (constant invariants are stronger and should be discovered separately)
        if values.iter().all(|&v| v == values[0]) {
            continue;
        }

        // Track which moduli we've already found for this variable
        // to filter redundant constraints (e.g., mod 4 = 0 when mod 2 = 0 already found)
        let mut found_moduli: Vec<(i128, i128)> = Vec::new();

        for &modulus in DIVISIBILITY_MODULI {
            if let Some(remainder) = infer_divisibility(values, modulus) {
                // Check if this is implied by an already-found smaller modulus
                // `mod(k*m) = r` is implied by `mod(m) = r` when both remainders are equal
                // Example: mod 4 = 0 is implied by mod 2 = 0
                // But: mod 4 = 2 is NOT implied by mod 2 = 0 (gives more info)
                let is_redundant = found_moduli
                    .iter()
                    .any(|&(m, r)| modulus % m == 0 && remainder == r);

                if !is_redundant {
                    found_moduli.push((modulus, remainder));
                    constraints.push(DivisibilityConstraint {
                        var_name: var_name.clone(),
                        modulus,
                        remainder,
                    });
                }
            }
        }
    }

    constraints
}

#[allow(clippy::unwrap_used)]
#[cfg(test)]
#[path = "divisibility_tests.rs"]
mod tests;
