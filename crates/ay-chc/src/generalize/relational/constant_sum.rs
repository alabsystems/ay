// Copyright 2026 Andrew Yates
// Author: Andrew Yates
//
// Licensed under the Apache License, Version 2.0

//! Constant sum generalizer: discovers sum invariants like `x + y = k`.

use crate::expr::{ChcExpr, ChcSort, ChcVar};
use crate::generalize::{LemmaGeneralizer, TransitionSystemRef};

/// Constant sum generalizer: discovers sum invariants like `x + y = k`.
///
/// When state (x=a, y=b) violates a preserved sum invariant from init,
/// this generalizer blocks all states where `x + y != init_sum`.
///
/// # When to Use
///
/// Use this generalizer early in the pipeline (Phase 0) when dealing with
/// programs that transfer quantities between variables. Examples:
/// - Counter transfers: `x_next = x+1, y_next = y-1` preserves `x + y`
/// - Token protocols: `send_next = send+1, recv_next = recv-1`
///
/// # Examples
///
/// If init has (x=0, y=100) and we observe state (x=50, y=60):
/// - Sum in init: 0 + 100 = 100
/// - Sum in state: 50 + 60 = 110 ≠ 100
/// - Generalized blocking: `x + y != 100`
///
/// # Design Note
///
/// This generalizer requires the transition system to provide information about
/// whether sums are preserved. Without this, it falls back to simpler checks.
/// For full algebraic verification, PDR's internal implementation is preferred.
///
/// Reference: PDR's Phase 0 (lines 6868-6929 in pdr.rs)
pub(crate) struct ConstantSumGeneralizer;

impl Default for ConstantSumGeneralizer {
    fn default() -> Self {
        Self::new()
    }
}

impl ConstantSumGeneralizer {
    /// Create a new constant sum generalizer.
    pub(crate) fn new() -> Self {
        Self
    }
}

impl LemmaGeneralizer for ConstantSumGeneralizer {
    fn generalize(&self, lemma: &ChcExpr, level: u32, ts: &mut dyn TransitionSystemRef) -> ChcExpr {
        let conjuncts = lemma.collect_conjuncts();

        // Need at least 2 equalities to find sum patterns
        if conjuncts.len() < 2 {
            return lemma.clone();
        }

        // Extract all (var_name, value) pairs from equalities
        let var_vals: Vec<(String, i128)> = conjuncts
            .iter()
            .filter_map(|e| e.extract_var_int_equality().map(|(v, c)| (v.name, c)))
            .collect();

        if var_vals.len() < 2 {
            return lemma.clone();
        }

        // Get init bounds
        let init_bounds = ts.init_bounds();
        if init_bounds.is_empty() {
            return lemma.clone();
        }

        // Try each pair of variables for sum invariant
        for i in 0..var_vals.len() {
            for j in (i + 1)..var_vals.len() {
                let (var_i, val_i) = &var_vals[i];
                let (var_j, val_j) = &var_vals[j];

                // Get init bounds for both variables
                let (bounds_i, bounds_j) = match (init_bounds.get(var_i), init_bounds.get(var_j)) {
                    (Some(bi), Some(bj)) => (bi, bj),
                    _ => continue,
                };

                // Only use exact init values (single-point bounds)
                if !bounds_i.is_exact() || !bounds_j.is_exact() {
                    continue;
                }

                // Use checked arithmetic to avoid overflow
                // (i64 + i64 always fits in i128, so the sum is exact)
                let init_sum = i128::from(bounds_i.min) + i128::from(bounds_j.min);
                let state_sum = match val_i.checked_add(*val_j) {
                    Some(s) => s,
                    None => continue, // Sum overflows - skip this pair
                };

                // Check if state violates the sum invariant
                if state_sum != init_sum {
                    // Build blocking formula: (var_i + var_j) != init_sum
                    let sum_expr = ChcExpr::add(
                        ChcExpr::var(ChcVar::new(var_i, ChcSort::Int)),
                        ChcExpr::var(ChcVar::new(var_j, ChcSort::Int)),
                    );
                    let blocking_formula = ChcExpr::ne(sum_expr, ChcExpr::Int(init_sum));

                    // Check if this is inductive (at level 1 for global invariant)
                    let check_level = if level > 1 { 1 } else { level };
                    if ts.check_inductive(&blocking_formula, check_level) {
                        return blocking_formula;
                    }
                }
            }
        }

        lemma.clone()
    }

    fn name(&self) -> &'static str {
        "constant-sum"
    }
}
