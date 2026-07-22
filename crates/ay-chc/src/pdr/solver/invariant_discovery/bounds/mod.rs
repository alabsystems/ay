// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bound / guard invariant discovery.
//!
//! Submodules:
//! - `bounds_core`: basic monotonicity bounds, orchestrator, entry guards,
//!   fact conjunct promotion, joint shifted bounds, preservation utilities,
//!   bound propagation, and monotonicity checks.
//! - `bounds_scaled_diff`: scaled difference bounds (B - k*A >= c).
//! - `bounds_sum`: sum bounds (A + B >= c).
//! - `bounds_exit`: loop exit bounds and scaled loop exit bounds.
//! - `bounds_ite_hints`: ITE toggle bounds, ITE constant propagation, and
//!   lemma hint application.

use super::*;

mod bounds_bv;
mod bounds_bv_candidates;
mod bounds_bv_seed_helpers;
mod bounds_core;
mod bounds_entry_value;
mod bounds_exit;
mod bounds_ite_hints;
mod bounds_scaled_diff;
mod bounds_scaled_diff_verify;
mod bounds_sum;

#[cfg(test)]
mod bounds_tests;

/// Candidate bounds are checked from high to low to find the tightest valid invariant.
///
/// Keep these small: each candidate may require multiple SMT queries.
/// Extended range: gj2007_m_1 needs A - 5*C >= -6, so we need negative bounds.
const SCALED_DIFF_BOUND_CANDIDATES: [i128; 10] = [2, 1, 0, -1, -2, -3, -4, -5, -6, -7];
const SUM_BOUND_CANDIDATES: [i128; 5] = [2, 1, 0, -1, -2];

/// Upper bound candidates for sum bounds (A + B <= c). Checked from low to high
/// to find the tightest valid upper bound (lowest c such that A + B <= c holds).
const SUM_UPPER_BOUND_CANDIDATES: [i128; 5] = [-2, -1, 0, 1, 2];
