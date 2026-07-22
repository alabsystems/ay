// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Dynamic tier boundary state for clause reduction (#5090).
//!
//! Groups tier-related fields into a single struct so the Solver's
//! hot BCP fields are not intermixed with clause reduction scheduling.
//! Accessed by reduction.rs and inprocessing/subsume.rs; never during BCP.

use crate::clause::{CORE_LBD, TIER1_LBD};

/// Dynamic tier boundaries for clause reduction (CaDiCaL tier.cpp).
///
/// These fields control how learned clauses are classified into tiers
/// (core, tier1, tier2) for reduction decisions. They are updated
/// periodically based on usage histograms, not on every conflict.
///
/// Reference: CaDiCaL `limit.hpp` (`keptglue`, `keptsize`) and
/// `tier.cpp` (dynamic boundary recomputation).
#[derive(Clone)]
pub(crate) struct TierState {
    /// Per-glue usage histogram, indexed by [stable_mode as usize][glue].
    /// Bumped in `bump_clause()` to track which glue values are most used.
    pub tier_usage: [Vec<u64>; 2],
    /// Total bumps per mode (stable/focused), for computing percentages.
    pub tier_bump_total: [u64; 2],
    /// Dynamic tier1 LBD boundary per mode [focused, stable]. Default: CORE_LBD (2).
    /// CaDiCaL stores `tier1[2]` indexed by `[focused=0, stable=1]`.
    /// `clause_tier()` always reads index 0 (focused) for reduction decisions.
    pub tier1_lbd: [u32; 2],
    /// Dynamic tier2 LBD boundary per mode [focused, stable]. Default: TIER1_LBD (6).
    /// CaDiCaL stores `tier2[2]` indexed by `[focused=0, stable=1]`.
    /// `clause_tier()` always reads index 0 (focused) for reduction decisions.
    pub tier2_lbd: [u32; 2],
    /// Maximum glue among clauses kept (not deleted) at the last `reduce_db`.
    /// Used by `likely_to_be_kept_clause` to gate subsumption candidates.
    /// CaDiCaL reference: `limit.hpp:36` (`keptglue`).
    pub kept_glue: u32,
    /// Maximum size among clauses kept (not deleted) at the last `reduce_db`.
    /// CaDiCaL reference: `limit.hpp:35` (`keptsize`).
    pub kept_size: u32,
    /// Conflict count at which to next recompute tier boundaries.
    pub next_recompute_tier: u64,
    /// Number of times tier boundaries have been recomputed.
    pub tier_recomputed: u64,
}

/// Initial conflict count before first tier boundary recomputation.
/// CaDiCaL: 1 << 1 = 2.
pub(crate) const TIER_RECOMPUTE_INIT: u64 = 2;

impl TierState {
    /// Create tier state with default boundaries.
    pub(crate) fn new() -> Self {
        Self {
            tier_usage: [vec![0u64; 64], vec![0u64; 64]],
            tier_bump_total: [0, 0],
            tier1_lbd: [CORE_LBD; 2],
            tier2_lbd: [TIER1_LBD; 2],
            kept_glue: 0,
            kept_size: 0,
            next_recompute_tier: TIER_RECOMPUTE_INIT,
            tier_recomputed: 0,
        }
    }
}
