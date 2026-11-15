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
    /// `--sat-reduce-kissat-tiers`: Kissat 4.0.4's tier rule instead of
    /// CaDiCaL's. The tier2 scan starts past the tier1 glue (Kissat tiers.c:28;
    /// CaDiCaL counts the tier1 bucket twice, so a histogram with half its uses
    /// at glue 1 always yields tier2 = 2), and reduction, vivification and
    /// subsumption read tier2 from STABLE mode (Kissat internal.h:255-256,
    /// `TIER2 = tier2[1]`). On E00X23 AY's tiers were 1/2 focused and 2/11
    /// stable against Kissat's 1/7 and 4/19, so every recently used clause
    /// with glue 3 or more went straight into the sort pool.
    pub kissat_rule: bool,
}

/// Highest glue the usage histogram tells apart under CaDiCaL's rule; higher
/// glues share its last bucket.
const CADICAL_MAX_GLUE_USED: usize = 63;
/// The same under Kissat's rule (`statistics.h` `MAX_GLUE_USED`): its stable
/// tier2 reaches 127 on cabp-V-nos6, where 44-57 percent of stable-mode clause
/// uses have glue 127 or more.
const KISSAT_MAX_GLUE_USED: usize = 127;

/// Initial conflict count before first tier boundary recomputation.
/// CaDiCaL: 1 << 1 = 2.
pub(crate) const TIER_RECOMPUTE_INIT: u64 = 2;

impl TierState {
    /// Create tier state with default boundaries.
    pub(crate) fn new() -> Self {
        Self {
            tier_usage: [
                vec![0u64; KISSAT_MAX_GLUE_USED + 1],
                vec![0u64; KISSAT_MAX_GLUE_USED + 1],
            ],
            tier_bump_total: [0, 0],
            tier1_lbd: [CORE_LBD; 2],
            tier2_lbd: [TIER1_LBD; 2],
            kept_glue: 0,
            kept_size: 0,
            next_recompute_tier: TIER_RECOMPUTE_INIT,
            tier_recomputed: 0,
            kissat_rule: false,
        }
    }

    pub(super) fn build_admitted<A: super::construction::Construction>(
        a: &A,
    ) -> Result<Self, A::Error> {
        a.metadata::<Self>()?;
        Ok(Self {
            tier_usage: [
                a.filled(KISSAT_MAX_GLUE_USED + 1, 0)?,
                a.filled(KISSAT_MAX_GLUE_USED + 1, 0)?,
            ],
            tier_bump_total: [0, 0],
            tier1_lbd: [CORE_LBD; 2],
            tier2_lbd: [TIER1_LBD; 2],
            kept_glue: 0,
            kept_size: 0,
            next_recompute_tier: TIER_RECOMPUTE_INIT,
            tier_recomputed: 0,
            kissat_rule: false,
        })
    }

    /// The last usage-histogram bucket a bump may land in.
    #[inline]
    pub(crate) fn max_glue_used(&self) -> usize {
        if self.kissat_rule {
            KISSAT_MAX_GLUE_USED
        } else {
            CADICAL_MAX_GLUE_USED
        }
    }

    /// The tier2 glue boundary that reduction, vivification and subsumption
    /// read: focused tier2 under CaDiCaL's rule, `max(tier1[focused],
    /// tier2[stable])` under Kissat's (reduce.c:62-63).
    #[inline]
    pub(crate) fn reduce_tier2(&self) -> u32 {
        if self.kissat_rule {
            self.tier1_lbd[0].max(self.tier2_lbd[1])
        } else {
            self.tier2_lbd[0]
        }
    }
}
