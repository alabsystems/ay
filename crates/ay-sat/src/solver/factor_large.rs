// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `--sat-factor-large`, ON by default since 2026-09-18 (`false` opts out):
//! lets the clause-factoring pass run on formulas the expensive-pass size gate
//! refuses. Lever 3 of competition/proof-posture-parity/PLAN-next-sat-levers.md at 9598c4206
//! (2026-09-14). Adopted on the A/B of competition/proof-posture-parity at 9598c4206: it solved
//! cabp-M k39 (UNSAT, 3 of 3 and at 1500 s) and lost nothing at 1500 s.
//!
//! On a formula above `PREPROCESS_EXPENSIVE_MAX_VARS` (200K) or
//! `PREPROCESS_EXPENSIVE_MAX_CLAUSES` (3M) four gates refuse factoring on the
//! default DIMACS route, and they fire together:
//! - the preprocess-time size gate at the factor step
//!   (`config_preprocess.rs`, `skip_expensive_preprocessing_passes`) and its
//!   in-search twin (`inprocessing_elimination.rs`,
//!   `skip_expensive_equivalence_passes`), whose only bypass is the dense band
//!   (density >= 90);
//! - the CaDiCaL delay gate at both factor sites,
//!   `floor_log10(active vars) > bve_phases + FACTOR_DELAY`, where
//!   `bve_phases` counts BVE phases entered. Above 150K variables the default
//!   route ships no BVE, so `bve_phases` stays 0 and the gate never opens on
//!   a formula with a million active variables (log10 = 6 > 0 + 4). Kissat's
//!   gate has the same shape (factor.c, `log10(active) <= eliminations +
//!   factordelay`), but Kissat always has an elimination phase to count:
//!   `eliminations` is bumped when `kissat_eliminate` is entered, whether or
//!   not it eliminated anything, and nothing size-gates its entry.
//!
//! The switch opens all four, and only inside the band below. Everything else
//! stays: the per-call effort budget (`FACTOR_INIT_TICKS`, 5 percent of the
//! search ticks, `FACTOR_MAX_EFFORT`), the interval and mark gates, the
//! occurrence build, and the proof emission (every factoring is a RAT
//! addition on its fresh literal, on the DRAT and VeriPB surfaces alike). It
//! never opens under LRAT, where the capability table clamps factoring, or
//! after an incremental call. Under `false`, every predicate is the boolean
//! it was before the lever.

use super::*;

/// The variable ceiling of the band: `BVE_GIANT_RAW_MAX_VARS` in
/// `variant.rs`, the giant raw-BVE route's own ceiling (arm C of the lever),
/// which `--sat-giant-band-max-vars` raises for both bands together
/// (`crate::variant::giant_band_max_vars`).
const FACTOR_LARGE_MAX_VARS: usize = 2_000_000;

/// The band `--sat-factor-large` acts in: a formula the expensive-pass size
/// gate refuses, and at most 2M variables, 10M active clauses (the giant
/// congruence band, `AUTO_CONGRUENCE_GIANT_MAX_CLAUSES`) and a density of
/// `PREPROCESS_BVE_SKIP_DENSITY` (20). In-band formulas (which the size gate
/// admits) and the giant and dense formulas outside it see no change.
pub(super) fn factor_large_band_counts(num_vars: usize, active_clauses: usize) -> bool {
    let refused = num_vars > PREPROCESS_EXPENSIVE_MAX_VARS
        || active_clauses > PREPROCESS_EXPENSIVE_MAX_CLAUSES;
    if !refused || num_vars == 0 {
        return false;
    }
    let density = active_clauses as f64 / num_vars as f64;
    num_vars <= FACTOR_LARGE_MAX_VARS.max(crate::variant::giant_band_max_vars())
        && active_clauses <= AUTO_CONGRUENCE_GIANT_MAX_CLAUSES
        && density <= PREPROCESS_BVE_SKIP_DENSITY
}

impl Solver {
    /// `true` when `--sat-factor-large` (on by default) opens the factor gates
    /// on this formula. Read per call, not cached: tests scope the switch, and
    /// the band is read on the live counts.
    pub(super) fn factor_large_unlock_active(&self) -> bool {
        if ay_core::sat_ab_switches().factor_large == Some(false) {
            return false;
        }
        if self.cold.lrat_enabled || self.cold.has_been_incremental {
            return false;
        }
        factor_large_band_counts(self.num_vars, self.arena.active_clause_count())
    }

    /// The CaDiCaL delay gate shared by the factor sites: `true` refuses. It is
    /// open in the band unless `--sat-factor-large false`; otherwise it is the
    /// predicate the sites carried before.
    pub(super) fn factor_delay_gate_holds(&self) -> bool {
        let active_vars = self
            .num_vars
            .saturating_sub(self.var_lifecycle.count_removed());
        let active_log10 = Self::floor_log10(active_vars);
        // `--sat-factor-schedule-kissat`: Kissat's gate, over its in-search
        // eliminations and at every size (factor.c:1068-1085).
        if self.cold.factor_schedule_kissat {
            return active_log10 > self.cold.kissat_eliminations + FACTOR_DELAY;
        }
        let delay_limit = u64::from(self.cold.bve_phases) + FACTOR_DELAY;
        active_log10 > delay_limit && !self.factor_large_unlock_active()
    }
}
