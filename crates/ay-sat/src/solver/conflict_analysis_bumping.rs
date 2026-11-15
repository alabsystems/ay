// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Post-analysis variable bumping for VSIDS/VMTF activity management.
//!
//! Separated from the 1UIP analysis loop to keep the hot conflict-analysis
//! path focused on resolution, while activity updates write to VSIDS/VMTF
//! data structures in a separate cache-friendly pass.

use super::*;
use crate::literal::Literal;

mod admitted;

/// Optional override for reason-side bump recursion depth, read once from
/// `AY_BUMPREASON_DEPTH` (#678 branching A/B). `None` = CaDiCaL default
/// (2 stable / 1 focused); `Some(0)` = disable reason-side bumping entirely
/// (Kissat-like analyzed-only bump); `Some(d)` = cap depth at `d`.
fn bumpreason_depth_override() -> Option<u32> {
    // B21: the AY_BUMPREASON_DEPTH A/B override is retired; the shipped
    // CaDiCaL default (2 stable / 1 focused) stands.
    None
}

/// Kissat's bias-corrected EMA (`smooth.c`), window 1e5, of the decisions
/// between consecutive conflicts, one per search mode
/// (`--sat-bump-reasons-kissat`).
#[derive(Clone, Copy, Debug)]
pub(super) struct KissatSmooth {
    biased: f64,
    exp: f64,
    saved_decisions: u64,
}

impl Default for KissatSmooth {
    fn default() -> Self {
        Self {
            biased: 0.0,
            exp: 1.0,
            saved_decisions: 0,
        }
    }
}

impl KissatSmooth {
    const ALPHA: f64 = 1.0 / 100_000.0;

    /// `kissat_update_smooth` with `y` = decisions since this mode's last
    /// conflict (`analyze.c:379-388`).
    pub(super) fn update(&mut self, decisions: u64) {
        let y = decisions.saturating_sub(self.saved_decisions) as f64;
        self.saved_decisions = decisions;
        self.biased += Self::ALPHA * (y - self.biased);
        if self.exp != 0.0 {
            let next = self.exp * (1.0 - Self::ALPHA);
            self.exp = if next == self.exp { 0.0 } else { next };
        }
    }

    /// Start this mode's decision count at `decisions` (Kissat mode.c:212,
    /// on every switch into the mode), so its next sample holds only the
    /// decisions made in the mode.
    pub(super) fn restart_count_at(&mut self, decisions: u64) {
        self.saved_decisions = decisions;
    }

    /// The bias-corrected value (`AVERAGE`).
    pub(super) fn value(&self) -> f64 {
        if self.exp == 0.0 {
            self.biased
        } else {
            self.biased / (1.0 - self.exp)
        }
    }
}

impl Solver {
    /// Update the EMA of decisions-per-conflict for bumpreason rate limiting.
    /// CaDiCaL analyze.cpp:924-929: tracks how many decisions occurred between
    /// consecutive conflicts. High decision rates mean the solver is exploring
    /// widely, and reason bumping adds VSIDS noise rather than focus.
    pub(super) fn update_bumpreason_decision_rate(&mut self) {
        if self.cold.bump_reasons_kissat {
            if self.cold.kissat_probing {
                return;
            }
            let mode = usize::from(self.stable_mode);
            self.cold.kissat_decision_rate[mode].update(self.cold.search_decisions);
            return;
        }
        let decisions_this_conflict = self
            .num_decisions
            .saturating_sub(self.cold.bumpreason_saved_decisions);
        self.cold.bumpreason_saved_decisions = self.num_decisions;
        // EMA with alpha = 2/(1e5+1) = 0.00002, matching CaDiCaL emadecisions=1e5.
        const ALPHA: f64 = 2.0 / 100_001.0;
        self.cold.bumpreason_decision_rate +=
            ALPHA * (decisions_this_conflict as f64 - self.cold.bumpreason_decision_rate);
    }

    pub(super) fn bump_analyzed_variables(&mut self) {
        match self.bump_analyzed_variables_admitted(&conflict_analysis_finalize::admitted::Ordinary)
        {
            Ok(()) => (),
            Err(never) => match never {},
        }
    }

    pub(super) fn bump_reason_literals(&mut self) {
        match self.bump_reason_literals_admitted(&conflict_analysis_finalize::admitted::Ordinary) {
            Ok(()) => (),
            Err(never) => match never {},
        }
    }

    #[cfg(test)]
    pub(super) fn add_reason_literals_to_analyzed(
        &mut self,
        lit: Literal,
        depth: u32,
        extra_added: &mut usize,
        limit: usize,
    ) {
        match self.add_reason_literals_admitted(
            lit,
            depth,
            extra_added,
            limit,
            &conflict_analysis_finalize::admitted::Ordinary,
        ) {
            Ok(()) => (),
            Err(never) => match never {},
        }
    }
    /// Charge `ticks` search ticks for conflict analysis's resolution work
    /// (the conflict clause, the resolved reasons, binary reasons). Kissat
    /// charges none of it (analyze.c), only large reasons in minimization,
    /// shrinking and reason-side bumping (minimize.c:51, shrink.c:179,
    /// analyze.c:158), so `--sat-analysis-ticks-kissat` leaves it uncharged.
    #[inline(always)]
    pub(super) fn charge_resolution_ticks(&mut self, ticks: u64) {
        if !self.cold.analysis_ticks_kissat {
            self.search_ticks[usize::from(self.stable_mode)] += ticks;
        }
    }
}

#[cfg(test)]
mod kissat_smooth_tests {
    use super::KissatSmooth;

    /// Kissat's bias correction makes the average exact from the first update,
    /// where an uncorrected EMA started at zero reads about y * n / 1e5.
    #[test]
    fn kissat_smooth_is_bias_corrected() {
        let mut s = KissatSmooth::default();
        let mut decisions = 0;
        for _ in 0..3 {
            decisions += 25;
            s.update(decisions);
            assert!((s.value() - 25.0).abs() < 1e-9, "value {}", s.value());
        }
        // A sample holds every decision since the last one; the mode switch
        // re-baselines the count so another mode's decisions stay out.
        s.update(decisions + 40);
        assert!(s.value() > 25.0);
        let mut t = KissatSmooth::default();
        t.update(25);
        t.restart_count_at(1_000);
        t.update(1_025);
        assert!((t.value() - 25.0).abs() < 1e-9, "value {}", t.value());
    }
}
