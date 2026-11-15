// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Kissat 4.0.4's substitution schedule (`--sat-subst-kissat`).
//!
//! AY's AUTO collapse probe turns congruence and SCC decompose off for the
//! whole solve when the first preprocessing congruence merges fewer than 5%
//! of the active variables, or when the parsed density is above 20, and in
//! search it runs congruence on a conflict interval that doubles when a round
//! is unproductive. Kissat never turns either off. Every probe round runs
//! congruence and then substitutes (`probe.c:26-43`), and congruence is
//! skipped only by its delay counter: an unproductive closure (merging under
//! 0.1% of the active variables) adds one round to the delay, a productive
//! one halves it (`congruence.c:4594, 4629-4632`; `kimits.c:155-194`).
//!
//! Under the switch neither disarm fires, congruence runs in every in-search
//! simplification round the delay allows (AY's round cadence is Kissat's
//! probe cadence under `--sat-inproc-nlogn-schedule`), and decompose runs
//! after it every time. Off under LRAT, whose Default route keeps decompose
//! off.

use super::*;

/// Kissat's `delay` (`kimits.h`): `count` rounds are still skipped; `current`
/// is the length of the last delay.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(super) struct KissatDelay {
    pub(super) current: u32,
    pub(super) count: u32,
}

impl KissatDelay {
    /// `kissat_delaying`: true while delayed, consuming one round.
    pub(super) fn delaying(&mut self) -> bool {
        if self.count > 0 {
            self.count -= 1;
            true
        } else {
            false
        }
    }

    /// `kissat_bump_delay`.
    pub(super) fn bump(&mut self) {
        self.current = self.current.saturating_add(1);
        self.count = self.current;
    }

    /// `kissat_reduce_delay`.
    pub(super) fn reduce(&mut self) {
        if self.current == 0 {
            return;
        }
        self.current /= 2;
        self.count = self.current;
    }
}

/// Kissat's productivity test for congruence and sweeping (congruence.c:4629,
/// sweep.c:1718): `found` is under 0.1% of `of`.
pub(super) fn kissat_unproductive(found: u64, of: u64) -> bool {
    of == 0 || (found as f64) / (of as f64) < 0.001
}

impl Solver {
    /// `--sat-probe-round-kissat` runs the backbone every round only when it
    /// is Kissat's binary backbone alone (`--sat-backbone-binary-kissat`); AY's
    /// bounded-CDCL backbone keeps its own interval.
    pub(super) fn probe_round_kissat_backbone(&self) -> bool {
        self.cold.probe_round_kissat
            && ay_core::sat_ab_switches().backbone_binary_kissat == Some(true)
    }

    /// `--sat-subst-kissat`, and not under LRAT.
    pub(super) fn subst_kissat_active(&self) -> bool {
        self.cold.subst_kissat && !self.cold.lrat_enabled
    }

    /// Congruence under the delay counter: runs `congruence`, updates the
    /// delay from its yield, and returns whether it found equivalences.
    /// `None` when the delay skips this round.
    pub(super) fn congruence_kissat_delayed(&mut self) -> Option<bool> {
        if self.cold.congruence_kissat_delay.delaying() {
            return None;
        }
        let before = self.inproc.congruence.stats().equivalences_found;
        let found = self.congruence();
        let merged = self
            .inproc
            .congruence
            .stats()
            .equivalences_found
            .saturating_sub(before);
        if kissat_unproductive(merged, self.var_lifecycle.count_active() as u64) {
            self.cold.congruence_kissat_delay.bump();
        } else {
            self.cold.congruence_kissat_delay.reduce();
        }
        Some(found)
    }
}

#[cfg(test)]
mod tests {
    use super::{kissat_unproductive, KissatDelay};

    #[test]
    fn kissat_delay_grows_by_one_and_halves() {
        let mut d = KissatDelay::default();
        assert!(!d.delaying());
        d.bump();
        assert!(d.delaying());
        assert!(!d.delaying());
        d.bump();
        assert_eq!((d.current, d.count), (2, 2));
        assert!(d.delaying() && d.delaying() && !d.delaying());
        d.bump();
        d.reduce();
        assert_eq!((d.current, d.count), (1, 1));
        d.reduce();
        d.reduce();
        assert_eq!((d.current, d.count), (0, 0));
    }

    #[test]
    fn congruence_productivity_is_a_tenth_of_a_percent() {
        assert!(kissat_unproductive(0, 1000));
        assert!(kissat_unproductive(9, 10_000));
        assert!(!kissat_unproductive(10, 10_000));
        assert!(kissat_unproductive(0, 0));
    }
}
