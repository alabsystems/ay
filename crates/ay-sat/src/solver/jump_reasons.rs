// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Kissat 4.0.4's effective jump-reason gate (`--sat-jump-reasons-kissat`).
//!
//! A binary propagation stores a jump reason: when the implying literal was
//! itself assigned through a binary clause, the new literal takes that
//! literal's reason, so reasons point at the roots of binary implication
//! chains (Kissat `fastassign.h:12-19`, AY `enqueue_binary_reason`). Analysis,
//! minimization, shrinking and reason-side bumping then walk the compressed
//! graph: the UIP moves toward chain roots and chain-interior variables are
//! neither learned nor bumped.
//!
//! Kissat gates it on `classification.bigbig` (`classify.c:5-28`), which
//! compares `kissat_percent (binary, clauses)`, a 0-100 percentage, against
//! `bigbigfraction / 1000.0` = 0.99. The test therefore holds on any formula
//! over `smallclauses` (100K) clauses with at least 0.99 percent binary
//! clauses, not the 99 percent the option's text describes and AY's default
//! gate (`solve/mod.rs`) copies. Kissat reclassifies at search start, after
//! elimination, probing and every reduction, and takes the jump without any
//! gate when it assigns a learned binary clause's UIP (`assign.c:31-43`).
//!
//! Under the switch AY classifies with Kissat's counts (all live binary
//! clauses, learned ones included, against binary plus live large irredundant
//! clauses), at solve start, at search start after preprocessing, at level 0
//! after each in-search simplification round, and at each reduction. A reduction may only switch the gate on: it runs above
//! level 0, and reduction's trail protection for learned binaries
//! (`binary_clause_may_support_the_trail`) is keyed on the gate, so switching
//! it off there could delete a binary that still supports a literal reason on
//! the trail. The learned-binary jump is taken only while the gate is on, for
//! the same reason.

use super::*;

/// Kissat's `smallclauses` default: a formula with at most this many clauses
/// is classified small and never takes jump reasons.
const KISSAT_SMALL_CLAUSES: u64 = 100_000;

/// Kissat's effective `bigbig` classification (`classify.c:7-19`).
pub(super) fn kissat_bigbig(binary: u64, large_irredundant: u64) -> bool {
    let clauses = binary + large_irredundant;
    clauses > KISSAT_SMALL_CLAUSES && 100.0 * binary as f64 / clauses as f64 >= 0.99
}

impl Solver {
    /// Kissat's clause counts: (binary clauses, learned ones included; large
    /// irredundant clauses).
    fn kissat_classify_counts(&self) -> (u64, u64) {
        let (mut binary, mut large) = (0u64, 0u64);
        // Live clauses only: garbage-kept and pending-garbage husks are not
        // in Kissat's counters (clause.c `dec_clause`), nor are unit clauses.
        for off in self.arena.live_indices() {
            let len = self.arena.len_of(off);
            if len == 2 {
                binary += 1;
            } else if len >= 3 && !self.arena.is_learned(off) {
                large += 1;
            }
        }
        (binary, large)
    }

    /// Recompute the jump-reason gate under `--sat-jump-reasons-kissat`.
    /// `allow_off` is true only at level 0 (see the module comment).
    pub(super) fn reclassify_jump_reasons_kissat(&mut self, allow_off: bool) {
        if !self.cold.jump_reasons_kissat || self.cold.lrat_enabled {
            return;
        }
        if self.cold.jump_reasons_enabled && !allow_off {
            return;
        }
        let (binary, large) = self.kissat_classify_counts();
        self.cold.jump_reasons_enabled = kissat_bigbig(binary, large);
    }

    /// Kissat assigns a learned binary clause's UIP through the jump rule
    /// (`assign.c:31-43`): `Some(other)` names the clause's false literal when
    /// that applies, so the caller enqueues with a literal reason.
    pub(super) fn learned_binary_jump_reason(
        &self,
        learned: &[Literal],
        backtrack_level: u32,
    ) -> Option<Literal> {
        (self.cold.jump_reasons_kissat
            && self.cold.jump_reasons_enabled
            && !self.cold.lrat_enabled
            && learned.len() == 2
            && backtrack_level > 0)
            .then(|| learned[1])
    }
}

#[cfg(test)]
mod tests {
    use super::kissat_bigbig;

    #[test]
    fn kissat_bigbig_is_a_percentage_against_a_fraction() {
        // Small formulas never qualify, whatever their binary share.
        assert!(!kissat_bigbig(100_000, 0));
        // Over 100K clauses, 0.99 percent binary clauses is enough ...
        assert!(kissat_bigbig(991, 99_010));
        // ... and just under it is not.
        assert!(!kissat_bigbig(989, 99_012));
        // cabp-V-nos6 k275: 7.66M binaries against 1.04M ternaries (89 percent).
        assert!(kissat_bigbig(7_661_115, 1_039_837));
        // A large formula with no binary clause stays off until it learns some.
        assert!(!kissat_bigbig(0, 5_000_000));
    }
}
