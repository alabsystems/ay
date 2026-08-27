// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! LBD-free two-stage learned clause management (arXiv:2602.20829).
//!
//! Cai, Zhang, Shi, Tao, Xu, *Rethinking Clause Management for CDCL SAT
//! Solvers* — 3rd place Main and Main UNSAT, SAT Competition 2026, shipped in
//! `yalun_kissat-eda-*`. "EDA" is the authors' lab, not the technique: the
//! technique is a two-stage retention policy that removes LBD from the
//! deletion decision entirely.
//!
//! ```text
//! OnLearnedClause(c)   score(c) <- 1
//! OnClauseUse(c)       score(c) <- score(c) + 1
//!                        ... when c forces a literal during BCP, OR
//!                        ... when c is a reason during conflict analysis
//! OnPeriodicDecay()    every T conflicts, for every learnt c:
//!                        score(c) <- max(0, score(c) - 1)          (T = 4096)
//! TwoStageReduction()  Stage 1: keep every c with score(c) > 0
//!                      Stage 2: Z <- { c | score(c) = 0 },
//!                               sort Z by clause LENGTH DESCENDING,
//!                               delete the leading `percent` of Z
//!                      percent = 0.90 - (0.90 - 0.50) / log10(r + 9)
//! ```
//!
//! The paper's ablation (Table 3) is why this is one switch and not two:
//! stage 1 + stage 2 solves 60, stage 1 alone 56, stage 2 alone 53. Shipping
//! half of it measures nothing.
//!
//! # What AY's `used` counted before this module
//!
//! AY inherited kissat/CaDiCaL's `used` field verbatim, and it is NOT the
//! paper's score. Three differences, all load-bearing:
//!
//! 1. **It is a recency flag, not a frequency counter.** Every use writes
//!    `set_used(idx, MAX_USED)` (31) rather than `+= 1`
//!    (`solver/reduction.rs` `bump_clause`, `solver/conflict_analysis_lrat.rs`
//!    on learn, `solver/otfs.rs` after in-place strengthening). A clause used
//!    once and a clause used ten thousand times are indistinguishable.
//! 2. **The BCP half of `OnClauseUse` is missing entirely.** Nothing in
//!    `propagation*.rs` touches `used`; only conflict analysis and clause
//!    creation do. That is faithful to kissat (`learn.c:110`, `deduce.c:18`,
//!    `reduce.c:72` are its only `c->used` writes) and to CaDiCaL, and it is
//!    exactly the signal the paper adds.
//! 3. **The decay period is a reduction round, not a conflict count.**
//!    `decay_used` runs once per learned clause per `reduce_db` call
//!    (`solver/reduction_execute.rs`), so the decay period drifts with the
//!    `1000*sqrt(r)` reduce schedule instead of being the paper's fixed
//!    `T = 4096` conflicts.
//!
//! And in AY `used` is only ever a tier-conditional SURVIVAL PREDICATE (Core
//! survives on `used > 0`, Tier1 on `used >= MAX_USED - 1`, Tier2 ignores it).
//! The RANKING key is `(glue << 32) | size` — LBD first, length as tiebreak —
//! which is precisely what the paper replaces.
//!
//! # What this module changes, and what it deliberately does not
//!
//! Armed, it re-points `used` to mean the paper's score and swaps the
//! keep/delete decision. It does NOT touch:
//!
//! - the reduction TRIGGER (`next_reduce_db`, `L += 1000*sqrt(r+1)`) — mixing
//!   a schedule change in would confound the corpus A/B;
//! - reason-clause protection, IC3-lemma protection, LRAT retention, satisfied
//!   clause GC, or anything else that deletion correctness rests on;
//! - `lbd()` itself, which still drives tier bookkeeping, `likely_to_be_kept`
//!   and subsumption gating.
//!
//! # Known deviations from the paper (all documented, none silent)
//!
//! - ~~**Score saturates at `MAX_USED` (31).**~~ REMOVED — see "The 5-bit
//!   ceiling, measured and removed" below. The score now has 16 bits and its
//!   own arena slot; `MAX_USED` is once again the OFF arm's recency flag only.
//! - **Virtual binary reasons are not scored.** `enqueue_binary_reason*`
//!   encodes the reason as a literal rather than a `ClauseRef`, so a learned
//!   binary propagating through that path gets no BCP bump. Harmless in
//!   practice: stage 2 sorts by length DESCENDING, so binaries are the last
//!   thing it deletes.
//! - **The `lbd <= reduce_permanent_protect_lbd()` gate is skipped** under the
//!   arm, because the policy is meant to be LBD-free. IC3 blocking lemmas keep
//!   their own explicit `is_ic3_lemma` protection, which is what incremental
//!   soundness actually rests on.
//! - **Flush is folded into the two-stage path.** CaDiCaL's aggressive flush
//!   (delete every unused clause regardless of tier, at 100K*3^n conflicts)
//!   has no counterpart in the paper, and under score semantics its
//!   `used >= MAX_USED - 1` tier gate would mean something different from what
//!   it was written to mean. Armed, a due flush still advances the flush
//!   schedule but runs `TwoStageReduction` instead.
//! - **Hyper resolvents keep their one-round lifetime.** Unchanged from the
//!   OFF arm; they are not the paper's subject. Armed, the one-round test
//!   reads the two-stage score rather than `used`, which the arm no longer
//!   writes.
//! - **Armed, `used` is never written, so it reads 0 everywhere.** Moving the
//!   score into its own slot means the arm no longer co-opts `used`, and no
//!   arm-side code writes it. Two default-off consumers therefore see a
//!   constant 0 under the arm: the `learned_1963` BCP saved-position probes
//!   (`propagation_bcp*.rs`, gated behind their own switches) and the
//!   between-solve incremental GC (`reduction_between_solves.rs`), which
//!   becomes maximally aggressive. Neither is a soundness surface — the GC
//!   keeps its unconditional IC3-lemma, reason-clause and `lbd <= CORE_LBD`
//!   protections — and neither is reachable in the shipped one-shot DIMACS
//!   configuration, which is the only place this arm has ever been measured.
//!
//! # The 5-bit ceiling: real, removed, and INERT
//!
//! The first port packed the score into the existing 5-bit `used` bitfield and
//! recorded the ceiling as knob #1 of its null result. It was a real confound.
//! Measured at HEAD, arm on, `--competition -T:120`, share of `OnClauseUse`
//! increments discarded at the ceiling:
//!
//! ```text
//! 0be1e12a 93.6%   ba773277 87.7%   12cd0c31 86.5%   262a226a 84.4%
//! 920bbe55 65.2%   958fd8bd 50.9%   f2c6d035  6.0%
//! ```
//!
//! and `score_max == 31` — pinned — on all seven. Widened, saturation is 0 on
//! five of seven and `score_max` is 1,689 / 7,073 / 21,413 / 22,702 / 27,375 /
//! 65,535 / 65,535. A frequency counter really does need three orders of
//! magnitude more range than the field it was living in.
//!
//! **And it changed nothing that matters.** Stage 1's test is `score > 0` — a
//! binary predicate — so range only reaches the decision through the decay
//! clock: a clause at score `s` needs `s` consecutive decay periods of disuse
//! to fall to a stage-2 candidate. AY's runs tick that clock 39-197 times in
//! total, so a score of 31 was *already* effectively unbounded, and every one
//! of those discarded increments lived strictly above the decision boundary.
//! The measured stage-1 keep share moves by at most **0.9 points**:
//!
//! ```text
//! keep%  5-bit -> 16-bit   12cd0c31 77.0->77.8   262a226a 81.2->81.3
//!                          958fd8bd 75.5->75.4   0be1e12a 65.3->66.2
//!                          920bbe55 69.8->69.5   f2c6d035 80.9->80.9
//!                          ba773277 76.5->76.7
//! ```
//!
//! (Monotonicity says the sign cannot surprise either: a saturating counter
//! with a higher cap is pointwise `>=` one with a lower cap, so widening can
//! only make the policy MORE retentive, never less — and over-retention was
//! the diagnosed failure mode.)
//!
//! **The knob that does move retention is `T`.** Rebuilt at `T = 1024`, the
//! same seven instances give keep shares of 40.9-62.2% instead of 65.3-81.3%,
//! and the arm's peak RSS and wall both improve over `T = 4096`. It still does
//! not beat the OFF arm: 3 of 7 instances take fewer conflicts, 4 take more —
//! the same 3/4 split as `T = 4096`. See the commit that landed this width for
//! the full conflict tables.

use super::*;

/// Decay interval `T`, in conflicts. The paper's sole hyperparameter; 4096 is
/// the value it measures as optimal for kissat (MiniSat wants 2048).
pub(super) const TWO_STAGE_DECAY_INTERVAL: u64 = 4096;

/// Stage-2 deletion fraction lower bound, in permille. The paper's 0.50.
///
/// Deliberately NOT `REDUCE_LOW_PERMILLE` (750). AY raised its own low bound
/// to 750 in #8448 because the fraction there applies to the whole post-tier
/// candidate pool; here it applies only to the `score == 0` residue, which is
/// a different and smaller set. Following the paper's number keeps the arm a
/// port rather than a hybrid.
pub(super) const TWO_STAGE_LOW_PERMILLE: u64 = 500;

/// Stage-2 deletion fraction upper bound, in permille. The paper's 0.90.
pub(super) const TWO_STAGE_HIGH_PERMILLE: u64 = 900;

/// `percent = 0.90 - (0.90 - 0.50) / log10(r + 9)`, in permille.
///
/// Same shape as `dynamic_reduce_delete_permille` (and as kissat
/// `reduce.c:105-113`), pinned to the paper's bounds. Split out so the formula
/// can be unit-tested at specific rounds without a solver.
#[inline]
pub(super) fn two_stage_delete_permille(reductions: u64) -> u64 {
    let high = TWO_STAGE_HIGH_PERMILLE as f64;
    let low = TWO_STAGE_LOW_PERMILLE as f64;
    let permille = high - (high - low) / (reductions as f64 + 9.0).log10();
    permille.clamp(low, high) as u64
}

/// Bucket a score into the reduce-time histogram emitted for reachability.
///
/// The top two buckets exist only because the score field was widened: with
/// the old 5-bit field every score `>= 16` landed in one bucket that was
/// indistinguishable from "pinned at the ceiling". `32-255` and `256+` are
/// where a real frequency counter's tail shows up, so a flat zero in both is
/// evidence the width bought nothing.
#[inline]
fn two_stage_score_bucket(score: u16) -> usize {
    match score {
        0 => 0,
        1 => 1,
        2..=3 => 2,
        4..=7 => 3,
        8..=15 => 4,
        16..=31 => 5,
        32..=255 => 6,
        _ => 7,
    }
}

impl Solver {
    /// `OnLearnedClause(c)`: `score(c) <- 1`.
    ///
    /// Called from the single clause-creation choke point
    /// (`add_clause_db_checked`) so that learned clauses created outside
    /// conflict analysis — vivification replacements, hyper resolvents, DIP
    /// extension clauses — also start at 1 rather than at the arena default 0.
    /// A clause born at 0 would be a stage-2 candidate in its first reduction,
    /// which is the exact failure mode stage 2 exists to prevent.
    #[inline]
    pub(super) fn two_stage_note_learned(&mut self, clause_idx: usize) {
        debug_assert!(self.two_stage_clause_management);
        self.arena.set_two_stage_score(clause_idx, 1);
        self.stats.two_stage_learned_inits += 1;
    }

    /// `OnClauseUse(c)` for the BCP half: `c` forced a literal.
    ///
    /// Hot path — called once per arena-clause-forced assignment. The arm
    /// check is first and is a load from the HOT section of `Solver`.
    #[inline(always)]
    pub(super) fn two_stage_note_bcp_use(&mut self, reason: ClauseRef) {
        if !self.two_stage_clause_management {
            return;
        }
        if self.two_stage_bump_score(reason.0 as usize) {
            self.stats.two_stage_bcp_bumps += 1;
        }
    }

    /// `OnClauseUse(c)` for the conflict-analysis half: `c` was a reason.
    #[inline]
    pub(super) fn two_stage_note_analysis_use(&mut self, clause_idx: usize) {
        debug_assert!(self.two_stage_clause_management);
        if self.two_stage_bump_score(clause_idx) {
            self.stats.two_stage_analysis_bumps += 1;
        }
    }

    /// `score(c) += 1`, saturating at `MAX_TWO_STAGE_SCORE`. Returns whether
    /// the clause was a scored (learned) clause at all.
    ///
    /// Irredundant clauses are never reduction candidates, so scoring them
    /// would be pure hot-path cost.
    #[inline(always)]
    fn two_stage_bump_score(&mut self, clause_idx: usize) -> bool {
        if !self.arena.is_learned(clause_idx) {
            return false;
        }
        let score = self.arena.two_stage_score(clause_idx);
        if score < crate::clause_arena::MAX_TWO_STAGE_SCORE {
            self.arena.set_two_stage_score(clause_idx, score + 1);
        } else {
            self.stats.two_stage_score_saturations += 1;
        }
        true
    }

    /// `OnPeriodicDecay()`: every `T` conflicts, `score <- max(0, score - 1)`
    /// for every learned clause.
    ///
    /// This REPLACES the per-reduce-round `decay_used` sweep rather than
    /// adding a second decay — `reduce_db` skips its own decay while the arm
    /// is set. Cost is one arena flags read-modify-write per learned clause
    /// every 4096 conflicts.
    pub(super) fn two_stage_periodic_decay_if_due(&mut self) {
        if !self.two_stage_clause_management {
            return;
        }
        if self.num_conflicts < self.cold.two_stage_next_decay {
            return;
        }
        self.cold.two_stage_next_decay =
            self.num_conflicts.saturating_add(TWO_STAGE_DECAY_INTERVAL);

        self.cold.reduce_indices_buf.clear();
        self.cold
            .reduce_indices_buf
            .extend(self.arena.learned_indices());
        let mut decayed = 0u64;
        for i in 0..self.cold.reduce_indices_buf.len() {
            let idx = self.cold.reduce_indices_buf[i];
            if !self.arena.is_active(idx) || !self.arena.is_learned(idx) {
                continue;
            }
            if self.arena.two_stage_score(idx) > 0 {
                self.arena.decay_two_stage_score(idx);
                decayed += 1;
            }
        }
        self.stats.two_stage_decay_rounds += 1;
        self.stats.two_stage_decay_clauses += decayed;
    }

    /// `TwoStageReduction` per-clause decision, called from `reduce_db` once
    /// the correctness-adjacent protections (reason, IC3, hyper) have run.
    ///
    /// Returns `true` when stage 1 keeps the clause outright (`score > 0`).
    /// Returns `false` after pushing it into the shared reduce-candidate pool
    /// as a stage-2 candidate, ranked by LENGTH alone: `compare_reduce_candidates`
    /// deletes the HIGHEST ranks first, so a bare length rank is exactly the
    /// paper's "sort Z by clause length in descending order". Binaries rank
    /// lowest and are the last thing this policy will ever remove.
    ///
    /// Also feeds the reduce-time score histogram, which is the reachability
    /// proof for the arm: only this path can emit it, so a flat-zero histogram
    /// with a non-zero reduce count means the policy never actually ran.
    pub(super) fn two_stage_classify_candidate(
        &mut self,
        clause_idx: usize,
        score: u16,
        size: u32,
    ) -> bool {
        self.stats.two_stage_score_hist[two_stage_score_bucket(score)] += 1;
        self.stats.two_stage_score_total += u64::from(score);
        if u64::from(score) > self.stats.two_stage_score_max {
            self.stats.two_stage_score_max = u64::from(score);
        }
        if score > 0 {
            return true;
        }
        self.cold.reduce_candidates_buf.push(cold::ReduceCandidate {
            rank: u64::from(size),
            clause_idx,
            pressure_adjusted: false,
            pressure_retained: false,
            pressure_steps: 0,
        });
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The paper's `percent = 0.90 - (0.90 - 0.50) / log10(r + 9)` at several
    /// rounds, computed independently of the implementation.
    #[test]
    fn two_stage_percent_matches_the_paper_formula() {
        for r in [0u64, 1, 2, 10, 91, 100, 1_000, 10_000] {
            let expected = 0.90 - (0.90 - 0.50) / ((r as f64) + 9.0).log10();
            let expected_permille = (expected * 1000.0).clamp(500.0, 900.0) as u64;
            assert_eq!(
                two_stage_delete_permille(r),
                expected_permille,
                "percent mismatch at reduction round {r}"
            );
        }
    }

    /// Anchored values so a future refactor cannot drift the curve silently.
    /// r=0: log10(9)=0.954 => 0.90 - 0.419 = 0.481, clamped up to the 0.50
    /// floor. r=1: log10(10)=1 => 0.90 - 0.40 = 0.50 exactly, the floor again.
    /// r=91: log10(100)=2 => 0.70. r=9991: log10(10^4)=4 => 0.80.
    #[test]
    fn two_stage_percent_anchors() {
        assert_eq!(two_stage_delete_permille(0), 500);
        assert_eq!(two_stage_delete_permille(1), 500);
        assert_eq!(two_stage_delete_permille(10), 587);
        assert_eq!(two_stage_delete_permille(91), 700);
        assert_eq!(two_stage_delete_permille(9_991), 800);
        // Monotone non-decreasing, and never outside [0.50, 0.90].
        let mut prev = 0;
        for r in 0..2_000u64 {
            let p = two_stage_delete_permille(r);
            assert!((500..=900).contains(&p), "r={r} p={p} out of band");
            assert!(p >= prev, "r={r} percent went backwards: {prev} -> {p}");
            prev = p;
        }
    }

    #[test]
    fn score_buckets_partition_the_range() {
        assert_eq!(two_stage_score_bucket(0), 0);
        assert_eq!(two_stage_score_bucket(1), 1);
        assert_eq!(two_stage_score_bucket(3), 2);
        assert_eq!(two_stage_score_bucket(4), 3);
        assert_eq!(two_stage_score_bucket(7), 3);
        assert_eq!(two_stage_score_bucket(8), 4);
        assert_eq!(two_stage_score_bucket(15), 4);
        assert_eq!(two_stage_score_bucket(16), 5);
        assert_eq!(
            two_stage_score_bucket(u16::from(crate::clause_arena::MAX_USED)),
            5
        );
        // The two buckets that only exist because the field was widened past
        // the old 5-bit `used` ceiling.
        assert_eq!(two_stage_score_bucket(32), 6);
        assert_eq!(two_stage_score_bucket(255), 6);
        assert_eq!(two_stage_score_bucket(256), 7);
        assert_eq!(
            two_stage_score_bucket(crate::clause_arena::MAX_TWO_STAGE_SCORE),
            7
        );
    }

    /// The widened field must actually be reachable: a score above the old
    /// 5-bit ceiling has to survive a store/load round trip through the arena
    /// header word it now occupies, and must not disturb `used`.
    #[test]
    fn wide_score_round_trips_past_the_old_five_bit_ceiling() {
        let mut arena = crate::clause_arena::ClauseArena::new();
        let off = arena.add(
            &[
                crate::literal::Literal::positive(crate::literal::Variable(0)),
                crate::literal::Literal::positive(crate::literal::Variable(1)),
            ],
            true,
        );
        assert_eq!(arena.two_stage_score(off), 0, "born at the arena default");
        arena.set_used(off, crate::clause_arena::MAX_USED);
        for value in [1u16, 31, 32, 255, 256, 4096, u16::MAX] {
            arena.set_two_stage_score(off, value);
            assert_eq!(arena.two_stage_score(off), value);
            assert_eq!(
                arena.used(off),
                crate::clause_arena::MAX_USED,
                "the wide score must not alias the 5-bit `used` field"
            );
            assert_eq!(arena.len_of(off), 2, "nor the literal count");
            assert!(arena.is_learned(off), "nor the flags");
        }
        arena.set_two_stage_score(off, 300);
        arena.decay_two_stage_score(off);
        assert_eq!(arena.two_stage_score(off), 299);
        arena.set_two_stage_score(off, 0);
        arena.decay_two_stage_score(off);
        assert_eq!(arena.two_stage_score(off), 0, "decay saturates at zero");
    }
}
