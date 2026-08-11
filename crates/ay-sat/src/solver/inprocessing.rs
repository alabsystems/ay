// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Inprocessing techniques: vivification, subsumption, probing, BVE, BCE, transitive reduction, HTR, gate extraction, SAT sweeping.
//!
//! # DRAT Proof Compatibility
//!
//! When proof logging is enabled (`proof_manager.is_some()`), each technique
//! either emits valid DRAT add/delete records or is disabled:
//!
//! | Technique        | DRAT Status | Notes |
//! |------------------|-------------|-------|
//! | BVE              | Emits       | Add resolvents, delete originals |
//! | BCE              | Emits       | Delete blocked clauses |
//! | Subsumption      | Emits       | Delete subsumed clauses |
//! | Vivification     | Emits       | Add strengthened, delete original |
//! | Transred         | Emits       | Delete redundant binary clauses |
//! | HTR              | Emits       | Delete hyper-binary resolvable clauses |
//! | Probing          | Emits       | Add failed-literal units |
//! | Conditioning     | Emits       | Delete globally blocked clauses via `delete_clause_checked` |
//! | Congruence       | Emits       | Add equivalence binaries, delete/replace rewritten |
//! | Factorization    | Emits (DRAT) | Divider+blocked+quotient per application; LRAT skipped |
//! | SAT Sweeping     | Disabled    | Sweep equivalences are not RUP/RAT-derivable in proof modes |
//! | SCC Decompose    | Emits       | Delete/replace rewritten, add units |

use super::mutate::{DeleteResult, ReasonPolicy, ReplaceResult};
use super::*;

/// Minimum irredundant clause count before enabling random-k-SAT skip heuristics.
///
/// Small formulas can accidentally look "uniform" while still being highly
/// structured (for example, hand-crafted XOR encodings). Use a conservative
/// floor so we only skip gate/BVE passes on large, likely-random instances.
pub(crate) const RANDOM_KSAT_MIN_CLAUSES: usize = 128;
const FACTOR_TICK_THRESHOLD: u64 = 7;
const HTR_TICK_THRESHOLD: u64 = 6;
/// CaDiCaL options.hpp: `backbonethresh = 5`. Raised to 8 (#8078): AY's
/// CDCL-based backbone is more expensive than CaDiCaL's binary-clause approach.
/// Higher threshold reduces frequency of unproductive backbone attempts.
const BACKBONE_TICK_THRESHOLD: u64 = 8;
/// CaDiCaL options.hpp: `sweepthresh = 5`. Raised to 8 (#8078): sweep is
/// expensive (600ms+ per round on FmlaEquivChain) and frequently unproductive.
/// Higher threshold reduces frequency without disabling sweep entirely.
const SWEEP_TICK_THRESHOLD: u64 = 8;
/// Tick-proportional scheduling threshold for vivification.
///
/// CaDiCaL options.hpp: `vivifythresh = 20`. Now that AY's tick accounting
/// matches CaDiCaL (ticks/conflict ~1459 vs ~1473), we use CaDiCaL's native
/// value. Prior workaround of threshold=1 compensated for 10x undercount
/// that was fixed in #8148. (#8188)
const VIVIFY_TICK_THRESHOLD: u64 = 20;
/// CaDiCaL options.hpp: `probethresh = 0` — probing has no tick threshold in CaDiCaL.
/// Setting to 0 means the threshold gate is always satisfied (no-op).
const PROBE_TICK_THRESHOLD: u64 = 0;
/// Tick-proportional scheduling threshold for subsumption (#8148).
/// CaDiCaL does not gate subsumption with a tick threshold, but adding one
/// prevents redundant calls when search ticks haven't advanced enough.
const SUBSUME_TICK_THRESHOLD: u64 = 2;
/// CaDiCaL options.hpp: BVE (elim) has no tick threshold — uses fixpoint guards instead.
/// Setting to 0 means the threshold gate is always satisfied (no-op).
const BVE_TICK_THRESHOLD: u64 = 0;
/// Tick-proportional scheduling threshold for transitive reduction (#8148).
/// CaDiCaL does not gate transred with a tick threshold, but adding one
/// prevents redundant calls when search ticks haven't advanced enough.
const TRANSRED_TICK_THRESHOLD: u64 = 2;
/// Tick-proportional scheduling threshold for blocked clause elimination (#8148).
/// CaDiCaL does not gate BCE with a tick threshold, but adding one
/// prevents redundant calls when search ticks haven't advanced enough.
const BCE_TICK_THRESHOLD: u64 = 2;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum ProbeSkipReason {
    DisabledFlag,
    IntervalNotDue,
    ThresholdDelay,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum SubsumeSkipReason {
    DisabledFlag,
    IntervalNotDue,
    ThresholdDelay,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum BveSkipReason {
    DisabledFlag,
    IntervalNotDue,
    FixpointGuard,
    ThresholdDelay,
    /// BVE inflated the clause DB in a previous phase (#8135).
    ClauseGrowthGuard,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum TransredSkipReason {
    DisabledFlag,
    IntervalNotDue,
    ThresholdDelay,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum BceSkipReason {
    DisabledFlag,
    IntervalNotDue,
    ThresholdDelay,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum FactorSkipReason {
    DisabledFlag,
    IntervalNotDue,
    DelayGuard,
    ThresholdDelay,
    NoNewMarks,
}

impl FactorSkipReason {
    /// Dense index for per-reason counting.
    pub(super) fn index(self) -> usize {
        match self {
            Self::DisabledFlag => 0,
            Self::IntervalNotDue => 1,
            Self::DelayGuard => 2,
            Self::ThresholdDelay => 3,
            Self::NoNewMarks => 4,
        }
    }

    /// Stable tag for `--stats`, in `index()` order.
    pub(super) const TAGS: [&'static str; FactorSkipReason::COUNT] =
        ["disabled", "interval", "delay", "threshold", "no-marks"];

    pub(super) const COUNT: usize = 5;
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum HtrSkipReason {
    DisabledFlag,
    IntervalNotDue,
    ThresholdDelay,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum BackboneSkipReason {
    DisabledFlag,
    IntervalNotDue,
    ThresholdDelay,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum SweepSkipReason {
    DisabledFlag,
    IntervalNotDue,
    ThresholdDelay,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) enum VivifySkipReason {
    DisabledFlag,
    IntervalNotDue,
    ThresholdDelay,
    SmallDenseSkip,
}

#[derive(Debug, Default, Clone, Copy)]
struct VivifyTierRun {
    processed: u64,
    strengthened: u64,
    enqueued_units: bool,
    conflict: bool,
}

impl VivifyTierRun {
    #[inline]
    fn is_low_yield(self) -> bool {
        self.processed == 0 || self.strengthened.saturating_mul(100) < self.processed
    }
}

mod accessors;
mod backbone;
mod bce;
mod bve;
pub(crate) use bve::BveBodyScratch;
mod cce;
mod component;
mod condition;
mod congruence;
mod decompose;
#[cfg(test)]
pub(crate) use decompose::FMLA_MAIN_LRAT_PREFLIGHT_MAX_PROOF_ROWS;
mod deduplicate;
mod factorize;
mod htr;
mod instantiate;
mod sbva;
#[cfg(test)]
pub(super) use instantiate::InstCandidate;
mod intree;
mod probe;
mod reorder;
mod subsume;
mod sweep;
mod transred;
mod vivify;

impl Solver {
    /// Level-0 garbage collection: remove satisfied clauses and root-false literals.
    ///
    /// CaDiCaL equivalent: `mark_satisfied_clauses_as_garbage()` +
    /// `remove_falsified_literals()` in `collect.cpp`. This ensures all
    /// inprocessing techniques (especially HTR) operate on clauses without
    /// stale level-0 false literals (#3971).
    ///
    /// Fixpoint guard: skips if no new level-0 assignments since last collection.
    /// Returns true if UNSAT detected (empty clause derived).
    ///
    /// REQUIRES: called at decision level 0 (level-0 assignments are permanent)
    /// ENSURES: no active clause is satisfied at level 0,
    ///          no active clause contains a level-0 false literal
    /// Lightweight level-0 garbage collection for large bit-blasted formulas.
    ///
    /// Skips clause modification entirely. The two-watch invariant handles
    /// stale false literals correctly during search, and satisfied clauses
    /// are inert (both watched literals are true, so BCP never visits them).
    ///
    /// Full GC on 1M+ clause formulas costs 12s+ due to per-clause watch
    /// removal/re-addition for satisfied clause deletion. This skip saves
    /// that overhead when expensive preprocessing (congruence, decompose)
    /// is already bypassed.
    ///
    /// Returns true if UNSAT detected (all-false clause found).
    pub(super) fn collect_level0_garbage_lightweight(&mut self) -> bool {
        debug_assert_eq!(
            self.decision_level, 0,
            "BUG: collect_level0_garbage_lightweight at decision level {}",
            self.decision_level,
        );
        if self.fixed_count == self.cold.last_collect_fixed {
            return false;
        }

        // Quick scan: only check for all-false clauses (UNSAT detection).
        // Do NOT delete satisfied clauses or remove false literals.
        //
        // Occ-guided path (#8097): when gc_occ is available, only check
        // clauses containing a newly-falsified literal (negation of a new
        // level-0 unit). A clause can only become all-false if it contains
        // such a literal. This is O(occ_count) instead of O(all_clauses).
        if let Some(ref gc_occ) = self.gc_occ {
            let arena_len = self.arena.len();
            // Collect affected clause indices from occ lists of negated new units.
            // We only care about clauses that *contain a false literal* (the negation
            // of a newly-fixed literal). Satisfied clauses are harmless in lightweight mode.
            let mut affected: Vec<usize> = Vec::new();
            for trail_pos in self.cold.last_collect_trail_pos..self.trail.len() {
                let unit_lit = self.trail[trail_pos];
                let neg_lit = unit_lit.negated();
                for &cidx in gc_occ.get(neg_lit) {
                    if cidx < arena_len {
                        affected.push(cidx);
                    }
                }
            }
            affected.sort_unstable();
            affected.dedup();
            for cidx in affected {
                if !self.arena.is_active(cidx) {
                    continue;
                }
                let clause_len = self.arena.len_of(cidx);
                if clause_len < 2 {
                    continue;
                }
                let lits = self.arena.literals(cidx);
                let mut has_non_false = false;
                for &lit in lits {
                    let val = self.lit_val(lit);
                    if val >= 0 || self.var_data[lit.variable().index()].level != 0 {
                        has_non_false = true;
                        break;
                    }
                }
                if !has_non_false {
                    return true; // All literals false at level 0 — UNSAT
                }
            }
        } else {
            // Fallback: full scan when gc_occ is not yet initialized.
            // Use arena.indices() directly to avoid collecting active_indices()
            // which allocates an O(clauses) Vec.
            for clause_idx in self.arena.indices() {
                if !self.arena.is_active(clause_idx) {
                    continue;
                }
                let clause_len = self.arena.len_of(clause_idx);
                if clause_len < 2 {
                    continue;
                }
                let lits = self.arena.literals(clause_idx);
                let mut has_non_false = false;
                for &lit in lits {
                    let val = self.lit_val(lit);
                    if val >= 0 || self.var_data[lit.variable().index()].level != 0 {
                        has_non_false = true;
                        break;
                    }
                }
                if !has_non_false {
                    return true; // All literals false at level 0 — UNSAT
                }
            }
        }

        self.cold.last_collect_fixed = self.fixed_count;
        false
    }

    pub(super) fn collect_level0_garbage(&mut self) -> bool {
        // Level-0 detection relies on decision_level == 0
        debug_assert_eq!(
            self.decision_level, 0,
            "BUG: collect_level0_garbage at decision level {}",
            self.decision_level,
        );
        if self.solve_deadline_expired() || self.is_interrupted() {
            return false;
        }
        // #lra-inc-engine (S3): the incremental QF_LRA engine lane keeps the
        // arena APPEND-ONLY so every check-sat's reset stays on the
        // state-preserving incremental path. This DESTRUCTIVE sweep (deleting
        // L0-satisfied clauses / strengthening clauses with L0-false literals)
        // sets `l0_gc_modified_clause_db`, which forces `can_use_incremental_reset`
        // to fall back to a full ledger-rebuild reset — defeating cross-check-sat
        // persistence (the whole point of the lane). Skip it here, exactly as
        // scoped BVE is disabled on this lane. SOUND: L0 GC is an inprocessing
        // OPTIMIZATION, not a correctness step — BCP, `propagate_check_unsat`
        // (called right after this at the restart-inprocessing site), and the
        // non-destructive `collect_level0_garbage_lightweight` still detect any
        // real all-false-clause conflict; skipping the delete/strengthen only
        // leaves inert L0-satisfied clauses in the arena (sound, slightly larger).
        if self.cold.inc_engine_reset_mode {
            return false;
        }
        // Fixpoint guard: skip if no new level-0 assignments.
        if self.fixed_count == self.cold.last_collect_fixed {
            return false;
        }

        // Prime unit proof IDs before the loop so that the first clause scan
        // can look up direct unit IDs. In LRAT mode we also refresh inside the
        // per-clause sweep below: earlier clause rewrites in the same pass can
        // materialize new level-0 unit proofs that later explicit-only hint
        // collection needs to see immediately.
        if self.cold.lrat_enabled {
            if !self.materialize_level0_unit_proofs_interruptible() {
                return false;
            }
        }

        // Per-clause BVE occ notifications (#8364) replace the old bulk
        // any_irredundant_mutated / invalidate_occ_lists pattern (#8223).

        // Enable deferred stale-reason cleanup during L0 GC (#8140).
        // Without this, delete_clause_checked scans O(num_vars) for each
        // clause deletion to find stale reason references. For large formulas
        // (bubble_sort22: 709K vars, 2.4M clauses), this creates O(num_vars *
        // num_deletions) overhead that dominates solve time. Deferred mode
        // collects affected variables from clause literals O(clause_len) and
        // does a single cleanup pass at the end.
        self.defer_stale_reason_cleanup = true;

        // #array-deadline-forward: set when the sweep below is truncated by
        // the whole-solve deadline / interrupt. Skips the fixpoint-guard
        // update (next call resumes) and the debug post-conditions (a
        // truncated pass legitimately leaves satisfied clauses behind).
        let mut deadline_truncated = false;

        loop {
            self.ensure_reason_clause_marks_current();

            // ── gc_occ rebuild (#8078, #8466) ─────────────────────────────
            // Build a fresh occ list each fixpoint pass for occ-guided
            // affected-set construction. The occ list is dropped immediately
            // after collecting the affected clause set so that the subsequent
            // replace_clause_impl / delete_clause_checked calls see
            // gc_occ = None and skip per-clause occ maintenance. On small
            // dense formulas (clique_n2_k10: 180 vars, 3160 clauses), the
            // per-replacement gc_occ remove+add was the dominant cost (38%
            // of runtime in replace_clause_impl). Moving the rebuild inside
            // the loop and dropping before mutations eliminates this.
            {
                // live_indices (husk adjudication #3): garbage-kept husks must
                // not enter the L0-GC affected set — the strengthen path would
                // route them into replace_clause_* (now also guarded at the
                // sink) and the satisfied path would double-delete them.
                //
                // Reuse a persistent occ-only allocation instead of allocating
                // a fresh OccList every pass/solve. Only `get()` is called on
                // gc_occ before it is dropped (below), so the pos_map position
                // index is never read here — building it was the dominant
                // HashMap insert+reserve_rehash cost on million-clause hard
                // MaxSAT parts. `new_occ_only` skips it entirely; `clear()`
                // retains the occ vec capacity so subsequent rebuilds do not
                // regrow. A cleared occ-only list is behaviorally identical to
                // a fresh `OccList::new` for the `get()`-only use here.
                let mut occ = self
                    .gc_occ_scratch
                    .take()
                    .unwrap_or_else(|| crate::occ_list::OccList::new_occ_only(self.num_vars));
                occ.clear();
                occ.ensure_num_vars(self.num_vars);
                for idx in self.arena.live_indices() {
                    if self.arena.len_of(idx) >= 2 {
                        let lits = self.arena.literals(idx);
                        occ.add_clause(idx, lits);
                    }
                }
                self.gc_occ = Some(occ);
            }

            // ── Occ-guided affected-set construction (#8097) ───────────────
            // For each new level-0 unit literal `l` on the trail since the
            // last GC pass, clauses containing `l` are satisfied (delete) and
            // clauses containing `~l` contain a false literal (strengthen).
            // Collect affected clause indices directly from gc_occ, sort, and
            // deduplicate — O(affected * log(affected)) instead of the prior
            // O(arena_len) bitset allocation + O(all_clauses) filter scan.
            // Always rescan from trail position 0 (#8078). Incremental
            // trail_start tracking (last_collect_trail_pos) misses clauses
            // added to gc_occ AFTER the last pass that contain already-false
            // level-0 literals: those trail entries were already "processed"
            // but the new clauses weren't part of gc_occ at that time.
            // Cost: O(level0_units * avg_occ_len) per call — typically small
            // since level-0 units are few and the gc_occ lookup is O(1).
            let trail_start = 0;
            let trail_end = self.trail.len();

            // Collect affected clause indices directly from occ lists.
            let arena_len = self.arena.len();
            let mut active: Vec<usize> = Vec::new();

            if let Some(ref gc_occ) = self.gc_occ {
                for trail_pos in trail_start..trail_end {
                    let unit_lit = self.trail[trail_pos];
                    // Clauses containing unit_lit are satisfied → delete
                    for &cidx in gc_occ.get(unit_lit) {
                        if cidx < arena_len {
                            active.push(cidx);
                        }
                    }
                    // Clauses containing ~unit_lit have a false literal → strengthen
                    let neg_lit = unit_lit.negated();
                    for &cidx in gc_occ.get(neg_lit) {
                        if cidx < arena_len {
                            active.push(cidx);
                        }
                    }
                }
            }

            // Safety net for small formulas (#8870): occurrence-guided lookup is
            // the hot path for large bit-blasted instances, but small formulas can
            // afford a conservative full scan. This catches clauses introduced or
            // rewritten between L0-GC passes that already contain old level-0
            // literals and therefore may not be reached by the optimized affected
            // set in every schedule.
            const SMALL_FORMULA_L0_GC_FULL_SCAN_WORDS: usize = 100_000;
            if arena_len <= SMALL_FORMULA_L0_GC_FULL_SCAN_WORDS {
                // live_indices (husk adjudication #3): exclude garbage-kept
                // husks from the full-scan affected set, same as the occ path.
                for cidx in self.arena.live_indices() {
                    if self.arena.len_of(cidx) < 2 {
                        continue;
                    }
                    if self.arena.literals(cidx).iter().any(|&lit| {
                        self.lit_val(lit) != 0 && self.var_data[lit.variable().index()].level == 0
                    }) {
                        active.push(cidx);
                    }
                }
            }

            // Drop gc_occ before clause mutations (#8466). The affected set
            // is already collected; the subsequent delete/replace calls no
            // longer need occ-guided lookup. Setting gc_occ = None makes all
            // `if let Some(ref mut gc_occ)` guards in replace_clause_impl
            // and delete_clause_observed become no-ops, avoiding O(clause_len
            // * occ_list_len) work per mutation. Move the allocation into the
            // reuse scratch instead of dropping it so the next pass/solve
            // reuses its capacity (see gc_occ_scratch). `take()` leaves
            // gc_occ = None, preserving the guard-disabling behavior exactly.
            self.gc_occ_scratch = self.gc_occ.take();

            // Update trail position for next pass iteration.
            self.cold.last_collect_trail_pos = trail_end;

            // If no affected clauses, skip the expensive per-clause scan.
            if active.is_empty() {
                break;
            }

            // Sort for arena-order iteration (required for LRAT proof chain
            // ordering) and deduplicate.
            active.sort_unstable();
            active.dedup();
            // Filter to live clauses only (deleted clauses may still be in occ
            // lists). Use !is_dead() rather than is_active(): is_active() only
            // checks lit_len_raw != 0 and passes garbage-kept husks, which the
            // strengthen path below would revive via replace (#8497 family,
            // husk adjudication #3).
            active.retain(|&idx| !self.arena.is_dead(idx));
            let mut new_lits: Vec<Literal> = Vec::new();
            let mut falsified_unit_ids: Vec<u64> = Vec::new();
            let mut pass_mutated = false;
            let trail_len_before = self.trail.len();

            let mut sweep_tick: u32 = 0;
            for clause_idx in active {
                // #array-deadline-forward: amortized whole-solve deadline /
                // interrupt poll. Each iteration deletes or strengthens one
                // clause with O(watchlist) `remove_watch` cost — on a grown
                // clause DB this sweep was measured running 12+s past the
                // caller's wall budget (QF_AX subset re-solves; the caller's
                // `should_stop` never reaches this pre-search phase).
                // FAIL-CLOSED truncation: L0 GC is an inprocessing
                // OPTIMIZATION, not a correctness step (see the
                // inc_engine_reset_mode skip above) — stopping between
                // clause mutations leaves inert satisfied clauses / stale
                // false literals that the two-watch invariant handles.
                // `last_collect_fixed` is NOT updated on truncation so the
                // next call resumes the sweep, and the satisfied/false
                // post-conditions are skipped for the truncated pass.
                sweep_tick = sweep_tick.wrapping_add(1);
                if sweep_tick & 15 == 0 && (self.solve_deadline_expired() || self.is_interrupted())
                {
                    deadline_truncated = true;
                    break;
                }
                let clause_len = self.arena.len_of(clause_idx);
                if clause_len < 2 {
                    continue;
                }

                if self.cold.lrat_enabled {
                    if !self.materialize_level0_unit_proofs_interruptible() {
                        deadline_truncated = true;
                        break;
                    }
                }

                // Scan literals for level-0 assignments. Literals are copied into
                // new_lits; the immutable borrow on clause_db ends before mutation.
                let lits = self.arena.literals(clause_idx);
                let mut satisfied = false;
                new_lits.clear();
                falsified_unit_ids.clear();

                for &lit in lits {
                    let val = self.lit_val(lit);
                    if val > 0 && self.var_data[lit.variable().index()].level == 0 {
                        // Literal true at level 0 — clause is satisfied.
                        satisfied = true;
                        break;
                    }
                    if val < 0 && self.var_data[lit.variable().index()].level == 0 {
                        // Literal false at level 0 — drop from clause.
                        // CaDiCaL Proof::flush_clause: collect unit_id(-lit) for
                        // each falsified literal directly (#7108).
                        if self.cold.lrat_enabled {
                            if let Some(pid) = self.level0_var_proof_id_for_lit(lit.negated()) {
                                if !falsified_unit_ids.contains(&pid) {
                                    falsified_unit_ids.push(pid);
                                }
                            }
                        }
                        continue;
                    }
                    new_lits.push(lit);
                }

                if satisfied {
                    // CaDiCaL: mark_garbage() for satisfied clauses.
                    // Use ClearLevel0 so level-0 reason references don't block deletion.
                    //
                    // LRAT guard (#5028): When LRAT is enabled, reason clauses must
                    // stay alive. ClearLevel0 saves the LRAT clause ID into
                    // level0_proof_id before deletion, but also emits an LRAT 'd'
                    // (delete) step. Later, append_lrat_unit_chain references
                    // level0_proof_id as a hint — pointing at a clause the checker
                    // considers deleted. Skipping deletion keeps the proof valid.
                    // The clause remains inert (satisfied, won't propagate) but its
                    // LRAT ID stays live for future proof chains.
                    if self.cold.lrat_enabled && self.is_reason_clause_marked(clause_idx) {
                        continue;
                    }
                    // Per-clause BVE occ notification (#8364): snapshot literals
                    // before deletion and notify BVE incrementally. Guard on
                    // DeleteResult::Deleted to avoid corrupting occ lists when
                    // delete_clause_checked returns Skipped.
                    let is_irredundant = !self.arena.is_learned(clause_idx);
                    let old_lits_snapshot = if is_irredundant {
                        Some(self.arena.literals(clause_idx).to_vec())
                    } else {
                        None
                    };
                    let delete_result =
                        self.delete_clause_checked(clause_idx, ReasonPolicy::ClearLevel0);
                    if is_irredundant && matches!(delete_result, DeleteResult::Deleted) {
                        self.note_irredundant_clause_removed_for_bve(
                            clause_idx,
                            old_lits_snapshot
                                .as_deref()
                                .expect("irredundant L0-satisfied clause snapshot"),
                        );
                    }
                    pass_mutated = true;
                    // #8375: Use l0_gc_modified_clause_db instead of
                    // inprocessing_modified_clause_db. L0 GC only deletes
                    // satisfied clauses — learned clauses derived under the
                    // original (non-BVE-simplified) clause set are safe to
                    // preserve across the rebuild.
                    self.cold.l0_gc_modified_clause_db = true;
                    continue;
                }

                if new_lits.len() < clause_len {
                    // All literals false at level 0 → clause unsatisfied → UNSAT.
                    if new_lits.is_empty() {
                        return true;
                    }
                    // Per-clause BVE occ notification (#8364): snapshot old literals
                    // before strengthening so the occ list can be updated incrementally.
                    let is_irredundant = !self.arena.is_learned(clause_idx);
                    let old_lits_for_bve = if is_irredundant {
                        Some(self.arena.literals(clause_idx).to_vec())
                    } else {
                        None
                    };
                    // CaDiCaL Proof::flush_clause starts from the direct
                    // unit IDs of falsified literals, but AY still needs the
                    // ordinary transitive level-0 LRAT chain here when one of
                    // those units depends on earlier root implications in the
                    // same sweep. Keep the direct unit IDs as explicit seeds
                    // and let replace_clause_checked_with_lrat_hints extend
                    // them as needed.
                    let result = if self.cold.lrat_enabled && !falsified_unit_ids.is_empty() {
                        self.replace_clause_checked_with_lrat_hints(
                            clause_idx,
                            &new_lits,
                            &falsified_unit_ids,
                        )
                    } else {
                        self.replace_clause_checked(clause_idx, &new_lits)
                    };
                    match result {
                        ReplaceResult::Empty => return true,
                        ReplaceResult::Unit | ReplaceResult::Replaced => {
                            pass_mutated = true;
                            // #8375: clause strengthened by L0 GC (false literal
                            // removal). Use l0_gc_modified_clause_db so the rebuild
                            // preserves learned clauses.
                            self.cold.l0_gc_modified_clause_db = true;
                            // Per-clause BVE occ notification (#8364).
                            if let Some(ref old_lits) = old_lits_for_bve {
                                self.note_irredundant_clause_replaced_for_bve(
                                    clause_idx, old_lits, &new_lits,
                                );
                            }
                        }
                        ReplaceResult::Skipped => {}
                    }
                }
            }

            if self.propagate_check_unsat() {
                return true;
            }

            // #array-deadline-forward: a truncated sweep must not iterate
            // the fixpoint — exit after the (sound) propagate check above.
            if deadline_truncated {
                break;
            }

            let trail_grew = self.trail.len() > trail_len_before;
            if !pass_mutated && !trail_grew {
                break;
            }
        }

        // Flush deferred stale reason cleanup (#8140).
        self.defer_stale_reason_cleanup = false;
        self.clear_stale_reasons();

        // Shadow-mode verification (#8364) removed from L0 GC (#8473):
        // BVE occ lists are only guaranteed consistent immediately after
        // refresh_incremental() at the start of each BVE round. Between
        // BVE rounds, CDCL search and inprocessing techniques may modify
        // the clause database without per-clause BVE occ notification.
        // The authoritative verification point is in bve_body() after
        // refresh_incremental/rebuild_with_vals.

        // #array-deadline-forward: only arm the fixpoint guard after a
        // COMPLETE sweep — a truncated pass must be resumed by the next call.
        if !deadline_truncated {
            self.cold.last_collect_fixed = self.fixed_count;
        }

        // Drop gc_occ after the fixpoint loop completes (#8466).
        // gc_occ is only needed DURING collect_level0_garbage's fixpoint loop
        // for efficient occ-guided clause scanning. Between calls, all the
        // incremental gc_occ maintenance in delete_clause_observed (reduce_db
        // path) and replace_clause_impl (subsumption path) is pure waste:
        // gc_occ gets fully rebuilt from scratch at the start of each call
        // (lines 318-326 above). On small dense formulas like clique_n2_k10
        // (180 vars, 3160 clauses), this wasted maintenance consumed 70% of
        // runtime (39% in replace_clause_impl, 31% in delete_clause_observed).
        // Setting gc_occ = None makes all `if let Some(ref mut gc_occ)` guards
        // in those paths become no-ops. The mark_satisfied_clauses_as_garbage
        // fallback path (full scan) is acceptable when gc_occ is absent.
        self.gc_occ = None;

        // Post-condition: no active clause should be satisfied at level 0.
        // Non-LRAT runs should also remove level-0 false literals. In LRAT mode,
        // proof-completeness can force a replacement to be skipped when the
        // signed unit chain is unavailable; the two-watch invariant still handles
        // those stale false literals during search (#8870).
        // Exception: LRAT-protected reason clauses may remain satisfied (#5028).
        // #array-deadline-forward: skipped after a deadline-truncated sweep —
        // unprocessed satisfied clauses are expected then (see the sweep poll).
        #[cfg(debug_assertions)]
        if !deadline_truncated {
            // Arena integrity pre-check: validate all active clauses have in-range
            // literals before the GC post-condition check. If this fires, the arena
            // is corrupt (ArenaIter misalignment, stale shrink_map, etc.) and the
            // GC assertion below would fire on garbage data. (#8078)
            for idx in self.arena.active_indices() {
                let len = self.arena.len_of(idx);
                if len < 2 {
                    continue;
                }
                for (i, &lit) in self.arena.literals(idx).iter().enumerate() {
                    assert!(
                        lit.variable().index() < self.num_vars,
                        "BUG: arena integrity check BEFORE GC post-condition: \
                         clause at offset {idx} (len={len}) has out-of-range \
                         literal[{i}] raw={} (var={}, num_vars={}). \
                         This is arena corruption, not a GC bug. \
                         Raw header: w0=0x{:08x} w1=0x{:08x} w2=0x{:08x} w3=0x{:08x} w4=0x{:08x}",
                        lit.raw(),
                        lit.variable().index(),
                        self.num_vars,
                        self.arena.raw_word(idx, 0),
                        self.arena.raw_word(idx, 1),
                        self.arena.raw_word(idx, 2),
                        self.arena.raw_word(idx, 3),
                        self.arena.raw_word(idx, 4),
                    );
                }
            }

            self.ensure_reason_clause_marks_current();
            // live_indices (husk adjudication #3): the satisfied/false-literal
            // post-conditions apply to the LIVE formula only. Garbage-kept
            // husks are logically deleted and deliberately excluded from the
            // L0-GC affected set, so a satisfied husk is expected here.
            for idx in self.arena.live_indices() {
                let off_header = idx;
                if self.arena.is_empty_clause(off_header) || self.arena.len_of(off_header) < 2 {
                    continue;
                }
                // LRAT-protected reason clauses are exempt from the satisfied check.
                if self.cold.lrat_enabled && self.is_reason_clause_marked(idx) {
                    continue;
                }
                for &lit in self.arena.literals(idx) {
                    assert!(
                        lit.variable().index() < self.num_vars,
                        "BUG: collect_level0_garbage post-check: clause at offset {idx} \
                         (len={}) contains out-of-range literal raw={} (var={}, num_vars={}). \
                         Arena corruption: header word0=0x{:08x}, word1=0x{:08x}, word2=0x{:08x}",
                        self.arena.len_of(idx),
                        lit.raw(),
                        lit.variable().index(),
                        self.num_vars,
                        self.arena.raw_word(idx, 0),
                        self.arena.raw_word(idx, 1),
                        self.arena.raw_word(idx, 2),
                    );
                    let val = self.lit_val(lit);
                    let lvl = self.var_data[lit.variable().index()].level;
                    debug_assert!(
                        !(val > 0 && lvl == 0),
                        "BUG: collect_level0_garbage left satisfied clause {idx} \
                         (lit {lit:?} true at level 0)"
                    );
                    if val < 0 && lvl == 0 {
                        if self.cold.lrat_enabled {
                            continue;
                        }
                        // Diagnostic: why did the GC miss this clause?
                        let clause_lits = self.arena.literals(idx);
                        let in_gc_occ = if let Some(ref gc_occ) = self.gc_occ {
                            gc_occ.get(lit).contains(&idx)
                                || gc_occ.get(lit.negated()).contains(&idx)
                        } else {
                            false
                        };
                        panic!(
                            "BUG: collect_level0_garbage left false literal {lit:?} \
                             (var={}, raw={}) at level 0 in clause {idx} (len={}). \
                             Clause literals: {:?}. \
                             In gc_occ for this lit? {in_gc_occ}. \
                             gc_occ exists? {}. \
                             last_collect_trail_pos={}, trail_len={}. \
                             fixed_count={}, last_collect_fixed={}",
                            lit.variable().index(),
                            lit.raw(),
                            clause_lits.len(),
                            clause_lits
                                .iter()
                                .map(|l| (l.variable().index(), l.is_positive(), l.raw()))
                                .collect::<Vec<_>>(),
                            self.gc_occ.is_some(),
                            self.cold.last_collect_trail_pos,
                            self.trail.len(),
                            self.fixed_count,
                            self.cold.last_collect_fixed,
                        );
                    }
                }
            }
        }

        false
    }

    /// Remove a watch for a clause from a literal's watch list
    pub(super) fn remove_watch(&mut self, lit: Literal, clause_ref: ClauseRef) {
        let mut list = self.watches.get_watches_mut(lit);
        // Defensive: a buggy inprocessing pass can leave duplicate watchers behind.
        // Remove all occurrences to avoid stale watches corrupting propagation/transred.
        let target = clause_ref.0;
        let mut i = 0;
        while i < list.len() {
            if list.clause_ref(i).0 == target {
                list.swap_remove(i);
            } else {
                i += 1;
            }
        }
    }

    /// Remove both watches for a clause from the watch lists of its two
    /// watched literals.
    ///
    /// Used by incremental watch maintenance in `apply_decompose_mutation`
    /// to detach watches before a clause is deleted or replaced (#8093).
    pub(super) fn detach_clause_watches(
        &mut self,
        clause_ref: ClauseRef,
        lit0: Literal,
        lit1: Literal,
    ) {
        self.remove_watch(lit0, clause_ref);
        self.remove_watch(lit1, clause_ref);
    }

    /// Finalize watch state after incremental watch maintenance.
    ///
    /// Performs the same qhead rewinding and debug assertions as
    /// `rebuild_watches()`, but WITHOUT clearing and re-building all watches
    /// from scratch. Call this after decompose/sweep when watches have been
    /// maintained incrementally by `apply_decompose_mutation()` (#8093).
    ///
    /// This is the incremental counterpart to `rebuild_watches()`. While
    /// `rebuild_watches()` is used for BVE (which disconnects all watches
    /// and operates on occurrence lists), `finalize_incremental_watches()`
    /// is used by techniques that make targeted clause mutations while 2WL
    /// watches remain connected:
    /// - **Decompose:** rewrites clauses via SCC-based equivalence substitution
    /// - **Sweep:** rewrites clauses via SAT-sweeping equivalence detection
    pub(super) fn finalize_incremental_watches(&mut self) {
        // Binary-first invariant is maintained incrementally via push_watcher.
        self.watches.debug_assert_binary_first();

        // Re-propagate assignments against the updated watch graph.
        // Minimal trail rewind (#8095): at level 0, use earliest_affected_trail_pos
        // to avoid re-propagating the entire trail when only a few positions changed.
        // At higher levels (rare during inprocessing), rewind to level start.
        self.apply_minimal_trail_rewind();

        // Shadow-mode checks (#8093): after incremental maintenance, the watch
        // state should be equivalent to what rebuild_watches() would produce.
        // These checks catch bugs in the incremental detach/attach logic that
        // would otherwise manifest as non-deterministic missed propagations.
        #[cfg(debug_assertions)]
        {
            // Forward check: every active non-garbage clause with len >= 2 must
            // have watches on its first two literals. Missing watches cause missed
            // propagations — a soundness bug.
            for idx in self.arena.active_indices() {
                let off_header = idx;
                if self.arena.is_empty_clause(off_header)
                    || self.arena.len_of(off_header) < 2
                    || self.arena.is_garbage(off_header)
                    || self.arena.is_pending_garbage(off_header)
                {
                    continue;
                }
                let cref = ClauseRef(idx as u32);
                let lit0 = self.arena.literal(idx, 0);
                let lit1 = self.arena.literal(idx, 1);
                debug_assert!(
                    {
                        let w0 = self.watches.get_watches(lit0);
                        let w1 = self.watches.get_watches(lit1);
                        (0..w0.len()).any(|i| w0.clause_ref(i) == cref)
                            && (0..w1.len()).any(|i| w1.clause_ref(i) == cref)
                    },
                    "BUG: finalize_incremental_watches: active clause {idx} (len={}) \
                     missing watch on lit0={lit0:?} or lit1={lit1:?}",
                    self.arena.len_of(off_header)
                );
            }

            // Reverse check for binary watches: every binary watch entry must
            // reference an active clause. Binary watches are eagerly removed on
            // deletion (delete_binary_clause_watches), so stale binary entries
            // indicate a bug in the incremental detach logic. Long-clause watches
            // are lazily filtered during BCP (flush_watches), so stale long-clause
            // entries are expected and harmless.
            for vi in 0..self.num_vars {
                for sign in [true, false] {
                    let lit = if sign {
                        Literal::positive(Variable(vi as u32))
                    } else {
                        Literal::negative(Variable(vi as u32))
                    };
                    let wl = self.watches.get_watches(lit);
                    for wi in 0..wl.len() {
                        if !wl.is_binary(wi) {
                            continue;
                        }
                        let cref = wl.clause_ref(wi);
                        let cidx = cref.0 as usize;
                        debug_assert!(
                            cidx < self.arena.len() && self.arena.is_active(cidx),
                            "BUG: finalize_incremental_watches: stale binary watch on \
                             lit={lit:?} → clause {cidx} (active={})",
                            cidx < self.arena.len() && self.arena.is_active(cidx),
                        );
                    }
                }
            }
        }

        self.earliest_affected_trail_pos = None;
    }

    /// Incremental watch reconnection after BVE (#8093).
    ///
    /// Replaces the `watches.clear()` + `rebuild_watches()` pattern with:
    /// 1. **Purge stale binary watch entries**: BVE deletes clauses while
    ///    `watches_disconnected=true`, so binary watches for deleted clauses
    ///    remain in watch lists. Binary watches are NOT lazily filtered by BCP
    ///    (#4924), so stale entries are a soundness bug. Scan all watch lists
    ///    and remove binary entries pointing to dead clauses via `retain_lit`.
    /// 2. **Attach watches for new clauses**: Iterate clauses at arena offsets
    ///    >= `arena_baseline` (resolvents added by BVE). Reorder literals and
    ///    > attach 2WL watch entries.
    /// 3. **Flush stale long-clause watches**: Clear dirty watch state so BCP
    ///    lazily filters any remaining stale long-clause entries.
    /// 4. **Trail rewind**: Apply minimal trail rewind for re-propagation.
    ///
    /// Cost: O(watch_entries + new_clauses) instead of O(all_clauses).
    /// Pre-existing long-clause watches for surviving clauses are kept when
    /// they match the clause's current watched literals. Stale entries (from
    /// clause strengthening that moved watched positions) are purged.
    pub(super) fn reconnect_bve_watches(&mut self, arena_baseline: usize) {
        let reconnect_start = ay_core::time::Instant::now();
        self.stats.clear_bcp_learned_1963_blocker_certs();
        // When baseline is 0, all clauses get watches reattached (including
        // JIT-compiled ones), so clear the detachment flag.

        // Fast path (#8093): when BVE was a no-op (zero deletions and no new
        // clauses added), skip the expensive Phase 1 purge + Phase 2 attach.
        // The watch graph is unchanged. Only clear dirty state and rewind trail.
        let no_new_clauses = self.arena.len() <= arena_baseline || {
            // Arena grew but check if any new clause is actually active.
            self.arena
                .active_indices_from(arena_baseline)
                .next()
                .is_none()
        };
        if self.cold.disconnected_deletions == 0 && no_new_clauses && arena_baseline > 0 {
            // Phase 3+4 only: clear dirty state and rewind trail.
            self.dirty_watches.iter_mut().for_each(|d| *d = false);
            self.dirty_watch_list.clear();
            self.watches.debug_assert_binary_first();
            self.apply_minimal_trail_rewind();

            let reconnect_elapsed_us = reconnect_start.elapsed().as_micros() as u64;
            self.stats.rebuild_watches_us = self
                .stats
                .rebuild_watches_us
                .saturating_add(reconnect_elapsed_us);
            self.stats.rebuild_watches_calls += 1;
            self.stats.incremental_reconnect_watches_us = self
                .stats
                .incremental_reconnect_watches_us
                .saturating_add(reconnect_elapsed_us);
            self.stats.incremental_reconnect_watches_calls += 1;

            let props_before = self.num_propagations;
            self.cold.post_rebuild_props_baseline = props_before;
            self.cold.post_rebuild_bcp_pending = true;
            self.cold.post_rebuild_is_full = false;

            tracing::debug!(
                arena_baseline,
                "reconnect_bve_watches: skipped (no-op BVE, zero deletions)"
            );
            return;
        }

        // Phase 1: Purge stale watch entries from all watch lists.
        //
        // During BVE with watches_disconnected=true:
        // - delete_clause_checked() skips binary watch removal (#4924)
        // - replace_clause_core() updates watches for strengthened clauses,
        //   but only when watches are intact at the time of strengthening.
        //   When instantiate() clears and rebuilds watches mid-BVE, then
        //   subsequent strengthening in later rounds may leave stale
        //   long-clause entries on old watched-literal lists.
        //
        // Purge both binary and long-clause stale entries:
        // - Binary: keep only if clause is still active in the arena.
        // - Long: keep only if clause is active AND `lit` is one of the
        //   clause's current watched literals (positions [0] or [1]).
        // Iterate ALL watch lists including extension variables from BVE/SBVA
        // beyond num_vars -- extension variables can have watch entries (#8135).
        // Track pre-existing clauses that lose a watch entry for Phase 1b.
        let total_watch_lits = self.watches.num_lists();
        let mut needs_reattach: Vec<usize> = Vec::new();
        for lit_idx in 0..total_watch_lits {
            let lit = Literal::from_index(lit_idx);
            self.watches.retain_lit(lit, |clause_raw, _blocker_raw| {
                let is_binary = clause_raw & BINARY_FLAG != 0;
                if is_binary {
                    let cidx = (clause_raw & !BINARY_FLAG) as usize;
                    // Use !is_dead() instead of is_active(): is_active() only
                    // checks lit_len_raw != 0, missing clauses marked via
                    // mark_garbage_keep_data() which set the garbage bit but
                    // preserve lit_len_raw. Stale binary watches for such
                    // clauses cause BCP to propagate eliminated variables
                    // (#8497).
                    return !self.arena.is_dead(cidx);
                }
                let cidx = clause_raw as usize;
                if self.arena.is_dead(cidx) {
                    return false;
                }
                let len = self.arena.len_of(cidx);
                if len < 2 {
                    return false;
                }
                let w0 = self.arena.literal(cidx, 0);
                let w1 = self.arena.literal(cidx, 1);
                let keep = w0 == lit || w1 == lit;
                if !keep && cidx < arena_baseline {
                    needs_reattach.push(cidx);
                }
                keep
            });
        }

        // Phase 1b: Re-attach watches for pre-existing clauses that lost
        // entries due to in-place replacement during BVE (#8135).
        if !needs_reattach.is_empty() {
            needs_reattach.sort_unstable();
            needs_reattach.dedup();
            for idx in needs_reattach {
                if self.arena.is_dead(idx) || self.arena.len_of(idx) < 2 {
                    continue;
                }
                let cref = ClauseRef(idx as u32);
                let (old_w0, old_w1) = self.arena.watched_literals(idx);
                self.remove_watch(old_w0, cref);
                self.remove_watch(old_w1, cref);
                let watched = {
                    let lits = self.arena.literals_mut(idx);
                    Self::prepare_watched_literals_with_state(
                        &self.vals,
                        &self.var_data,
                        lits,
                        WatchOrderPolicy::AssignmentScore,
                    )
                    .expect("pre-existing clause with len >= 2")
                };
                let clause_len = self.arena.len_of(idx);
                self.attach_clause_watches(cref, watched, clause_len == 2);
            }
        }

        // Phase 2: Attach watches for new clauses (resolvents from BVE).
        // Clauses at offsets >= arena_baseline were added during BVE.
        // Pre-existing clauses (< baseline) retain their original watch entries.
        //
        // CRITICAL (#8093): Some clauses >= arena_baseline may already have
        // watches from replace_clause_core() during the interleaved subsumption
        // rounds. replace_clause_core() unconditionally detaches old watches
        // and attaches new ones (it does not check watches_disconnected).
        // If we naively attach again here, we create duplicate entries that
        // cause stale-watch debug assertions during BCP (the first BCP pass
        // through a duplicate entry moves the watch, so the second entry
        // points to a clause whose watched literals no longer match).
        //
        // Fix: detach any existing watches before attaching fresh ones.
        let new_indices: Vec<usize> = self.arena.active_indices_from(arena_baseline).collect();

        for i in new_indices {
            let clause_len = self.arena.len_of(i);
            if clause_len < 2 {
                continue;
            }
            // Skip garbage/pending-garbage clauses (#8497): active_indices_from
            // only checks lit_len_raw != 0, missing clauses marked via
            // mark_garbage_keep_data() which preserve lit_len_raw but set the
            // garbage bit. Attaching watches for such clauses causes BCP to
            // propagate through dead clauses, assigning eliminated variables.
            if self.arena.is_garbage(i) || self.arena.is_pending_garbage(i) {
                continue;
            }
            // Detach any existing watches for this clause (#8093).
            // Clauses strengthened by replace_clause_core() during BVE already
            // have watch entries from the unconditional attach in replace_clause_core.
            // Remove them before re-attaching with optimal watched-literal order.
            let clause_ref = ClauseRef(i as u32);
            {
                let (old_w0, old_w1) = self.arena.watched_literals(i);
                self.remove_watch(old_w0, clause_ref);
                self.remove_watch(old_w1, clause_ref);
            }
            let watched = {
                let lits = self.arena.literals_mut(i);
                Self::prepare_watched_literals_with_state(
                    &self.vals,
                    &self.var_data,
                    lits,
                    WatchOrderPolicy::AssignmentScore,
                )
                .expect("reconnect_bve_watches: clause with len >= 2 must produce watch pair")
            };
            self.attach_clause_watches(clause_ref, watched, clause_len == 2);
        }

        // Phase 3: Clear dirty watch state.
        // BVE with watches_disconnected=true skips dirty marking
        // (mutate_delete.rs:98). Clear any pre-existing dirty state so
        // flush_watches starts clean after reconnection.
        self.dirty_watches.iter_mut().for_each(|d| *d = false);
        self.dirty_watch_list.clear();

        // Binary-first invariant is maintained by push_watcher and retain_lit.
        self.watches.debug_assert_binary_first();

        // Phase 4: Trail rewind for re-propagation.
        self.apply_minimal_trail_rewind();

        let reconnect_elapsed_us = reconnect_start.elapsed().as_micros() as u64;
        self.stats.rebuild_watches_us = self
            .stats
            .rebuild_watches_us
            .saturating_add(reconnect_elapsed_us);
        self.stats.rebuild_watches_calls += 1;
        // Incremental-reconnect-specific counters (#8103).
        self.stats.incremental_reconnect_watches_us = self
            .stats
            .incremental_reconnect_watches_us
            .saturating_add(reconnect_elapsed_us);
        self.stats.incremental_reconnect_watches_calls += 1;

        // Record post-reconnect BCP measurement baseline (#8103).
        // Mirrors the rebuild_watches() baseline setup so the next
        // propagate_check_unsat() captures cache behavior after incremental
        // reconnection, enabling comparison with the full rebuild path.
        let props_before = self.num_propagations;
        self.cold.post_rebuild_props_baseline = props_before;
        self.cold.post_rebuild_bcp_pending = true;
        self.cold.post_rebuild_is_full = false;

        // Shadow-mode debug assertions: verify watch state matches expectations.
        #[cfg(debug_assertions)]
        {
            // Forward check: every active non-garbage clause with len >= 2 must
            // have watches on its first two literals.
            for idx in self.arena.active_indices() {
                let off_header = idx;
                if self.arena.is_empty_clause(off_header)
                    || self.arena.len_of(off_header) < 2
                    || self.arena.is_garbage(off_header)
                    || self.arena.is_pending_garbage(off_header)
                {
                    continue;
                }
                let cref = ClauseRef(idx as u32);
                let lit0 = self.arena.literal(idx, 0);
                let lit1 = self.arena.literal(idx, 1);
                debug_assert!(
                    {
                        let w0 = self.watches.get_watches(lit0);
                        let w1 = self.watches.get_watches(lit1);
                        (0..w0.len()).any(|i| w0.clause_ref(i) == cref)
                            && (0..w1.len()).any(|i| w1.clause_ref(i) == cref)
                    },
                    "BUG: reconnect_bve_watches: active clause {idx} (len={}) \
                     missing watch on lit0={lit0:?} or lit1={lit1:?}",
                    self.arena.len_of(off_header)
                );
            }

            // Reverse check: no stale watch entries (binary or long) should
            // remain after reconnection (#8135).
            self.validate_watches_reverse("after reconnect_bve_watches");
        }

        self.earliest_affected_trail_pos = None;
    }

    /// Push equivalence reconstruction entries for substituted variables.
    ///
    /// For each variable where `reprs[pos] != pos`, records two equivalence
    /// clauses so `extend_model` can reconstruct the original assignment:
    ///   (repr ∨ ¬pos) with witness ¬pos
    ///   (¬repr ∨ pos) with witness pos
    ///
    /// Used by `decompose()` (reprs).
    fn push_equivalence_reconstruction(&mut self, reprs: &[Literal]) {
        // Keep the original-clause ledger immutable. Decompose may rewrite the
        // working clause DB, but `verify_against_original` must continue to
        // check the user-provided clauses as-added, not a representative-space
        // projection of them (#7432).
        for var_idx in 0..self.num_vars {
            let pos = Literal::positive(Variable(var_idx as u32));
            let repr = reprs[pos.index()];
            if repr == pos {
                continue;
            }
            let ext_pos = self.externalize(pos);
            let ext_repr = self.externalize(repr);
            self.inproc
                .reconstruction
                .push_bce(ext_pos.negated(), vec![ext_repr, ext_pos.negated()]);
            self.inproc
                .reconstruction
                .push_bce(ext_pos, vec![ext_repr.negated(), ext_pos]);
        }
    }

    /// Clear stale reason references pointing to dead clauses.
    ///
    /// Clear stale reason references after a deferred-cleanup batch.
    ///
    /// When the dirty list (`stale_reasons`) is non-empty, iterates only the
    /// collected variable indices — O(stale_count) instead of O(num_vars).
    /// Falls back to a full scan when the dirty list is empty (e.g. after
    /// watch-free BVE where per-deletion tracking was skipped entirely).
    ///
    /// Must be called after inprocessing/BVE completes but before
    /// rebuild_watches/BCP, since conflict analysis follows reason chains.
    pub(super) fn clear_stale_reasons(&mut self) {
        let mut cleared = false;

        if self.stale_reasons.is_empty() {
            // Fallback: full scan for watch-free BVE or other paths that
            // don't populate the dirty list.
            for vi in 0..self.num_vars {
                let reason = self.var_data[vi].reason;
                // #8373: Skip lazy theory reasons — their `reason` field is a
                // table index, not an arena clause offset. Treating it as an
                // arena offset would incorrectly clear valid lazy reasons.
                if is_clause_reason(reason)
                    && !self.var_data[vi].is_lazy_theory_reason()
                    && !self.arena.is_active(reason as usize)
                {
                    self.var_data[vi].reason = NO_REASON;
                    cleared = true;
                }
            }
        } else {
            // Fast path: process only dirty variables.
            for i in 0..self.stale_reasons.len() {
                let vi = self.stale_reasons[i] as usize;
                if vi < self.num_vars {
                    let reason = self.var_data[vi].reason;
                    // #8373: Skip lazy theory reasons (same guard as full-scan path).
                    if is_clause_reason(reason)
                        && !self.var_data[vi].is_lazy_theory_reason()
                        && !self.arena.is_active(reason as usize)
                    {
                        self.var_data[vi].reason = NO_REASON;
                        cleared = true;
                    }
                }
            }
            self.stale_reasons.clear();
        }

        // Debug verification: check that no ASSIGNED variable has a stale
        // reason reference. Unassigned variables (backtracked to level > 0)
        // may retain stale reason fields — these are dead data that will be
        // overwritten on re-propagation and are never dereferenced.
        #[cfg(debug_assertions)]
        {
            for vi in 0..self.num_vars {
                if !self.var_is_assigned(vi) {
                    continue;
                }
                let reason = self.var_data[vi].reason;
                // #8373: Lazy theory reasons are valid even with small `reason`
                // values that alias inactive arena offsets.
                debug_assert!(
                    !is_clause_reason(reason)
                        || self.var_data[vi].is_lazy_theory_reason()
                        || self.arena.is_active(reason as usize),
                    "BUG: clear_stale_reasons missed stale reason for assigned var {vi} \
                     (reason={reason}, active=false, level={})",
                    self.var_data[vi].level,
                );
            }
        }

        if cleared {
            // Mass-invalidate reason marks after batch stale-reason cleanup (#8100).
            self.invalidate_reason_clause_marks();
        }
    }

    /// Rebuild watched literals for all non-empty clauses.
    ///
    /// Reorders each clause's literals for optimal watch placement before
    /// re-attaching. After inprocessing, clause mutations (strengthening, BVE)
    /// may leave suboptimal literals in positions [0]/[1]. (#3812)
    ///
    /// # Why full rebuild is required for BVE (#8093)
    ///
    /// BVE operates on **occurrence lists** (every clause containing a literal),
    /// not 2-watched-literal (2WL) lists. The two data structures serve
    /// incompatible purposes: occurrence lists need complete per-literal clause
    /// sets for resolution; 2WL watches track only two literals per clause for
    /// efficient BCP. During BVE, watches are disconnected (`watches.clear()`)
    /// and must be fully rebuilt afterward. This is the standard architecture
    /// used by all major CDCL solvers:
    ///
    /// - **CaDiCaL** (`elim.cpp:1046,1127-1128`): `reset_watches()` before BVE,
    ///   `init_watches(); connect_watches();` after.
    /// - **Kissat** (`eliminate.c:587,589`): `kissat_enter_dense_mode()` before,
    ///   `kissat_resume_sparse_mode()` after.
    /// - **CaDiCaL instantiate** (`instantiate.cpp:321-322,361`): temporarily
    ///   `connect_watches()` for BCP-based instantiation, `reset_watches()` after.
    ///
    /// Maintaining 2WL watches incrementally during BVE would add O(watches)
    /// overhead to every resolvent addition and original clause deletion, with
    /// zero benefit since BCP (the only consumer of 2WL watches) does not run
    /// during BVE. The full rebuild cost is O(active_clauses) — unavoidable
    /// since every clause needs fresh watch placement.
    ///
    /// Incremental watch maintenance (via `apply_decompose_mutation` +
    /// `finalize_incremental_watches`) is used by decompose and sweep, which
    /// make targeted clause mutations while 2WL watches remain connected.
    ///
    /// # Call sites (3, all BVE-related)
    ///
    /// 1. `config_preprocess_bve.rs` — preprocessing BVE
    /// 2. `inprocessing_elimination.rs` — inprocessing BVE interleave loop
    /// 3. `inprocessing/instantiate.rs` — temporary reconnect for BCP during
    ///    post-BVE instantiation
    pub(super) fn rebuild_watches(&mut self) {
        let rebuild_start = ay_core::time::Instant::now();
        self.stats.clear_bcp_learned_1963_blocker_certs();
        // Clear all watch lists
        self.watches = WatchedLists::new(self.num_vars);
        // Full rebuild leaves no stale entries — clear dirty bits (#8101).
        self.dirty_watches.iter_mut().for_each(|d| *d = false);
        self.dirty_watch_list.clear();
        // Full rebuild reattaches all clauses including JIT-compiled ones.

        // Collect indices to avoid borrow conflict (active_indices borrows clause_db)
        let indices: Vec<usize> = self.arena.active_indices().collect();

        for i in indices {
            let clause_len = self.arena.len_of(i);
            if clause_len < 2 {
                continue;
            }
            // Skip garbage/pending-garbage clauses (#8497 family, husk
            // adjudication): active_indices only checks lit_len_raw != 0 and
            // passes garbage-kept husks. Attaching watches for a husk lets BCP
            // propagate through a logically deleted clause (mirrors the guard
            // in reconnect_bve_watches Phase 2).
            if self.arena.is_garbage_any(i) {
                continue;
            }
            let watched = {
                let lits = self.arena.literals_mut(i);
                Self::prepare_watched_literals_with_state(
                    &self.vals,
                    &self.var_data,
                    lits,
                    WatchOrderPolicy::AssignmentScore,
                )
                .expect("rebuild_watches only handles clauses with len >= 2")
            };
            let clause_ref = ClauseRef(i as u32);
            self.attach_clause_watches(clause_ref, watched, clause_len == 2);
        }

        // Binary-first invariant is maintained incrementally via push_watcher.
        self.watches.debug_assert_binary_first();

        // Snapshot propagation count before re-propagation (#8103).
        // The next propagate() call after qhead rewind uses the freshly-built
        // sequential watch layout. Comparing props/ns here vs overall BCP
        // quantifies the cache benefit of full sequential rebuild.
        let props_before = self.num_propagations;

        // Re-propagate assignments against the rebuilt watch graph.
        // Without rewinding qhead, propagate() may skip all currently assigned
        // literals and miss immediate unit/conflict consequences.
        //
        // Minimal trail rewind (#8095): at level 0, use earliest_affected_trail_pos
        // to avoid re-propagating the entire trail when only a few positions changed.
        // At higher levels (rare during inprocessing), rewind to level start.
        self.apply_minimal_trail_rewind();

        let rebuild_elapsed_us = rebuild_start.elapsed().as_micros() as u64;
        self.stats.rebuild_watches_us = self
            .stats
            .rebuild_watches_us
            .saturating_add(rebuild_elapsed_us);
        self.stats.rebuild_watches_calls += 1;
        // Full-rebuild-specific counters (#8103).
        self.stats.full_rebuild_watches_us = self
            .stats
            .full_rebuild_watches_us
            .saturating_add(rebuild_elapsed_us);
        self.stats.full_rebuild_watches_calls += 1;

        // Record post-rebuild BCP measurement baseline (#8103).
        // The caller's next propagate_check_unsat() call will time the BCP and
        // capture the propagation delta against this baseline.
        self.cold.post_rebuild_props_baseline = props_before;
        self.cold.post_rebuild_bcp_pending = true;
        self.cold.post_rebuild_is_full = true;

        // Shadow mode (#8095): verify that no active clause is a unit whose
        // propagation literal would be missed by the minimal qhead. A clause
        // is a "missed unit" if: (a) exactly one literal is unassigned, (b) all
        // others are false at level 0, and (c) neither watched literal is on
        // the trail at a position >= qhead (meaning BCP from qhead would not
        // visit it). Any such clause is a soundness bug in the trail tracking.
        #[cfg(debug_assertions)]
        if self.decision_level == 0 && self.earliest_affected_trail_pos.is_some() {
            let minimal_qhead = self.qhead;
            for idx in self.arena.active_indices() {
                if self.arena.is_empty_clause(idx) || self.arena.len_of(idx) < 2 {
                    continue;
                }
                // Husks are not attached by the rebuild loop (husk
                // adjudication) and are not part of the live formula — BCP
                // is not required to discover units through them.
                if self.arena.is_garbage_any(idx) {
                    continue;
                }
                let lits = self.arena.literals(idx);
                let mut unassigned_lit = None;
                let mut has_true = false;
                let mut all_others_false_l0 = true;
                for &cl in lits {
                    let v = self.lit_val(cl);
                    if v > 0 {
                        has_true = true;
                        break;
                    }
                    if v == 0 {
                        if unassigned_lit.is_some() {
                            all_others_false_l0 = false; // 2+ unassigned = not unit
                            break;
                        }
                        unassigned_lit = Some(cl);
                    } else {
                        // v < 0 (false): check level
                        let lvl = self.var_data[cl.variable().index()].level;
                        if lvl != 0 {
                            all_others_false_l0 = false;
                            break;
                        }
                    }
                }
                // A unit clause: exactly one unassigned literal, rest false at level 0.
                if !has_true && all_others_false_l0 {
                    if let Some(unit_lit) = unassigned_lit {
                        // This literal must be reachable from qhead via BCP.
                        // BCP scans watches on trail[qhead..]. The unit is
                        // reachable if either watched literal's negation is
                        // on the trail at position >= minimal_qhead.
                        let w0 = self.arena.literal(idx, 0);
                        let w1 = self.arena.literal(idx, 1);
                        let w0_neg_pos = if self.lit_val(w0.negated()) > 0 {
                            None // w0 is false, check if ~w0 = true => w0's negation value
                        } else {
                            // w0 is false means w0's var is assigned with w0 being false
                            let vi = w0.variable().index();
                            if self.var_is_assigned(vi) {
                                Some(self.var_data[vi].trail_pos as usize)
                            } else {
                                None
                            }
                        };
                        let w1_neg_pos = {
                            let vi = w1.variable().index();
                            if self.var_is_assigned(vi) {
                                Some(self.var_data[vi].trail_pos as usize)
                            } else {
                                None
                            }
                        };
                        // At least one watched false literal must have trail
                        // pos >= minimal_qhead for BCP to discover this unit.
                        let reachable = w0_neg_pos.is_some_and(|p| p >= minimal_qhead)
                            || w1_neg_pos.is_some_and(|p| p >= minimal_qhead)
                            || unit_lit == w0  // unit lit is watched; BCP propagates it
                            || unit_lit == w1; // unit lit is watched; BCP propagates it
                        debug_assert!(
                            reachable,
                            "BUG: minimal trail rewind (#8095) would miss unit clause {idx} \
                             (unit_lit={unit_lit:?}, qhead={minimal_qhead}, \
                             w0={w0:?} pos={w0_neg_pos:?}, w1={w1:?} pos={w1_neg_pos:?})"
                        );
                    }
                }
            }
        }

        // Post-condition: every active clause with len >= 2 should have watches.
        // Missing watches cause missed propagations — a soundness bug that is
        // extremely hard to diagnose because it manifests as non-deterministic
        // incorrect SAT/UNSAT results.
        #[cfg(debug_assertions)]
        {
            // Forward check: active clause → has watches.
            for idx in self.arena.active_indices() {
                let off_header = idx;
                if self.arena.is_empty_clause(off_header) || self.arena.len_of(off_header) < 2 {
                    continue;
                }
                // Garbage/pending-garbage husks are deliberately NOT attached
                // by the rebuild loop above (husk adjudication) — they must
                // not be required to have watches here.
                if self.arena.is_garbage_any(off_header) {
                    continue;
                }
                let cref = ClauseRef(idx as u32);
                let lit0 = self.arena.literal(idx, 0);
                let lit1 = self.arena.literal(idx, 1);
                // attach_clause_watches(cref, (lit0, lit1), ..) stores watches under
                // lit0/lit1 (not negations). During BCP, propagating p scans watches[¬p].
                debug_assert!(
                    {
                        let w0 = self.watches.get_watches(lit0);
                        let w1 = self.watches.get_watches(lit1);
                        (0..w0.len()).any(|i| w0.clause_ref(i) == cref)
                            && (0..w1.len()).any(|i| w1.clause_ref(i) == cref)
                    },
                    "BUG: rebuild_watches: active clause {idx} (len={}) missing watch on \
                     lit0={lit0:?} or lit1={lit1:?}",
                    self.arena.len_of(off_header)
                );
            }

            // Reverse check: every watch entry must reference an active clause.
            // rebuild_watches() builds from scratch, so there should be zero
            // stale entries (unlike the incremental path where long-clause
            // watches are lazily filtered).
            for vi in 0..self.num_vars {
                for sign in [true, false] {
                    let lit = if sign {
                        Literal::positive(Variable(vi as u32))
                    } else {
                        Literal::negative(Variable(vi as u32))
                    };
                    let wl = self.watches.get_watches(lit);
                    for wi in 0..wl.len() {
                        let cref = wl.clause_ref(wi);
                        let cidx = cref.0 as usize;
                        debug_assert!(
                            cidx < self.arena.len()
                                && self.arena.is_active(cidx)
                                && self.arena.len_of(cidx) >= 2,
                            "BUG: rebuild_watches: stale watch on lit={lit:?} → \
                             clause {cidx} (active={}, len={})",
                            cidx < self.arena.len() && self.arena.is_active(cidx),
                            if cidx < self.arena.len() {
                                self.arena.len_of(cidx)
                            } else {
                                0
                            },
                        );
                    }
                }
            }
        }
    }
}
