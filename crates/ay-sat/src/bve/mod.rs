// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded Variable Elimination (BVE)
//!
//! Implements variable elimination as an inprocessing technique.
//! For a variable x, we can eliminate it by:
//! 1. Collecting all clauses containing x (positive occurrences)
//! 2. Collecting all clauses containing ~x (negative occurrences)
//! 3. Computing all resolvents between positive and negative clauses
//! 4. If the total size of resolvents <= original clauses, eliminate x
//!
//! The "bounded" part ensures we only eliminate if it doesn't increase the
//! formula size too much (bounded by a growth limit).
//!
//! Reference: Een & Biere, "Effective Preprocessing in SAT through Variable
//! and Clause Elimination", SAT 2005.

use crate::clause::ClauseSignature;
use crate::elim_heap::ElimHeap;
use crate::kani_compat::DetHashMap;
use crate::literal::{Literal, Variable};
use crate::occ_list::OccList;

// Re-import for test module visibility (tests use `use super::*;`).
#[cfg(test)]
use crate::clause_arena::ClauseArena;

/// Maximum growth bound for BVE inprocessing.
/// CaDiCaL uses an adaptive bound (0→1→2→4→8→16) for inprocessing,
/// starting conservative and relaxing after successful rounds.
/// `fastelimbound=8` is only for preprocessing; inprocessing uses `elimboundmin=0`.
const BVE_GROWTH_BOUND_MAX: usize = 16;

/// Maximum total occurrences (pos+neg) for a variable to be considered for
/// elimination. Kissat uses `eliminateocclim=2000` applied to the sum of
/// positive and negative occurrences (resolve.c:282-289). CaDiCaL uses
/// `elimocclim=100` applied per-polarity (elim.cpp:698), which is much
/// more restrictive and causes AY to miss elimination opportunities on
/// formulas like mp1-klieber where many variables have 100-500 occurrences
/// per polarity but are profitably eliminable. Using Kissat's approach:
/// the resolvent_budget (clause-count bound) already prevents unprofitable
/// elimination, so the occurrence limit is only a pre-filter to avoid
/// wasting resolution effort.
pub(crate) const ELIM_OCC_LIMIT: usize = 2_000;

/// Maximum resolvent size in literals. If any single resolvent exceeds this,
/// the variable elimination is rejected. Matches CaDiCaL `elimclslim=100`
/// (options.hpp:89, elim.cpp:509).
pub(crate) const ELIM_CLAUSE_SIZE_LIMIT: usize = 100;

/// Cached per-process read of the `--sat-[no-]bve-additive-fastelim` kill-switch,
/// returning the explicit override (if any) rather than a final bool.
///
/// Three-state (the house `AY_AB_*` kill-switch convention, extended for the
/// var-count band in `additive_fastelim_default`):
///   - `"1"` => `Some(true)`  — force the additive Pass-1 budget ON *everywhere*
///     (the original uncapped opt-in; for A/B against baseline).
///   - `"0"` => `Some(false)` — force OFF *everywhere* (restores the full
///     CaDiCaL no-growth baseline: byte-identical behaviour on every formula).
///   - unset / anything else => `None` — band-gated default (see
///     `additive_fastelim_default`): additive is ACTIVE only when
///     `num_vars > AY_BVE_ADDITIVE_MIN_VARS` (200K).
///
/// Band evidence (wf_eab7d219 + wf_e2bdf6e1, 120s serial `--competition`):
///   - 6f354fbe (48,032 vars): additive REGRESSES UNSAT -> UNKNOWN — clause
///     growth perturbs an already-working search, so it must stay baseline.
///   - ebbda8d9 (723,395 vars): additive FLIPS UNKNOWN -> UNSAT (bve
///     245,783 -> 306,728 eliminated), independently dpr-trim + cake_lpr
///     VERIFIED and kissat-corroborated.
/// The 15x var-count gap (48K vs 723K) with the band edge at 200K
/// (= `PREPROCESS_EXPENSIVE_MAX_VARS`, the post-collapse expensive-preprocessing
/// edge) captures the flip while leaving every small formula byte-identical.
/// Read once and cached like the other `AY_AB_*` knobs.
fn additive_fastelim_override() -> Option<bool> {
    // B36: CLI-owned tri-state (--sat-bve-additive-fastelim /
    // --sat-no-bve-additive-fastelim); unset keeps the band auto decision.
    let s = ay_core::sat_ab_switches();
    if s.no_bve_additive_fastelim {
        Some(false)
    } else if s.bve_additive_fastelim {
        Some(true)
    } else {
        None
    }
}

/// Default variable-count floor (strict `>`) above which the banded additive
/// Pass-1 fastelim budget is ACTIVE. Mirrors the solver's
/// `PREPROCESS_EXPENSIVE_MAX_VARS` (200K) post-collapse band edge: below it
/// BVE was already sufficient and additive clause-growth only perturbs a
/// working search (6f354fbe 48K regressed); above it additive reaches
/// kissat-class coverage and flips otherwise-unsolved giants (ebbda8d9 723K
/// UNKNOWN -> cake_lpr-VERIFIED UNSAT). Kept as a local const (rather than
/// importing the `pub(super)` solver constant across the module boundary) but
/// deliberately equal to it; overridable via `AY_BVE_ADDITIVE_MIN_VARS` for
/// A/B tuning of the edge.
const AY_BVE_ADDITIVE_MIN_VARS_DEFAULT: usize = 200_000;

/// Banded-additive variable-count floor (200K). (B3: the env override is
/// deleted.)
fn additive_fastelim_min_vars() -> usize {
    // B3: the AY_BVE_ADDITIVE_MIN_VARS env override is deleted.
    AY_BVE_ADDITIVE_MIN_VARS_DEFAULT
}

/// Resolve the default `additive_fastelim` flag for a BVE engine covering
/// `num_vars` variables: honour the `--sat-[no-]bve-additive-fastelim` kill-switch
/// override if set, else apply the variable-count band
/// (`num_vars > AY_BVE_ADDITIVE_MIN_VARS`). Computed once per BVE engine at
/// construction from the solver's current var count — the same way the env
/// read was wired, now with the band folded in.
fn additive_fastelim_default(num_vars: usize) -> bool {
    match additive_fastelim_override() {
        Some(forced) => forced,
        None => num_vars > additive_fastelim_min_vars(),
    }
}

const BVE_OCC_DELTA_MAX_TOUCHED_CLAUSES: usize = 4_096;
const BVE_OCC_DELTA_MAX_TOUCHED_LITS: usize = 32_768;
const BVE_OCC_DELTA_MAX_OCC_ENTRIES: u64 = 262_144;

/// Statistics for BVE operations
#[derive(Debug, Clone, Default)]
#[allow(clippy::upper_case_acronyms)]
#[non_exhaustive]
pub struct BVEStats {
    /// Number of variables eliminated
    pub vars_eliminated: u64,
    /// Number of clauses removed (before resolvents added)
    pub clauses_removed: u64,
    /// Number of resolvents added
    pub resolvents_added: u64,
    /// Number of tautological resolvents skipped
    pub tautologies_skipped: u64,
    /// Resolution pairs where the 64-bit clause signature filter guaranteed
    /// no tautological resolvent, enabling the fast path that skips per-literal
    /// opposite-polarity mark checks (issue #7922).
    pub sig_fast_path: u64,
    /// Number of elimination rounds
    pub rounds: u64,
    /// Number of root-level-false literals pruned from resolvents
    pub root_literals_pruned: u64,
    /// Number of resolution pairs skipped because a parent was satisfied at root level
    pub root_satisfied_parents: u64,
    /// Number of double self-subsuming resolutions (CaDiCaL elim.cpp:413-424)
    pub double_otfs: u64,
    /// Number of single self-subsuming resolutions
    pub single_otfs: u64,
    /// Total literals across all non-unit resolvents (for average resolvent size tracking)
    pub total_resolvent_literals: u64,
    /// Count of non-unit resolvents added (excludes units, empties, OTFS)
    pub non_unit_resolvents: u64,
    /// Maximum resolvent length encountered
    pub max_resolvent_len: u64,
    /// Number of clauses deleted by backward subsumption during BVE
    pub backward_subsumed: u64,
    /// Number of clauses strengthened by backward self-subsumption during BVE
    pub backward_strengthened: u64,
    /// Number of unit literals derived by hyper-unary resolution during BVE
    pub backward_units: u64,
    /// Number of backward subsumption candidates filtered by 64-bit signature
    /// pre-check (#7922). These candidates were skipped in O(1) without the
    /// expensive O(|D|) literal-by-literal scan.
    pub backward_sig_filtered: u64,
    /// Variables eliminated during the quick elimination pre-pass (Pass 0).
    /// CaDiCaL `elimfast.cpp` pattern: tight limits (5 occs, 20 clause size).
    pub fast_elim_vars: u64,
    /// Clauses removed during the quick elimination pre-pass.
    pub fast_elim_clauses: u64,
    /// Number of LRAT BVE transactions rejected by proof preflight.
    pub lrat_preflight_rejected: u64,
    /// LRAT BVE preflight rejected because no proof manager was available.
    pub lrat_preflight_missing_proof_manager: u64,
    /// LRAT BVE preflight rejected because a source ID was missing or hidden.
    pub lrat_preflight_missing_or_hidden_source_id: u64,
    /// LRAT BVE preflight rejected because a deletion target was not live.
    pub lrat_preflight_deletion_target_not_live: u64,
    /// LRAT BVE preflight rejected malformed strengthening metadata.
    pub lrat_preflight_malformed_strengthening: u64,
    /// LRAT BVE preflight rejected malformed resolvent metadata.
    pub lrat_preflight_malformed_resolvent: u64,
    /// LRAT BVE preflight rejected replacement cleanup that would emit a unit.
    pub lrat_preflight_replacement_cleanup_unit: u64,
    /// LRAT BVE preflight rejected during planned-add validation.
    pub lrat_preflight_planned_add_rejected: u64,
    /// Planned-add rejection because proof output was not LRAT.
    pub lrat_preflight_planned_not_lrat: u64,
    /// Planned-add rejection because LRAT output was blocked.
    pub lrat_preflight_planned_lrat_blocked: u64,
    /// Planned-add rejection because proof I/O had failed.
    pub lrat_preflight_planned_io_failed: u64,
    /// Planned-add rejection because deletion batches were still pending.
    pub lrat_preflight_planned_pending_deletions: u64,
    /// Planned-add rejection because ProofManager and writer IDs diverged.
    pub lrat_preflight_planned_output_id_mismatch: u64,
    /// Planned-add rejection because the clause was invalid.
    pub lrat_preflight_planned_invalid_clause: u64,
    /// Planned-add rejection because an axiom would be suppressed.
    pub lrat_preflight_planned_suppressed_axiom: u64,
    /// Planned-add rejection because a trusted unit would be hidden.
    pub lrat_preflight_planned_hidden_trusted_unit: u64,
    /// Planned-add rejection because a derived add had no hints.
    pub lrat_preflight_planned_missing_hints: u64,
    /// Planned-add rejection because a hint was zero.
    pub lrat_preflight_planned_zero_hint: u64,
    /// Planned-add rejection because a hint was duplicated.
    pub lrat_preflight_planned_duplicate_hint: u64,
    /// Planned-add rejection because a hint was unknown.
    pub lrat_preflight_planned_unknown_hint: u64,
    /// Planned-add rejection because a hint named a trusted hidden ID.
    pub lrat_preflight_planned_trusted_hint: u64,
    /// Planned-add rejection because a hint referenced a backward-reserved ID.
    pub lrat_preflight_planned_backward_reserved_hint: u64,
    /// Planned-add rejection because the planned ID range overflowed.
    pub lrat_preflight_planned_id_overflow: u64,
    /// Same-epoch occurrence refreshes that skipped structural validation.
    pub occ_epoch_fastpath_refreshes: u64,
    /// Occurrence refreshes validated by the default-off touched-region delta path.
    pub occ_delta_validated_refreshes: u64,
    /// Touched-region delta validation failures that fell back to the full gate.
    pub occ_delta_validation_fallbacks: u64,
    /// Uncertified touched-region deltas that fell back to the full gate.
    pub occ_delta_uncertified_fallbacks: u64,
    /// Oversized touched-region deltas that fell back to the full gate.
    pub occ_delta_oversize_fallbacks: u64,
    /// Unique touched clauses seen by delta validation attempts.
    pub occ_delta_touched_clauses: u64,
    /// Unique touched literals seen by delta validation attempts.
    pub occ_delta_touched_lits: u64,
    /// Occurrence-list entries scanned by touched-region validation.
    pub occ_delta_occ_entries_checked: u64,
    /// Missing current clause-to-literal entries found by delta validation.
    pub occ_delta_missing_entries: u64,
    /// Stale live entries found by delta validation.
    pub occ_delta_stale_live_entries: u64,
    /// Live learned entries found by delta validation.
    pub occ_delta_live_learned_entries: u64,
    /// Populated occurrence saved-states dropped at a round boundary because
    /// cross-round reuse is disabled.
    pub occ_saved_state_round_end_drops: u64,
    /// Populated occurrence saved-states retained at a round boundary for the
    /// default-off cross-round reuse candidate.
    pub occ_saved_state_round_end_retains: u64,
}

#[derive(Debug, Clone)]
struct BveOccDelta {
    enabled: bool,
    uncertified_since_validation: bool,
    touched_clauses: Vec<usize>,
    touched_lits: Vec<Literal>,
    lit_stamps: Vec<u32>,
    current_lit_stamp: u32,
    max_touched_clauses: usize,
    max_touched_lits: usize,
    max_occ_entries: u64,
}

impl Default for BveOccDelta {
    fn default() -> Self {
        Self {
            enabled: false,
            uncertified_since_validation: false,
            touched_clauses: Vec::new(),
            touched_lits: Vec::new(),
            lit_stamps: Vec::new(),
            current_lit_stamp: 1,
            max_touched_clauses: BVE_OCC_DELTA_MAX_TOUCHED_CLAUSES,
            max_touched_lits: BVE_OCC_DELTA_MAX_TOUCHED_LITS,
            max_occ_entries: BVE_OCC_DELTA_MAX_OCC_ENTRIES,
        }
    }
}

impl BveOccDelta {
    fn set_enabled(&mut self, enabled: bool, num_vars: usize) {
        self.enabled = enabled;
        if enabled {
            self.ensure_num_vars(num_vars);
        } else {
            self.clear_validated();
        }
    }

    fn ensure_num_vars(&mut self, num_vars: usize) {
        if self.enabled {
            let needed = num_vars.saturating_mul(2);
            if self.lit_stamps.len() < needed {
                self.lit_stamps.resize(needed, 0);
            }
        }
    }

    fn has_touches(&self) -> bool {
        !self.touched_clauses.is_empty() || !self.touched_lits.is_empty()
    }

    fn needs_validation(&self) -> bool {
        self.enabled && (self.uncertified_since_validation || self.has_touches())
    }

    fn mark_uncertified(&mut self) {
        if !self.enabled {
            return;
        }
        self.touched_clauses.clear();
        self.touched_lits.clear();
        self.uncertified_since_validation = true;
        self.advance_lit_stamp();
    }

    fn clear_validated(&mut self) {
        self.touched_clauses.clear();
        self.touched_lits.clear();
        self.uncertified_since_validation = false;
        self.advance_lit_stamp();
    }

    fn record_clause(&mut self, clause_idx: usize, literals: &[Literal], num_vars: usize) {
        if !self.enabled {
            return;
        }
        self.ensure_num_vars(num_vars);
        self.touched_clauses.push(clause_idx);
        for &lit in literals {
            self.record_lit(lit);
        }
    }

    fn record_replace(
        &mut self,
        clause_idx: usize,
        old_lits: &[Literal],
        new_lits: &[Literal],
        num_vars: usize,
    ) {
        if !self.enabled {
            return;
        }
        self.ensure_num_vars(num_vars);
        self.touched_clauses.push(clause_idx);
        for &lit in old_lits {
            self.record_lit(lit);
        }
        for &lit in new_lits {
            self.record_lit(lit);
        }
    }

    fn prepare_unique_touches(&mut self) {
        self.touched_clauses.sort_unstable();
        self.touched_clauses.dedup();
        self.touched_lits.sort_unstable();
        self.touched_lits.dedup();
    }

    fn within_budget(&self) -> bool {
        self.touched_clauses.len() <= self.max_touched_clauses
            && self.touched_lits.len() <= self.max_touched_lits
    }

    fn record_lit(&mut self, lit: Literal) {
        let idx = lit.index();
        if idx >= self.lit_stamps.len() {
            self.lit_stamps.resize(idx + 1, 0);
        }
        if self.lit_stamps[idx] != self.current_lit_stamp {
            self.lit_stamps[idx] = self.current_lit_stamp;
            self.touched_lits.push(lit);
        }
    }

    fn advance_lit_stamp(&mut self) {
        if self.current_lit_stamp == u32::MAX {
            self.lit_stamps.fill(0);
            self.current_lit_stamp = 1;
        } else {
            self.current_lit_stamp += 1;
        }
    }

    #[cfg(test)]
    fn set_limits_for_tests(
        &mut self,
        max_touched_clauses: usize,
        max_touched_lits: usize,
        max_occ_entries: u64,
    ) {
        self.max_touched_clauses = max_touched_clauses;
        self.max_touched_lits = max_touched_lits;
        self.max_occ_entries = max_occ_entries;
    }
}

/// Outcome of attempting to resolve two clauses during BVE.
///
/// CaDiCaL `elim.cpp:292-359`: resolution checks `val(lit)` for each literal.
/// Root-level-true literals indicate a satisfied parent (garbage-collect it);
/// root-level-false literals are dropped from the resolvent.
pub(crate) enum ResolveOutcome {
    /// Non-tautological resolvent produced.
    /// Second field: variable indices of root-level-false literals pruned from
    /// the resolvent. The caller uses these to look up LRAT proof IDs for the
    /// unit clauses that falsified them (CaDiCaL elim.cpp:303-308).
    Resolvent(Vec<Literal>, Vec<usize>),
    /// Resolvent is tautological (contains both L and ~L).
    Tautology,
    /// A parent clause is satisfied at root level — skip this resolution pair.
    /// CaDiCaL: `elim_update_removed_clause` + `mark_garbage`.
    /// The boolean indicates which parent: `true` = first (positive) parent,
    /// `false` = second (negative) parent.
    ParentSatisfied(bool),
}

/// Result of attempting to eliminate a variable
#[derive(Debug, Clone)]
pub(crate) struct EliminationResult {
    /// The variable that was eliminated
    pub variable: Variable,
    /// Indices of clauses to delete (containing the eliminated variable)
    pub to_delete: Vec<usize>,
    /// Reconstruction witness entries for eliminated clauses.
    ///
    /// Each entry stores the exact witness literal that CaDiCaL would push on
    /// the extension stack for that clause, avoiding polarity inference during
    /// later reconstruction bookkeeping.
    pub witness_entries: Vec<WitnessEntry>,
    /// New resolvents: (lits, pos_ante_idx, neg_ante_idx, pruned_root_var_indices).
    /// The fourth element lists variable indices of root-level-false literals
    /// pruned from the resolvent; the caller maps them to LRAT proof IDs (#5071).
    pub resolvents: Vec<(Vec<Literal>, usize, usize, Vec<usize>)>,
    /// Parent clauses that can be strengthened in-place (OTFS-style) instead
    /// of adding an equivalent resolvent.
    pub strengthened: Vec<ClauseStrengthening>,
    /// Parent clause indices detected as satisfied at root level during
    /// resolution checking. The caller marks these as garbage immediately
    /// (CaDiCaL elim.cpp:316-325).
    pub satisfied_parents: Vec<usize>,
    /// Whether elimination was performed
    pub eliminated: bool,
    /// Number of actual resolution pair attempts (CaDiCaL elim.cpp:271 parity).
    /// The caller charges this against the BVE resolution budget, NOT the
    /// theoretical pos*neg product.
    pub resolution_attempts: u64,
}

/// Witness metadata for one eliminated clause.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct WitnessEntry {
    /// Clause index (word offset) in the current ClauseArena.
    pub clause_idx: usize,
    /// Witness literal used to reconstruct this clause.
    pub witness: Literal,
}

/// Planned in-place strengthening for one parent clause.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ClauseStrengthening {
    /// Clause index (word offset) in the current ClauseArena.
    pub clause_idx: usize,
    /// New literal list after removing the pivot from the parent clause.
    pub new_lits: Vec<Literal>,
    /// Antecedent clause indices that justify the strengthening (OTFS).
    /// The resolvent of these two clauses subsumes the original clause.
    /// Used for LRAT hint chain construction (#5149).
    pub pos_ante: usize,
    pub neg_ante: usize,
    /// Variable indices of root-level-false literals pruned from the
    /// resolvent. The LRAT hint chain for the strengthened clause must
    /// include the unit-clause proof IDs for these variables, matching
    /// CaDiCaL's `unit_id(-lit)` calls in `elim.cpp:303-308` (#5026).
    pub pruned_vars: Vec<usize>,
}

impl EliminationResult {
    /// Returns a "not eliminated" result for the given variable.
    fn not_eliminated(var: Variable) -> Self {
        Self {
            variable: var,
            to_delete: Vec::new(),
            witness_entries: Vec::new(),
            resolvents: Vec::new(),
            strengthened: Vec::new(),
            satisfied_parents: Vec::new(),
            eliminated: false,
            resolution_attempts: 0,
        }
    }
}

/// Occurrence list for BVE — uses the shared `OccList` type.
pub(crate) type BVEOccList = OccList;

/// Bounded Variable Elimination engine
#[allow(clippy::upper_case_acronyms)] // -D warnings overrides crate-level #![allow]
pub(crate) struct BVE {
    /// Occurrence lists
    occ: BVEOccList,
    /// Statistics
    stats: BVEStats,
    /// Number of variables
    num_vars: usize,
    /// Variables that have been eliminated (cannot be eliminated again)
    eliminated: Vec<bool>,
    /// Temporary buffer for resolvent computation
    resolvent_buf: Vec<Literal>,
    /// Var indices of root-level-false literals pruned from the last resolvent.
    /// Used by the caller to build LRAT hint chains (#5071).
    pruned_root_vars_buf: Vec<usize>,
    /// Reusable buffer for positive occurrence indices (avoids per-call allocations)
    pos_occ_buf: Vec<usize>,
    /// Reusable buffer for negative occurrence indices (avoids per-call allocations)
    neg_occ_buf: Vec<usize>,
    /// Per-variable score credit for structurally detected gates.
    ///
    /// A credit of `pos_gate * neg_gate` approximates the number of gate×gate
    /// resolution pairs skipped by restricted resolution. The heap subtracts it
    /// from the raw elimination score so gate-defined variables move up in the
    /// schedule without changing pure-literal priority.
    schedule_gate_pair_credit: Vec<u64>,
    /// Dynamic priority-queue schedule: indexed min-heap by elimination cost.
    /// CaDiCaL `heap<elim_more>`: cheapest variables popped first, scores
    /// updated mid-round as clauses are added/removed.
    schedule: ElimHeap,
    /// Pending inprocessing candidates whose occurrence counts changed since
    /// the last completed elimination phase.
    ///
    /// CaDiCaL uses per-variable `flags.elim` marks and only schedules marked
    /// variables in normal elimination rounds (`elim.cpp:830-846`). Without a
    /// similar filter, AY rebuilds the heap over all live variables on every
    /// BVE call, wasting the resolution budget on unchanged candidates.
    candidate_dirty: Vec<bool>,
    /// True after `build_schedule()` has been called since the last `rebuild()`.
    /// Prevents infinite re-builds when the heap drains without any successful
    /// elimination (failed variables are not re-inserted). Reset by `rebuild()`.
    schedule_built: bool,
    /// Adaptive growth bound for BVE (CaDiCaL elimboundmin→elimboundmax pattern).
    /// Starts at 0 (net-zero clause growth) and doubles after each successful round.
    growth_bound: usize,
    /// True when running preprocessing fast elimination (CaDiCaL fastelim):
    /// budget = min(growth_bound, clauses_removed).
    /// False in normal inprocessing mode:
    /// budget = clauses_removed + growth_bound.
    fastelim_mode: bool,
    /// True during the quick elimination pre-pass (Pass 0, #8242).
    quick_elim_mode: bool,
    /// True when occurrence lists reflect the current irredundant clause state
    /// and can be refreshed incrementally instead of fully rebuilt (#8096).
    /// Set to true after a full `rebuild_with_vals()`; set to false on
    /// compaction or other resets that invalidate the occ lists.
    occ_populated: bool,
    /// Solver clause-DB mutation epoch for which the occurrence lists were last
    /// release-mode validated against the arena (#9106).
    ///
    /// `None` means callers must use the conservative full consistency check.
    /// When production BVE supplies `clause_db_changes`, refresh can skip the
    /// O(formula) bidirectional scan if no checked clause mutation occurred
    /// since the last validation or rebuild. If the epoch changes, the scan
    /// still runs and falls back to a full rebuild on any stale/missing entry.
    occ_consistency_epoch: Option<u64>,
    /// Default-off touched-region certificate for validating saved occurrence
    /// lists without a full bidirectional arena scan.
    occ_delta: BveOccDelta,
    /// Default-off candidate for retaining occurrence state across preprocessing
    /// or restart-inprocessing round boundaries.
    ///
    /// When disabled, the current BVE/preprocessing round may still use live
    /// occurrence lists for dense propagation and same-round BCE sharing, but
    /// the round finalizer clears `occ_populated` so later clause mutations do
    /// not maintain saved state that will not be reused.
    occ_saved_state_reuse_enabled: bool,
    /// Reusable buffer for positive clause profiles in bounded elimination check.
    /// Avoids per-attempt `Vec::with_capacity(n)` allocations (#8134).
    pos_profile_buf: Vec<ResolveClauseProfile>,
    /// Reusable buffer for negative clause profiles in bounded elimination check.
    neg_profile_buf: Vec<ResolveClauseProfile>,
    /// Scoped BVE (#8369): variables with index < this floor are protected.
    scope_var_floor: usize,
    /// Lever `--sat-[no-]bve-additive-fastelim` (wf_eab7d219, banded wf_e2bdf6e1):
    /// when true, the Pass-1 fastelim budget (`fastelim_mode && !quick_elim_mode`)
    /// switches from CaDiCaL's no-growth `min(clauses_removed, growth_bound)` to
    /// kissat's ADDITIVE `clauses_removed + growth_bound` (resolve.c:283-294).
    /// Post-fast-inner-fix each elimination is ~30x cheaper, so the no-growth
    /// cap (which rejects EVERY var whose elimination grows the clause DB at
    /// all) leaves ~7.9x coverage on the table on d0298807-class sparse
    /// formulas (measured 3,165 -> 24,898 eliminated). Initialised at
    /// construction from `additive_fastelim_default(num_vars)`: BAND-GATED by
    /// default (ACTIVE iff `num_vars > AY_BVE_ADDITIVE_MIN_VARS` = 200K), which
    /// captures the ebbda8d9 723K flip (UNKNOWN -> cake_lpr-VERIFIED UNSAT)
    /// while leaving the small floor byte-identical (6f354fbe 48K, the
    /// regression sentinel, stays below the band). `--sat-[no-]bve-additive-fastelim`
    /// forces it ON everywhere, `=0` forces it OFF everywhere. See
    /// `resolvent_budget`, `additive_fastelim_default`, `additive_fastelim_override`.
    additive_fastelim: bool,
}

struct ResolveAcc<'a> {
    clauses_removed: usize,
    resolvents: &'a mut Vec<(Vec<Literal>, usize, usize, Vec<usize>)>,
    strengthened: &'a mut Vec<ClauseStrengthening>,
    /// Maps clause_idx → index in `strengthened` for O(1) lookup (#5075).
    strengthened_idx: &'a mut DetHashMap<usize, usize>,
    found_empty_resolvent: &'a mut bool,
    /// CaDiCaL fastelim product shortcut (elimfast.cpp:85-88, :239):
    /// when `pos * neg <= budget`, the clause-count bound is trivially
    /// satisfied even if ALL resolvents are non-tautological. The per-pair
    /// clause-count early-abort is skipped, saving comparison overhead.
    clause_count_guaranteed: bool,
    /// Parent clause indices detected as satisfied at root level during
    /// resolution (CaDiCaL elim.cpp:316-325).
    satisfied_parents: &'a mut Vec<usize>,
}

type BoundedElimCheck = (
    bool,
    Vec<(Vec<Literal>, usize, usize, Vec<usize>)>,
    Vec<ClauseStrengthening>,
    Vec<usize>,
    u64, // resolution_attempts: actual try_resolve_pair calls (CaDiCaL elim.cpp:271)
);

#[derive(Clone, Copy)]
struct ResolveClauseProfile {
    clause_idx: usize,
    signature: ClauseSignature,
    tautological: bool,
}

impl BVE {
    /// Create a new BVE engine for n variables
    pub(crate) fn new(num_vars: usize) -> Self {
        Self {
            // Sized on first use: `OccList::add_clause` grows to cover each
            // literal it sees, and `get` is bounds-safe, so nothing has to
            // pre-size this. Eagerly it costs ~128 resident bytes per
            // variable at solver construction, on every instance, whether or
            // not this engine ever runs.
            occ: BVEOccList::new(0),
            stats: BVEStats::default(),
            num_vars,
            eliminated: vec![false; num_vars],
            resolvent_buf: Vec::new(),
            pruned_root_vars_buf: Vec::new(),
            pos_occ_buf: Vec::new(),
            neg_occ_buf: Vec::new(),
            schedule_gate_pair_credit: vec![0; num_vars],
            schedule: ElimHeap::new(num_vars),
            candidate_dirty: vec![false; num_vars],
            schedule_built: false,
            growth_bound: 0,
            fastelim_mode: false,
            quick_elim_mode: false,
            occ_populated: false,
            occ_consistency_epoch: None,
            occ_delta: BveOccDelta::default(),
            occ_saved_state_reuse_enabled: false,
            pos_profile_buf: Vec::new(),
            neg_profile_buf: Vec::new(),
            scope_var_floor: 0,
            additive_fastelim: additive_fastelim_default(num_vars),
        }
    }

    /// Ensure internal buffers can handle `num_vars` variables.
    ///
    /// ENSURES: self.num_vars >= num_vars, eliminated buffer sized accordingly
    pub(crate) fn ensure_num_vars(&mut self, num_vars: usize) {
        if self.num_vars >= num_vars {
            return;
        }
        self.num_vars = num_vars;
        self.occ.ensure_num_vars(num_vars);
        self.schedule.ensure_num_vars(num_vars);
        if self.eliminated.len() < num_vars {
            self.eliminated.resize(num_vars, false);
        }
        if self.schedule_gate_pair_credit.len() < num_vars {
            self.schedule_gate_pair_credit.resize(num_vars, 0);
        }
        if self.candidate_dirty.len() < num_vars {
            self.candidate_dirty.resize(num_vars, false);
        }
        self.occ_delta.ensure_num_vars(num_vars);

        debug_assert!(
            self.eliminated.len() >= num_vars,
            "BUG: ensure_num_vars({num_vars}) failed: eliminated={}",
            self.eliminated.len()
        );
    }

    /// Get statistics
    pub(crate) fn stats(&self) -> &BVEStats {
        &self.stats
    }

    /// Restore previously saved statistics (e.g., after compaction recreates
    /// the BVE engine via `BVE::new()`). Without this, stats are zeroed.
    pub(crate) fn restore_stats(&mut self, stats: BVEStats) {
        self.stats = stats;
    }

    /// Whether we're in fastelim (preprocessing) mode.
    /// CaDiCaL parity: fastelim does NOT use gate detection.
    pub(crate) fn is_fastelim_mode(&self) -> bool {
        self.fastelim_mode
    }

    /// Whether the quick elimination pre-pass (Pass 0, #8242) is active.
    pub(crate) fn is_quick_elim_mode(&self) -> bool {
        self.quick_elim_mode
    }

    /// Enable or disable quick elimination mode.
    pub(crate) fn set_quick_elim_mode(&mut self, mode: bool) {
        self.quick_elim_mode = mode;
    }

    /// Whether the additive Pass-1 fastelim budget lever is engaged.
    #[cfg(test)]
    pub(crate) fn is_additive_fastelim(&self) -> bool {
        self.additive_fastelim
    }

    /// Force the additive Pass-1 fastelim budget on/off (tests + explicit
    /// solver configuration). Production defaults to the cached env read in
    /// `BVE::new`; this setter lets tests exercise both budgets deterministically
    /// without depending on process-global env state.
    #[cfg(test)]
    pub(crate) fn set_additive_fastelim(&mut self, v: bool) {
        self.additive_fastelim = v;
    }

    /// Get mutable access to statistics (for tracking fast_elim counters).
    pub(crate) fn stats_mut(&mut self) -> &mut BVEStats {
        &mut self.stats
    }

    /// Enable or disable bounded touched-region occurrence validation.
    ///
    /// Default remains disabled. This only affects the cold BVE refresh path:
    /// mutation hooks already update occurrence lists exactly, and this gate
    /// decides whether `refresh_incremental_at_epoch` may validate the touched
    /// region instead of running the full bidirectional occurrence check.
    pub(crate) fn set_occ_delta_validation_enabled(&mut self, enabled: bool) {
        self.occ_delta.set_enabled(enabled, self.num_vars);
    }

    /// Whether bounded touched-region occurrence validation is enabled.
    pub(crate) fn occ_delta_validation_enabled(&self) -> bool {
        self.occ_delta.enabled
    }

    /// Enable or disable retaining BVE occurrence state across preprocessing or
    /// restart-inprocessing round boundaries.
    ///
    /// Default remains disabled. Same-round BVE/BCE/dense consumers can still
    /// use populated occurrence lists, but the round finalizer drops the live
    /// marker unless this candidate is explicitly enabled.
    pub(crate) fn set_occ_saved_state_reuse_enabled(&mut self, enabled: bool) {
        self.occ_saved_state_reuse_enabled = enabled;
    }

    /// Whether cross-round occurrence saved-state reuse is enabled.
    pub(crate) fn occ_saved_state_reuse_enabled(&self) -> bool {
        self.occ_saved_state_reuse_enabled
    }

    #[cfg(test)]
    pub(crate) fn set_occ_delta_validation_enabled_for_tests(&mut self, enabled: bool) {
        self.set_occ_delta_validation_enabled(enabled);
    }

    #[cfg(test)]
    pub(crate) fn set_occ_saved_state_reuse_enabled_for_tests(&mut self, enabled: bool) {
        self.set_occ_saved_state_reuse_enabled(enabled);
    }

    #[cfg(test)]
    pub(crate) fn set_occ_delta_limits_for_tests(
        &mut self,
        max_touched_clauses: usize,
        max_touched_lits: usize,
        max_occ_entries: u64,
    ) {
        self.occ_delta
            .set_limits_for_tests(max_touched_clauses, max_touched_lits, max_occ_entries);
    }

    /// Check if a variable has been eliminated
    #[cfg(test)]
    pub(crate) fn is_eliminated(&self, var: Variable) -> bool {
        let idx = var.index();
        idx < self.eliminated.len() && self.eliminated[idx]
    }

    /// Check if a variable is marked as eliminated in BVE's internal tracking.
    /// This is used by backward subsumption strengthening (#8482) to decide
    /// whether removing a literal from a clause is safe: if the literal's
    /// variable has already been eliminated, its extension stack entries
    /// already exist and strengthening cannot corrupt reconstruction.
    pub(crate) fn is_var_eliminated_internal(&self, var_idx: usize) -> bool {
        var_idx < self.eliminated.len() && self.eliminated[var_idx]
    }

    /// Mark a variable as eliminated in BVE's internal tracking, without
    /// performing actual BVE elimination. Called by decompose/sweep when
    /// a variable is substituted, so that subsequent BVE rounds skip it.
    /// Without this, substituted variables leak through next_candidate()
    /// because BVE's eliminated[] flag is not synchronized with var_lifecycle.
    pub(crate) fn mark_removed_external(&mut self, var_idx: usize) {
        if var_idx < self.eliminated.len() {
            self.eliminated[var_idx] = true;
            self.candidate_dirty[var_idx] = false;
        }
    }

    /// Clear the BVE eliminated flag for a variable that is being reactivated.
    /// Called during incremental reset when variables that were eliminated by BVE
    /// need to be restored for the next solve cycle.
    pub(crate) fn clear_removed_external(&mut self, var_idx: usize) {
        if var_idx < self.eliminated.len() {
            self.eliminated[var_idx] = false;
        }
    }

    /// Get occurrence list for a literal.
    pub(crate) fn get_occs(&self, lit: Literal) -> &[usize] {
        self.occ.get(lit)
    }

    /// Borrow the underlying OccList for read-only use by other inprocessing
    /// techniques (e.g., BCE) when the occ lists are already populated (#8096).
    ///
    /// Returns `Some(&OccList)` when occ lists are populated and reflect the
    /// current irredundant clause state. Returns `None` when occ lists need
    /// a full rebuild (e.g., after compaction or before the first BVE call).
    pub(crate) fn borrow_occ_list(&self) -> Option<&OccList> {
        if self.occ_populated {
            Some(&self.occ)
        } else {
            None
        }
    }

    /// Set the scope variable floor for scoped BVE (#8369).
    pub(crate) fn set_scope_var_floor(&mut self, floor: usize) {
        self.scope_var_floor = floor;
    }

    /// Get the current scope variable floor.
    #[allow(dead_code)] // audited-unused: kept pending the next dead-code cleanup slice
    pub(crate) fn scope_var_floor(&self) -> usize {
        self.scope_var_floor
    }
}

pub(crate) mod backward;
mod eliminate;
pub(crate) mod fast_eliminate;
mod occs;
mod resolve;
mod schedule;

// Phase 1 of incremental BVE during search (#8795).
//
// These modules live alongside the preprocessing-only `bve` machinery so
// that Phase 2 can share clause-database accessors without the parallel-
// island pattern that was rolled back in #8808. They are NOT yet wired
// into the CDCL loop — the public API is exercised only by the unit tests
// in this module. Phase 2 will register the tracker in the solver state
// and call the trigger from `solver/solve/inprocessing_schedule.rs`.
// `dead_code` is allowed because no production caller imports these yet;
// the Phase 2 wiring session removes the allow when the trigger is
// invoked from the inprocessing schedule.
#[allow(dead_code)]
pub(crate) mod incremental_cost;
#[allow(dead_code)]
pub(crate) mod trigger;

#[cfg(test)]
mod tests;
