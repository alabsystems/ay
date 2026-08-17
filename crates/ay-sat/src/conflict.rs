// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Conflict analysis (1UIP learning)
//!
//! Implements the First Unique Implication Point (1UIP) scheme for
//! conflict-driven clause learning.

use crate::literal::Literal;
use crate::solver::VarData;

mod analysis_state;

/// Result of conflict analysis
#[derive(Debug, Clone)]
pub(crate) struct ConflictResult {
    /// The learned clause (first literal is the asserting literal)
    pub(crate) learned_clause: Vec<Literal>,
    /// The backtrack level
    pub(crate) backtrack_level: u32,
    /// The LBD (Literal Block Distance) of the learned clause
    pub(crate) lbd: u32,
    /// Resolution chain (clause IDs used to derive the learned clause)
    /// Used for LRAT proof generation. Empty if LRAT is not enabled.
    pub(crate) resolution_chain: Vec<u64>,
    /// OTFS Branch B: when set, the strengthened clause already exists in the
    /// clause DB and should be used as the driving clause directly. The caller
    /// must skip `add_learned_clause` and use this ClauseRef for `enqueue`.
    /// CaDiCaL reference: analyze.cpp:1109-1127.
    pub(crate) otfs_driving_clause: Option<crate::watched::ClauseRef>,
}

/// Conflict analyzer
///
/// # Seen Mark Invariant (#8498)
///
/// Seen marks are stored in `VarData.flags` (not in this struct) for cache
/// locality. The `seen_to_clear` list tracks which indices have been marked
/// so `clear()` can reset them in O(marked) instead of O(num_vars).
///
/// **All seen-mark operations MUST go through this struct's API** (`mark_seen`,
/// `unmark_seen`, `register_jit_seen`, `clear`, `compact`). Code that directly
/// calls `var_data[idx].set_seen()` without updating `seen_to_clear` and
/// `seen_true_count` creates a desync that can corrupt the next conflict
/// analysis.
///
/// **Known exception:** `backbone_binary_analyze` uses its own local `seen_vars`
/// Vec to track and clear seen marks directly in `var_data`. It must fully
/// clear all marks before returning. A `conflict.clear()` must be called before
/// entering backbone probing to flush any stale `seen_to_clear` entries.
#[derive(Debug, Default, Clone)]
pub(crate) struct ConflictAnalyzer {
    /// Indices to clear in VarData.flags seen bit (sparse clear optimization).
    /// Seen marks are stored in VarData.flags for cache locality (#6994).
    pub(crate) seen_to_clear: Vec<usize>,
    /// Debug-only count of currently marked variables.
    ///
    /// Keeps postcondition checks O(1) instead of scanning the full vector
    /// after every conflict.
    #[cfg(debug_assertions)]
    seen_true_count: usize,
    /// Temporary learned clause being built (without the UIP)
    learned: Vec<Literal>,
    /// The asserting literal (UIP negated)
    asserting_lit: Option<Literal>,
    /// Resolution chain (clause IDs used during analysis)
    pub(crate) resolution_chain: Vec<u64>,
    /// Pivot literal for each resolution-chain entry.
    ///
    /// The first entry seeds the chain with the conflict clause and has no
    /// pivot. Reason-clause entries from the 1UIP loop record the trail
    /// literal being resolved. LRAT-only augmentation entries from
    /// minimization or level-0 unit chains intentionally have no pivot.
    resolution_chain_pivots: Vec<Option<Literal>>,
    /// Workspace for LBD computation (reused to avoid allocations)
    lbd_seen: Vec<bool>,
    /// Indices to clear in lbd_seen after LBD computation
    lbd_to_clear: Vec<usize>,
    /// Reusable buffer for clause literals during conflict analysis
    clause_buf: Vec<Literal>,
    /// Incrementally tracked maximum decision level among learned literals
    /// (== `compute_backtrack_level` while `learned_level_tracking_valid`).
    /// Maintained by `add_to_learned_tracked` during the 1UIP loop so the
    /// finalize path can skip the O(clause_len) backtrack-level rescan (#8790).
    learned_max_level: u32,
    /// First learned index >= 1 attaining `learned_max_level`, or `usize::MAX`
    /// when only `learned[0]` attains it (or the clause is unit). This is
    /// exactly the literal `reorder_for_watches` swaps into watch slot 1
    /// (clause index = learned index + 1 after the UIP prepend).
    learned_max_swap_idx: usize,
    /// True while `learned` is exactly the sequence built via
    /// `add_to_learned_tracked` since the last `clear()`. Any mutation that
    /// removes or reorders literals (minimize retain with removals, shrink
    /// replace, untracked adds) invalidates the incremental tracking and
    /// forces the single fused rescan in `backtrack_level_and_watch_swap`.
    learned_level_tracking_valid: bool,
}

impl ConflictAnalyzer {
    /// Create a new conflict analyzer
    pub(crate) fn new(_num_vars: usize) -> Self {
        Self {
            seen_to_clear: Vec::new(),
            #[cfg(debug_assertions)]
            seen_true_count: 0,
            learned: Vec::new(),
            asserting_lit: None,
            resolution_chain: Vec::new(),
            resolution_chain_pivots: Vec::new(),
            lbd_seen: Vec::new(),
            lbd_to_clear: Vec::new(),
            clause_buf: Vec::new(),
            learned_max_level: 0,
            learned_max_swap_idx: usize::MAX,
            learned_level_tracking_valid: false,
        }
    }

    /// Ensure the analyzer can track `num_vars` variables.
    /// Seen marks are now stored in VarData.flags, so no resizing needed here.
    pub(crate) fn ensure_num_vars(&mut self, _num_vars: usize) {}

    /// Clear the analyzer state for a new conflict.
    /// Uses sparse clear - O(marked) instead of O(num_vars).
    /// Seen marks are stored in `var_data[i].flags` for cache locality (#6994).
    ///
    /// Robust to external seen-bit manipulation (#8498): backbone_binary_analyze
    /// and other probing paths directly set/clear `var_data[idx].set_seen()` without
    /// updating ConflictAnalyzer bookkeeping (`seen_to_clear`, `seen_true_count`).
    /// When such external clearing removes a seen bit that was tracked here, the
    /// `seen_true_count` decrement is skipped for that entry. The unconditional
    /// reset at the end ensures the counter is always correct after clear().
    ///
    /// Also bounds-checks indices against `var_data.len()` (#8498): after variable
    /// compaction, stale `seen_to_clear` entries may reference indices beyond the
    /// truncated `var_data`. The bounds check prevents panics; `compact()` should
    /// have cleared stale entries, but defense-in-depth is warranted.
    pub(crate) fn clear(&mut self, var_data: &mut [VarData]) {
        let var_data_len = var_data.len();
        // Sparse clear - only reset indices that were actually marked.
        // Bounds-check: after compaction, stale entries may exceed var_data.len() (#8498).
        // Reset seen_true_count to 0 unconditionally at end (not per-entry decrement)
        // because external code paths can clear seen bits without bookkeeping.
        for &idx in &self.seen_to_clear {
            if idx < var_data_len {
                var_data[idx].set_seen(false);
            }
        }
        self.seen_to_clear.clear();
        self.learned.clear();
        self.asserting_lit = None;
        self.resolution_chain.clear();
        self.resolution_chain_pivots.clear();
        // Re-arm incremental learned-level tracking for the next analysis
        // (#8790). Valid as long as every append goes through
        // `add_to_learned_tracked` and no removal/reorder happens.
        self.learned_max_level = 0;
        self.learned_max_swap_idx = usize::MAX;
        self.learned_level_tracking_valid = true;
        // CaDiCaL analyze.cpp:1200-1210 -- postcondition: all seen marks are
        // cleared after sparse clear.
        //
        // Unconditional reset (#8498): external code (backbone_binary_analyze,
        // conflict_analysis JIT non-false literal cleanup) can clear seen bits
        // in var_data without updating seen_true_count. When this happens, the
        // sparse clear above clears already-false entries, leaving
        // seen_true_count > 0. Rather than asserting (which causes spurious
        // crashes), log a diagnostic and reset.
        #[cfg(debug_assertions)]
        {
            if self.seen_true_count != 0 {
                tracing::debug!(
                    residual_count = self.seen_true_count,
                    "ConflictAnalyzer::clear() seen_true_count residual — \
                     external code cleared seen bits without bookkeeping update (#8498)"
                );
            }
            self.seen_true_count = 0;

            // Full-scan postcondition (#8498): verify no seen marks remain in
            // var_data after sparse clear. If any are found, an external code
            // path (backbone_binary_analyze, probe UIP extraction, etc.) left a
            // residual seen mark that was NOT tracked in seen_to_clear. This is
            // a correctness risk: stale seen marks corrupt the next conflict
            // analysis by inflating the counter or adding wrong literals to the
            // learned clause.
            //
            // O(num_vars) scan; only runs in debug builds.
            for (idx, vd) in var_data.iter().enumerate() {
                debug_assert!(
                    !vd.is_seen(),
                    "BUG: residual seen mark at var_data[{idx}] after \
                     ConflictAnalyzer::clear() — stale mark not tracked in \
                     seen_to_clear (possible backbone_binary_analyze leak or \
                     external seen manipulation without bookkeeping) (#8498)"
                );
            }
        }
    }

    /// Compute LBD for an arbitrary clause (e.g. OTFS strengthened, or bump recompute).
    /// Counts ALL distinct levels including level 0, matching CaDiCaL's `recompute_glue`
    /// (analyze.cpp:206-219) which also counts all levels without subtraction.
    /// Uses the same sparse-clear workspace as `compute_lbd`.
    ///
    /// Currently used only in tests; will be called from OTFS strengthening and
    /// ChrBT LBD recompute (#6998) once those land.
    #[cfg(test)]
    pub(crate) fn compute_lbd_for_clause(&mut self, lits: &[Literal], var_data: &[VarData]) -> u32 {
        if self.lbd_seen.len() < var_data.len() + 1 {
            self.lbd_seen.resize(var_data.len() + 1, false);
        }
        let mut count = 0u32;
        for &lit in lits {
            let lvl = var_data[lit.variable().index()].level as usize;
            if !self.lbd_seen[lvl] {
                self.lbd_seen[lvl] = true;
                self.lbd_to_clear.push(lvl);
                count += 1;
            }
        }
        for &idx in &self.lbd_to_clear {
            self.lbd_seen[idx] = false;
        }
        self.lbd_to_clear.clear();
        count.max(1)
    }

    /// Compute the LBD (Literal Block Distance / glue) of the learned clause.
    ///
    /// Matches CaDiCaL's convention (analyze.cpp:1193): `glue = levels.size() - 1`.
    /// CaDiCaL counts all distinct levels during analysis (including the conflict
    /// level), then subtracts 1. The conflict level is always present since at
    /// least one literal in the conflict is at the current decision level.
    /// The subtraction excludes this level, measuring how many "decision blocks"
    /// below the conflict the clause depends on.
    ///
    /// All CaDiCaL tier thresholds (reducetier1glue=2, reducetier2glue=6) are
    /// calibrated to this convention. AY's CORE_LBD=2 and TIER1_LBD=6 must use
    /// the same convention to classify clauses equivalently.
    pub(crate) fn compute_lbd(&mut self, var_data: &[VarData]) -> u32 {
        let mut count = 0u32;

        // Ensure workspace is large enough for all decision levels
        if self.lbd_seen.len() < var_data.len() + 1 {
            self.lbd_seen.resize(var_data.len() + 1, false);
        }

        // Add asserting literal's level (this is the conflict level)
        if let Some(lit) = self.asserting_lit {
            let lvl = var_data[lit.variable().index()].level as usize;
            if !self.lbd_seen[lvl] {
                self.lbd_seen[lvl] = true;
                self.lbd_to_clear.push(lvl);
                count += 1;
            }
        }

        // Add other literals' levels
        for &lit in &self.learned {
            let lvl = var_data[lit.variable().index()].level as usize;
            if !self.lbd_seen[lvl] {
                self.lbd_seen[lvl] = true;
                self.lbd_to_clear.push(lvl);
                count += 1;
            }
        }

        // Clear workspace for next call
        for &idx in &self.lbd_to_clear {
            self.lbd_seen[idx] = false;
        }
        self.lbd_to_clear.clear();

        // CaDiCaL: glue = levels.size() - 1 (analyze.cpp:1193). Subtract 1 to
        // exclude the conflict level. The asserting literal is always present,
        // so count >= 1 for non-empty clauses, making the subtraction safe.
        // Unit clauses get glue 0; glue < clause_size (analyze.cpp:1199).
        count.saturating_sub(1)
    }

    /// Get the final conflict result.
    /// Builds the learned clause in-place (UIP prepend + mem::take) to reuse
    /// the Vec's heap capacity across conflicts. CaDiCaL: persistent `clause`
    /// member in internal.hpp, cleared but never freed between conflicts.
    pub(crate) fn get_result(&mut self, backtrack_level: u32, lbd: u32) -> ConflictResult {
        debug_assert!(
            self.asserting_lit.is_some(),
            "BUG: get_result called without asserting literal set"
        );

        // Prepend asserting literal to self.learned in-place.
        // insert(0, lit) shifts elements right by 1 — O(n) on a warm cache line
        // (just written during analysis), replacing the O(n) memcpy that previously
        // created a fresh Vec. Net cost: same O(n) work, zero malloc.
        if let Some(lit) = self.asserting_lit {
            self.learned.insert(0, lit);
        }

        // Transfer ownership of the Vec's heap allocation — no copy, no alloc.
        // Capacity is returned via return_learned_buf() after arena insertion.
        let learned_clause = std::mem::take(&mut self.learned);
        // The learned buffer is consumed; incremental level tracking no longer
        // describes it (#8790). clear() re-arms it for the next conflict.
        self.learned_level_tracking_valid = false;

        let result = ConflictResult {
            learned_clause,
            backtrack_level,
            lbd,
            resolution_chain: std::mem::take(&mut self.resolution_chain),
            otfs_driving_clause: None,
        };
        self.resolution_chain_pivots.clear();
        result
    }

    /// Return a consumed learned clause buffer for capacity reuse across conflicts.
    /// Called after arena insertion copies the data. CaDiCaL: clause.clear()
    /// in analyze.cpp:1092 preserves the vector's heap capacity.
    pub(crate) fn return_learned_buf(&mut self, mut buf: Vec<Literal>) {
        buf.clear();
        self.learned = buf;
    }

    /// Return a consumed resolution chain buffer for capacity reuse.
    pub(crate) fn return_chain_buf(&mut self, mut buf: Vec<u64>) {
        buf.clear();
        self.resolution_chain = buf;
    }

    #[cfg(test)]
    pub(crate) fn learned_capacity(&self) -> usize {
        self.learned.capacity()
    }

    #[cfg(test)]
    pub(crate) fn resolution_chain_capacity(&self) -> usize {
        self.resolution_chain.capacity()
    }

    /// Heap-backed buffer bytes used by conflict analysis state.
    ///
    /// Excludes the inline `ConflictAnalyzer` struct itself so callers can
    /// count the parent solver shell exactly once.
    #[cfg(test)]
    pub(crate) fn buffer_bytes(&self) -> usize {
        use std::mem::size_of;

        fn packed_bool_vec_bytes(capacity: usize) -> usize {
            capacity.div_ceil(8)
        }

        self.seen_to_clear.capacity() * size_of::<usize>()
            + self.learned.capacity() * size_of::<Literal>()
            + self.resolution_chain.capacity() * size_of::<u64>()
            + self.resolution_chain_pivots.capacity() * size_of::<Option<Literal>>()
            + packed_bool_vec_bytes(self.lbd_seen.capacity())
            + self.lbd_to_clear.capacity() * size_of::<usize>()
            + self.clause_buf.capacity() * size_of::<Literal>()
    }

    /// Resize internal buffers for variable compaction.
    /// Clear stale seen flags in var_data BEFORE emptying seen_to_clear.
    /// Without this, compact() orphans seen=true flags in var_data entries,
    /// causing counter underflow in subsequent conflict analysis (#7331).
    pub(crate) fn compact(&mut self, var_data: &mut [VarData]) {
        // Sparse-clear: reset seen flags using OLD indices (before remap).
        for &idx in &self.seen_to_clear {
            if idx < var_data.len() {
                var_data[idx].set_seen(false);
            }
        }
        self.seen_to_clear.clear();
        #[cfg(debug_assertions)]
        {
            self.seen_true_count = 0;
        }
        self.learned.clear();
        self.asserting_lit = None;
        self.resolution_chain.clear();
        self.resolution_chain_pivots.clear();
        self.lbd_seen.clear();
        self.lbd_to_clear.clear();
        self.clause_buf.clear();
        self.learned_max_level = 0;
        self.learned_max_swap_idx = usize::MAX;
        self.learned_level_tracking_valid = false;
    }
}

/// Reorder learned clause so lits[1] is at backtrack level (for 2WL correctness).
/// Production path: inline in `add_learned_clause`. This is for tests/Kani only.
pub(crate) fn reorder_for_watches(
    clause: &mut [Literal],
    var_data: &[VarData],
    backtrack_level: u32,
) {
    if clause.len() < 2 {
        return;
    }

    // Find a literal at the backtrack level (not the first one)
    for i in 2..clause.len() {
        if var_data[clause[i].variable().index()].level == backtrack_level {
            clause.swap(1, i);
            return;
        }
    }

    // If no exact match, find the highest level (should be at position 1)
    let mut max_idx = 1;
    let mut max_level = var_data[clause[1].variable().index()].level;
    for i in 2..clause.len() {
        let lit_level = var_data[clause[i].variable().index()].level;
        if lit_level > max_level {
            max_level = lit_level;
            max_idx = i;
        }
    }
    if max_idx != 1 {
        clause.swap(1, max_idx);
    }
}

#[allow(clippy::panic)]
#[cfg(test)]
#[path = "conflict_tests.rs"]
mod tests;

#[cfg(kani)]
#[path = "conflict_verification.rs"]
mod verification;
