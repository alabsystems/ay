// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! CaDiCaL-style one-watch forward subsumption (subsume.cpp port).
//!
//! Forward subsumption: for each candidate clause C, check whether any
//! existing smaller-or-equal clause D subsumes C or can strengthen C.
//! Only one literal per clause is connected in occurrence lists (one-watch
//! scheme, SDM'11 Bayardo/Lintao Zhang). Incremental via per-variable
//! `subsume_dirty` bits: only clauses with >= 2 dirty variables are
//! scheduled, and only occ-lists of dirty variables are traversed.
//!
//! Split into submodules:
//! - `types`: data types and constants
//! - `check`: marking and subsumption check logic
//! - `forward`: one-watch forward subsumption round (scheduling + connection)
//!
//! Reference: `reference/cadical/src/subsume.cpp` lines 335-602.

mod check;
mod forward;
pub(crate) mod types;

#[cfg(feature = "jit")]
pub(crate) mod simd_prepass;

#[cfg(test)]
mod tests;

pub use types::SubsumeStats;
use types::{Bin, DEFAULT_CHECK_LIMIT};
pub(crate) use types::{KeptThresholds, SubsumeResult};

use crate::clause_arena::ClauseArena;
use crate::occ_list::OccList;

/// CaDiCaL-style one-watch forward subsumption engine.
///
/// Unlike the old backward engine, this builds occurrence lists
/// incrementally during the forward pass (one literal per clause)
/// and uses per-variable dirty bits for incremental scheduling.
pub(crate) struct Subsumer {
    /// Per-variable mark array. Indexed by variable index.
    /// 0 = unmarked, `lit.0 + 1` = marked with that literal's polarity.
    marks: Vec<u32>,
    /// Statistics.
    stats: SubsumeStats,
    /// Max subsumption checks per round (0 = unlimited).
    check_limit: u64,
    /// Checks performed in current round.
    round_checks: u64,
    /// Reusable schedule buffer (avoids per-round allocation).
    schedule: Vec<(usize, usize)>,
    /// Reusable occurrence list buffer (avoids per-round allocation).
    occs: Vec<Vec<usize>>,
    /// Reusable binary clause table buffer (avoids per-round allocation).
    bins: Vec<Vec<Bin>>,
    /// Per-literal occurrence count in scheduled clauses (CaDiCaL noccs).
    /// Used to sort connected clause literals by ascending frequency so
    /// subsumption checks fail faster on rare literals.
    noccs: Vec<u64>,
    /// Full per-literal occurrence lists for "new clause already subsumed"
    /// queries used by BVE gate resolution.
    full_occs: OccList,
}

impl Subsumer {
    /// Create a new subsumption engine for `num_vars` variables.
    pub(crate) fn new(num_vars: usize) -> Self {
        Self {
            marks: vec![0; num_vars],
            stats: SubsumeStats::default(),
            check_limit: DEFAULT_CHECK_LIMIT,
            round_checks: 0,
            schedule: Vec::new(),
            occs: Vec::new(),
            bins: Vec::new(),
            noccs: Vec::new(),
            // Sized on first use: `OccList::add_clause` grows to cover each
            // literal it sees, and `get` is bounds-safe, so nothing has to
            // pre-size this. Eagerly it costs ~128 resident bytes per
            // variable at solver construction, on every instance, whether or
            // not this engine ever runs.
            full_occs: OccList::new(0),
        }
    }

    /// Ensure buffers can handle `num_vars` variables.
    pub(crate) fn ensure_num_vars(&mut self, num_vars: usize) {
        if self.marks.len() < num_vars {
            self.marks.resize(num_vars, 0);
        }
        self.full_occs.ensure_num_vars(num_vars);
    }

    #[inline]
    fn check_limit_reached(&self) -> bool {
        self.check_limit > 0 && self.round_checks >= self.check_limit
    }

    /// Set the per-round check limit (CaDiCaL: proportional to propagations).
    pub(crate) fn set_check_limit(&mut self, limit: u64) {
        self.check_limit = limit;
    }

    pub(crate) fn stats(&self) -> &SubsumeStats {
        &self.stats
    }

    /// Restore previously saved statistics after compaction recreates the engine.
    pub(crate) fn restore_stats(&mut self, stats: SubsumeStats) {
        self.stats = stats;
    }

    /// No-op in one-watch engine. Kept for backward compatibility with
    /// preprocessing (`config.rs`) which calls `rebuild` before `run_subsumption`.
    pub(crate) fn rebuild(&mut self, clauses: &ClauseArena) {
        self.full_occs.clear();
        for idx in clauses.indices() {
            if clauses.is_dead(idx) {
                continue;
            }
            self.full_occs.add_clause(idx, clauses.literals(idx));
        }
    }

    /// Run subsumption (backward-compatible API for preprocessing + inprocessing).
    ///
    /// Delegates to the one-watch forward algorithm with all variables marked dirty
    /// and all vals=0 (unassigned).
    pub(crate) fn run_subsumption(
        &mut self,
        clauses: &mut ClauseArena,
        freeze_counts: &[u32],
        _start_idx: usize,
        _max_clauses: usize,
    ) -> SubsumeResult {
        let num_vars = self.marks.len();
        let all_dirty = vec![true; num_vars];
        let all_unassigned = vec![0i8; num_vars * 2];
        self.run_forward_subsumption(
            clauses,
            freeze_counts,
            &all_dirty,
            &all_unassigned,
            KeptThresholds::all_inclusive(),
        )
    }
}
