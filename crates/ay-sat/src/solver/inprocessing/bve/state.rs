// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared scratch buffers and counters for the BVE body helpers.

use super::super::super::*;
use crate::kani_compat::DetHashSet as HashSet;

#[derive(Default)]
pub(super) struct BveBodyStats {
    pub total_eliminations: usize,
    pub bw_subsumed_total: u64,
    pub bw_strengthened_total: u64,
    pub bw_satisfied_total: u64,
    pub bw_checks_total: u64,
    pub resolvents_total: u64,
    /// Backward-subsumed clauses successfully deleted (#8367).
    pub bw_subsumed_deleted: u64,
    /// Number of backward subsumption cascade rounds that ran beyond
    /// the initial round (CaDiCaL backward.cpp:202 re-enqueue pattern).
    pub bw_cascade_rounds: u64,
}

#[derive(Default)]
pub(crate) struct BveBodyScratch {
    pub pos_occs: Vec<usize>,
    pub neg_occs: Vec<usize>,
    pub kept_strengthened: Vec<usize>,
    pub sat_buf: Vec<usize>,
    pub old_lits_buf: Vec<Literal>,
    pub new_lits_buf: Vec<Literal>,
    pub add_buf: Vec<Literal>,
    pub otfs_old_clauses: Vec<(usize, Literal, Vec<Literal>)>,
    /// Resolvent clause indices added during this round, collected for
    /// backward subsumption between rounds (CaDiCaL backward.cpp).
    pub resolvent_indices: Vec<usize>,
    /// Clause indices already strengthened in the current backward
    /// subsumption batch. Used to prevent double-strengthening when
    /// two resolvents both match the same clause (#8223).
    pub bw_strengthened_seen: HashSet<usize>,
    /// Variables eliminated during this BVE phase (#3521). Used for
    /// occ-guided post-elimination GC: instead of scanning all clauses,
    /// look up only clauses containing these variables via gc_occ.
    pub eliminated_vars: Vec<Variable>,
    /// Re-enqueue buffer for backward subsumption cascade (#8216).
    /// Strengthened clauses from one backward subsumption batch are
    /// collected here and used as the source set for the next cascade
    /// round (CaDiCaL backward.cpp:202 `eliminator.enqueue(d)` pattern).
    pub bw_cascade_queue: Vec<usize>,
}

impl BveBodyScratch {
    /// Clear all buffers for reuse between BVE rounds (#8602).
    /// Retains allocated capacity to avoid re-allocation.
    pub(crate) fn clear(&mut self) {
        self.pos_occs.clear();
        self.neg_occs.clear();
        self.kept_strengthened.clear();
        self.sat_buf.clear();
        self.old_lits_buf.clear();
        self.new_lits_buf.clear();
        self.add_buf.clear();
        self.otfs_old_clauses.clear();
        self.resolvent_indices.clear();
        self.bw_strengthened_seen.clear();
        self.eliminated_vars.clear();
        self.bw_cascade_queue.clear();
    }
}
