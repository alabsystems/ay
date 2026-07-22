// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Types and constants for the forward subsumption engine.

use crate::literal::Literal;

/// Statistics for subsumption operations.
#[derive(Debug, Clone, Default)]
#[non_exhaustive]
pub struct SubsumeStats {
    /// Number of forward-subsumption rounds started
    pub rounds: u64,
    /// Number of rounds that processed the full scheduled candidate set
    pub completed_rounds: u64,
    /// Total clauses scheduled as forward-subsumption candidates
    pub candidates_scheduled: u64,
    /// Clauses removed by forward subsumption
    pub forward_subsumed: u64,
    /// Literals removed by self-subsumption (strengthening)
    pub strengthened_literals: u64,
    /// Clauses strengthened by self-subsumption
    pub strengthened_clauses: u64,
    /// Subsumption checks performed
    pub checks: u64,
    /// Native subsumption check applications.
    ///
    /// Always 0: the subsumption JIT dispatch was removed (2026-07-14 triage,
    /// per the #8517 order). Retained so the `sat.subsumption_native_applications`
    /// stats key keeps its schema.
    pub native_applications: u64,
}

/// Result of a subsumption round.
#[derive(Debug, Clone)]
pub(crate) struct SubsumeResult {
    /// Subsumed clause pairs: (subsumed_idx, subsumer_idx).
    /// The subsumer identity is needed for irredundant promotion logic
    /// (CaDiCaL subsume.cpp:133-149).
    pub subsumed: Vec<(usize, usize)>,
    /// Clauses strengthened: (clause_idx, new_literals, subsumer_clause_idx).
    pub strengthened: Vec<(usize, Vec<Literal>, usize)>,
    /// Whether the round completed all scheduled candidates without hitting
    /// the effort limit. CaDiCaL subsume.cpp:590: dirty bits are only reset
    /// when the round completed; incomplete rounds preserve dirty state so
    /// the next round picks up where this one left off.
    pub completed: bool,
    /// Number of clauses scheduled as candidates in this round.
    pub candidates_scheduled: u64,
    /// Number of subsumption checks performed in this round.
    pub checks_performed: u64,
}

impl Default for SubsumeResult {
    fn default() -> Self {
        Self::new()
    }
}

impl SubsumeResult {
    pub(crate) fn new() -> Self {
        Self {
            subsumed: Vec::new(),
            strengthened: Vec::new(),
            completed: false,
            candidates_scheduled: 0,
            checks_performed: 0,
        }
    }
}

/// Dynamic thresholds from the last `reduce_db()` pass, used to gate
/// subsumption candidates via CaDiCaL's `likely_to_be_kept_clause` predicate.
/// Reference: `reference/cadical/src/internal.hpp:1053-1069`.
#[derive(Debug, Clone, Copy)]
pub(crate) struct KeptThresholds {
    /// Dynamic tier2 LBD boundary (CaDiCaL `tier2[stable]`).
    pub tier2_lbd: u32,
    /// Max glue among clauses kept at last reduce (CaDiCaL `lim.keptglue`).
    pub kept_glue: u32,
    /// Max size among clauses kept at last reduce (CaDiCaL `lim.keptsize`).
    pub kept_size: u32,
}

impl KeptThresholds {
    /// All-inclusive thresholds: every clause passes the kept check.
    pub(crate) fn all_inclusive() -> Self {
        Self {
            tier2_lbd: u32::MAX,
            kept_glue: u32::MAX,
            kept_size: u32::MAX,
        }
    }
}

/// Max clause length to consider for subsumption (CaDiCaL subsumeclslim=100).
pub(super) const SUBSUME_CLS_LIM: usize = 100;

/// Max one-watch occ-list length for non-binary connection (CaDiCaL subsumeocclim=100).
pub(super) const SUBSUME_OCC_LIM: usize = 100;

/// Default check limit.
pub(super) const DEFAULT_CHECK_LIMIT: u64 = 10_000_000;

/// Binary clause entry in the flat per-literal bin table.
/// Stores (other_literal, clause_index) for O(1) marked-lookup subsumption.
#[derive(Clone, Copy)]
pub(super) struct Bin {
    pub(super) other: Literal,
    pub(super) clause_idx: usize,
}
