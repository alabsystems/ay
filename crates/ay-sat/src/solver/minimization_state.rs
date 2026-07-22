// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Clause minimization and LRAT chain work arrays (#5090).
//!
//! Groups conflict analysis minimization state into a single struct to
//! separate it from the Solver's hot BCP fields. These arrays are only
//! accessed during conflict analysis (per-conflict, not per-propagation).

use crate::literal::Literal;

/// Per-level seen tracking: count of seen literals and minimum trail
/// position, packed into one 8-byte struct so the minimize hot path pays a
/// single indexed load (CaDiCaL `level.hpp` keeps `seen.count` and
/// `seen.trail` adjacent in `Level` for the same reason). Instruction-shave
/// #3: previously two parallel arrays (`Vec<u32>` + `Vec<usize>`) costing
/// two bounds-checked loads on two cache lines per query.
///
/// `trail` uses `u32::MAX` as the "unset" sentinel. Trail positions are
/// `VarData::trail_pos` values (u32), and real positions never reach
/// `u32::MAX`, so `min`-tracking and `<=` abort comparisons are exactly
/// equivalent to the old `usize::MAX` sentinel.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct LevelSeen {
    /// Number of seen literals on this level (CaDiCaL `Level.seen.count`).
    pub count: u32,
    /// Minimum trail position among seen literals on this level
    /// (CaDiCaL `Level.seen.trail`). `u32::MAX` = none seen yet.
    pub trail: u32,
}

impl LevelSeen {
    /// Empty tracking state (no literal seen on this level).
    pub(crate) const EMPTY: Self = Self {
        count: 0,
        trail: u32::MAX,
    };
}

/// Clause minimization and LRAT chain work arrays (reused per-conflict).
///
/// Contains the packed minimize flags, per-level tracking arrays, and
/// LRAT chain support. All accessed only during conflict analysis and
/// clause minimization, never during BCP.
///
/// Reference: CaDiCaL `minimize.cpp`, `level.hpp` (seen tracking).
#[derive(Clone)]
pub(crate) struct MinimizationState {
    /// Packed minimize flags per variable. Access via `MIN_*` constants.
    /// Bits: poison(0x01), removable(0x02), visited(0x04), keep(0x08),
    /// LRAT_A(0x10), LRAT_B(0x20).
    pub minimize_flags: Vec<u8>,
    /// List of variable indices to clear after minimization.
    pub minimize_to_clear: Vec<usize>,
    /// Per-level seen tracking during conflict analysis (CaDiCaL
    /// `level.hpp` `Level.seen`). Used by minimize early-abort.
    pub level_seen: Vec<LevelSeen>,
    /// Dirty list of decision levels touched during analysis (for cleanup).
    pub level_seen_to_clear: Vec<u32>,
    /// Incrementally derived shrink-prescan bit (#8790): set by
    /// `track_level_seen` when a non-conflict-level decision level is seen a
    /// second time (or a tracked literal has a stale trail position). While
    /// `level_seen_flag_valid`, equals what
    /// `learned_clause_has_repeated_non_uip_level` would return at finalize,
    /// eliminating that O(clause_len) prescan. Reset by `clear_level_seen`
    /// and at analysis entry.
    pub level_seen_repeated_non_uip: bool,
    /// True when the current conflict analysis started with clean
    /// `level_seen` state, making `level_seen_repeated_non_uip` exact.
    /// The rare ghost-drop bailout returns without `clear_level_seen`,
    /// leaving stale counters; finalize then falls back to the prescan.
    pub level_seen_flag_valid: bool,
    /// Sparse cleanup list for LRAT bits in minimize_flags.
    pub lrat_to_clear: Vec<usize>,
    /// Reusable removed-literal snapshot for LRAT removed-literal chains.
    pub lrat_original_learned_buf: Vec<Literal>,
    /// Maximum recursion depth for minimization.
    pub minimize_depth_limit: u32,
    /// Per-level seen tracking over the learned clause literals only
    /// (CaDiCaL `l.seen` as populated by `minimize_clause`). Fallback data
    /// for direct minimize calls outside the analyze pipeline.
    pub minimize_level_seen: Vec<LevelSeen>,
    /// Sparse cleanup list for minimize_level_seen.
    pub minimize_levels_to_clear: Vec<u32>,
}

impl MinimizationState {
    /// Create minimization state for `num_vars` variables.
    pub(crate) fn new(num_vars: usize) -> Self {
        Self {
            minimize_flags: vec![0u8; num_vars],
            minimize_to_clear: Vec::with_capacity(num_vars),
            level_seen: Vec::new(),
            level_seen_to_clear: Vec::new(),
            level_seen_repeated_non_uip: false,
            level_seen_flag_valid: false,
            lrat_to_clear: Vec::with_capacity(num_vars),
            lrat_original_learned_buf: Vec::new(),
            minimize_depth_limit: 1000, // CaDiCaL default
            minimize_level_seen: vec![LevelSeen::EMPTY; num_vars + 1],
            minimize_levels_to_clear: Vec::with_capacity(64),
        }
    }

    /// Grow the analysis-phase per-level tracking to cover `lvl`.
    ///
    /// Cold path of `track_level_seen`: decision levels can exceed the
    /// initial capacity; growth happens O(log) times per solve, so it is
    /// kept out of the inlined hot path.
    #[cold]
    #[inline(never)]
    pub(crate) fn grow_level_seen(&mut self, lvl: usize) {
        self.level_seen.resize(lvl + 1, LevelSeen::EMPTY);
    }
}
