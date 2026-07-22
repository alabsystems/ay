// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Walk/warmup phase-initialization state for hot/cold field separation (#5090).
//!
//! These fields are used during startup phase initialization and periodic
//! rephasing, not during the BCP hot loop. Grouping them shrinks the top-level
//! `Solver` shell while keeping the state inline and cache-local.

use super::constants::WALK_DEFAULT_LIMIT;
use crate::walk::WalkStats;
use crate::warmup::WarmupStats;

/// Walk-based and warmup-based phase initialization state.
#[derive(Clone)]
pub(crate) struct PhaseInitState {
    /// Walk statistics.
    pub(super) walk_stats: WalkStats,
    /// Whether walk-based phase initialization is enabled.
    pub(super) walk_enabled: bool,
    /// Whether startup walk phase initialization may run.
    pub(super) startup_walk_enabled: bool,
    /// Walk tick limit (effort per walk round).
    pub(super) walk_limit: u64,
    /// Search tick watermark used to budget rephase walk effort.
    pub(super) walk_last_ticks: u64,
    /// Previous walk best phases for continuity across rephase operations.
    pub(super) walk_prev_phase: Vec<bool>,
    /// Warmup statistics.
    pub(super) warmup_stats: WarmupStats,
    /// Whether warmup-based phase initialization is enabled.
    pub(super) warmup_enabled: bool,
    /// Whether startup warmup phase initialization may run.
    pub(super) startup_warmup_enabled: bool,
}

impl PhaseInitState {
    /// Create the walk/warmup state for `num_vars` variables.
    pub(crate) fn new(num_vars: usize) -> Self {
        Self {
            walk_stats: WalkStats::default(),
            walk_enabled: true,
            startup_walk_enabled: true,
            walk_limit: WALK_DEFAULT_LIMIT,
            walk_last_ticks: 0,
            walk_prev_phase: vec![false; num_vars],
            warmup_stats: WarmupStats::default(),
            warmup_enabled: true,
            startup_warmup_enabled: true,
        }
    }
}
