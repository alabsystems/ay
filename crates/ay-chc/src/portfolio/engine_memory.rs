// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Per-lane memory shares for parallel portfolio engines (WP-F).
//!
//! Before this, the only memory signals were process-wide: the 95 % advisory
//! (`TermStore::global_memory_exceeded`, which cancels EVERY lane) and the
//! allocator's hard ceiling at 100 % (which ends the process with `memout`).
//! One engine growing without bound — measured: PDKIND's model-based
//! projection expanding a shared transition DAG per occurrence, 8 GiB in
//! 3 s — therefore took every other engine's answer with it.
//!
//! Each parallel lane now runs inside an `ay_sys::MemoryGroup` charged by the
//! global allocator for the lane's own thread:
//! * above [`LANE_SOFT_SHARE_PERCENT`] of the process limit the lane's own
//!   cancellation token is cancelled — that engine returns `Unknown` at its
//!   next checkpoint, the other lanes continue;
//! * above [`LANE_HARD_SHARE_PERCENT`] an engine that never polls is unwound
//!   at its next expression-walk step (`maybe_grow_expr_stack`), which the
//!   lane's `catch_unwind` turns into `Unknown`.
//!
//! Several lanes growing together cross no share while the process crosses
//! its budget; the memory governor (`ay_sys::memory_governor`) then SHEDS the
//! lane holding the most live heap — the same cancel and unwind, chosen by
//! the process's pressure — and the others continue. Each lane registers its
//! engine name for that census.
//!
//! The process-wide signals stay in place as the last resort. A cancelled or
//! unwound lane only ever produces `Unknown`; no verdict path changes.

use crate::CancellationToken;

/// Share of the process memory limit one lane may hold before it alone is
/// cancelled.
pub(crate) const LANE_SOFT_SHARE_PERCENT: usize = 50;

/// Share beyond which a lane that did not stop cooperatively is unwound.
pub(crate) const LANE_HARD_SHARE_PERCENT: usize = 75;

/// Byte limits of one lane's memory group.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct LaneMemoryLimits {
    pub(crate) soft: usize,
    pub(crate) hard: usize,
}

impl LaneMemoryLimits {
    /// The lane shares of the configured process memory limit; `None` when no
    /// limit is set (library use, uncapped runs).
    pub(crate) fn from_process_limit() -> Option<Self> {
        let limit = ay_sys::get_process_memory_limit();
        (limit != 0).then(|| Self {
            soft: limit / 100 * LANE_SOFT_SHARE_PERCENT,
            hard: limit / 100 * LANE_HARD_SHARE_PERCENT,
        })
    }
}

/// The calling thread's lane accounting, active until dropped (on that thread).
pub(crate) struct EngineMemoryLane {
    scope: ay_sys::MemoryGroupScope,
}

impl EngineMemoryLane {
    /// Enter a memory group named `label` whose soft limit cancels `token`
    /// (this lane only: the group sets the token's own flag, which only this
    /// token and its descendants observe).
    pub(crate) fn enter(
        label: &'static str,
        limits: Option<LaneMemoryLimits>,
        token: &CancellationToken,
    ) -> Option<Self> {
        let limits = limits?;
        let group =
            ay_sys::MemoryGroup::named(label, limits.soft, limits.hard, token.interrupt_flag());
        Some(Self {
            scope: ay_sys::enter_memory_group(group),
        })
    }

    /// Whether this lane crossed its soft share or was shed by the memory
    /// governor (and was cancelled for it).
    pub(crate) fn tripped(&self) -> bool {
        self.scope.group().soft_tripped() || self.shed()
    }

    /// Whether the memory governor shed this lane.
    pub(crate) fn shed(&self) -> bool {
        self.scope.group().was_shed()
    }

    /// Peak live bytes charged to the lane, in MiB (reporting only).
    pub(crate) fn peak_mib(&self) -> isize {
        self.scope.group().note_peak();
        self.scope.group().peak_bytes() / (1024 * 1024)
    }
}
