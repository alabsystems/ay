// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Learned-clause deletion/mutation hook scaffold for gated future experiments.
//!
//! The active learned-clause contract is profile-only: no native propagator is
//! installed into SAT propagation today. If a future external code generation experiment
//! crosses the required proof, telemetry, deletion, and fail-closed competition
//! gates, clause deletion or mutation must invalidate any installed artifact
//! before scalar SAT state can change underneath it.
//!
//! This scaffold lets tests and future integration code model that invalidation
//! boundary without reviving the retired BCP/watch JIT path.

#![allow(dead_code)] // Future gated learned-clause runtime invalidation hook.

/// Opaque identifier for a future learned-clause runtime artifact.
///
/// The profile-only path does not issue these. Future external code generation dispatch, if
/// it crosses the required gates, can use this to locate the corresponding
/// invalidation record.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct PropagatorId(pub(crate) u32);

impl PropagatorId {
    /// Construct a new propagator id from a raw index.
    ///
    /// The current profile-only path does not assign these; the constructor
    /// exists so downstream code can mock invalidation events in tests.
    #[must_use]
    pub const fn new(raw: u32) -> Self {
        Self(raw)
    }

    /// Raw index for the artifact.
    #[must_use]
    pub const fn raw(self) -> u32 {
        self.0
    }
}

/// Tracks which future learned-clause runtime artifacts have been marked dead.
///
/// This is intentionally inert today. A native dispatch experiment must attach
/// real artifact ownership and reclamation before it can execute.
#[derive(Debug, Default)]
pub struct DeletionHook {
    dead: Vec<PropagatorId>,
}

impl DeletionHook {
    /// Create an empty deletion hook.
    #[must_use]
    pub fn new() -> Self {
        Self { dead: Vec::new() }
    }

    /// Mark an artifact dead. The current scaffold records the id only.
    pub fn mark_dead(&mut self, id: PropagatorId) {
        self.dead.push(id);
    }

    /// Number of artifacts pending invalidation handling.
    #[must_use]
    pub fn pending(&self) -> usize {
        self.dead.len()
    }

    /// Drain the pending list.
    pub fn drain_pending(&mut self) -> Vec<PropagatorId> {
        std::mem::take(&mut self.dead)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn mark_dead_increments_pending() {
        let mut hook = DeletionHook::new();
        assert_eq!(hook.pending(), 0);
        hook.mark_dead(PropagatorId::new(0));
        hook.mark_dead(PropagatorId::new(1));
        assert_eq!(hook.pending(), 2);
    }

    #[test]
    fn drain_pending_empties_the_list() {
        let mut hook = DeletionHook::new();
        hook.mark_dead(PropagatorId::new(7));
        hook.mark_dead(PropagatorId::new(42));
        let drained = hook.drain_pending();
        assert_eq!(drained.len(), 2);
        assert_eq!(hook.pending(), 0);
        assert_eq!(drained[0].raw(), 7);
        assert_eq!(drained[1].raw(), 42);
    }

    #[test]
    fn propagator_id_roundtrips_raw() {
        assert_eq!(PropagatorId::new(123).raw(), 123);
    }
}
