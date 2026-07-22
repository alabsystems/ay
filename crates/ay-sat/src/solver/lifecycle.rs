// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Variable lifecycle state machine.
//!
//! Ports CaDiCaL's `flags.hpp`/`flags.cpp` variable status tracking to AY.
//! Each variable has a lifecycle state that governs which solver operations
//! may touch it. This replaces the previous `eliminated: Vec<bool>` which
//! conflated BVE-eliminated and SCC-substituted variables.
//!
//! Reference: `reference/cadical/src/flags.hpp:44-71`, `flags.cpp:5-133`

/// Variable lifecycle state, matching CaDiCaL's `Flags::status`.
///
/// State transitions:
/// - `Active -> Fixed`: root-level unit propagation (permanent)
/// - `Active -> Eliminated`: bounded variable elimination (BVE)
/// - `Active -> Substituted`: equivalent literal substitution (SCC decompose)
/// - `{Eliminated, Substituted} -> Active`: reactivation (incremental push)
///
/// `Fixed` is permanent — variables assigned at decision level 0 can never be
/// unassigned or reactivated. CaDiCaL asserts `f.status != Flags::FIXED` in
/// `reactivate()` (`flags.cpp:92`).
///
/// Future extensions (add when implemented):
/// - `Pure`: pure literal elimination (reactivatable)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(u8)]
pub(crate) enum VarState {
    /// Variable is active in the solver.
    Active = 0,
    /// Variable permanently assigned at decision level 0 (non-reactivatable).
    /// CaDiCaL: `Flags::FIXED = 2` in `flags.hpp:47`.
    Fixed = 1,
    /// Variable was removed by bounded variable elimination (BVE).
    Eliminated = 2,
    /// Variable was removed by equivalent literal substitution (SCC decompose).
    Substituted = 3,
}

impl VarState {
    /// Returns `true` if the variable was removed by an equisatisfiable
    /// inprocessing transformation (BVE elimination or SCC substitution).
    ///
    /// Fixed (level-0 assigned) variables are NOT removed — they remain in
    /// clauses with valid watch lists. Use `is_inactive()` for the broader
    /// check that matches CaDiCaL's `!active()`.
    #[inline]
    pub(crate) fn is_removed(self) -> bool {
        matches!(self, Self::Eliminated | Self::Substituted)
    }

    /// Returns `true` if the variable is no longer active in the solver.
    ///
    /// Includes Fixed (permanently assigned at level 0), Eliminated (BVE),
    /// and Substituted (SCC decompose). Matches CaDiCaL's `!active()`.
    #[inline]
    pub(crate) fn is_inactive(self) -> bool {
        self != Self::Active
    }

    /// Returns `true` if the variable can be reactivated during incremental push.
    ///
    /// Fixed variables are permanent and can never be reactivated.
    /// CaDiCaL: `assert(f.status != Flags::FIXED)` in `reactivate()` (`flags.cpp:92`).
    #[inline]
    pub(crate) fn can_reactivate(self) -> bool {
        matches!(self, Self::Eliminated | Self::Substituted)
    }

    /// Returns `true` if the variable is fixed at decision level 0.
    #[inline]
    pub(crate) fn is_fixed(self) -> bool {
        self == Self::Fixed
    }
}

/// Per-variable lifecycle state array with transition methods.
///
/// Enforces valid transitions via debug assertions, matching CaDiCaL's
/// `mark_eliminated`, `mark_substituted`, and `reactivate` in `flags.cpp`.
#[derive(Clone)]
pub(crate) struct VarLifecycle {
    states: Vec<VarState>,
}

impl VarLifecycle {
    /// Create a lifecycle tracker for `num_vars` variables, all initially Active.
    pub(crate) fn new(num_vars: usize) -> Self {
        Self {
            states: vec![VarState::Active; num_vars],
        }
    }

    /// Returns `true` if the variable has been removed by inprocessing.
    /// Direct replacement for `self.eliminated[var_idx]`.
    #[inline]
    pub(crate) fn is_removed(&self, var_idx: usize) -> bool {
        self.states[var_idx].is_removed()
    }

    /// Transition: Active -> Fixed (level-0 unit propagation).
    ///
    /// Once fixed, a variable is permanently assigned and can never be
    /// reactivated. CaDiCaL: `Internal::mark_fixed` in `flags.cpp:5-32`.
    ///
    /// # Panics (debug only)
    /// Panics if the variable is not in `Active` state. Callers must guard
    /// with `!is_inactive()` (not just `!is_fixed()`) to avoid calling this
    /// on Eliminated/Substituted variables that receive level-0 assignments
    /// from conditioning or sweep after BVE.
    pub(crate) fn mark_fixed(&mut self, var_idx: usize) {
        debug_assert_eq!(
            self.states[var_idx],
            VarState::Active,
            "BUG: mark_fixed on non-active var {var_idx} (state: {:?})",
            self.states[var_idx]
        );
        self.states[var_idx] = VarState::Fixed;
    }

    /// Returns `true` if the variable is fixed at decision level 0.
    #[inline]
    pub(crate) fn is_fixed(&self, var_idx: usize) -> bool {
        self.states[var_idx].is_fixed()
    }

    /// Returns `true` if the variable is no longer active (Fixed, Eliminated, or Substituted).
    #[inline]
    pub(crate) fn is_inactive(&self, var_idx: usize) -> bool {
        self.states[var_idx].is_inactive()
    }

    /// Transition: Active -> Eliminated (BVE).
    ///
    /// CaDiCaL: `Internal::mark_eliminated` in `flags.cpp:36-47`
    pub(crate) fn mark_eliminated(&mut self, var_idx: usize) {
        debug_assert_eq!(
            self.states[var_idx],
            VarState::Active,
            "BUG: mark_eliminated on non-active var {var_idx} (state: {:?})",
            self.states[var_idx]
        );
        self.states[var_idx] = VarState::Eliminated;
    }

    /// Transition: Active -> Substituted (SCC decompose).
    ///
    /// CaDiCaL: `Internal::mark_substituted` in `flags.cpp:69-80`
    pub(crate) fn mark_substituted(&mut self, var_idx: usize) {
        debug_assert_eq!(
            self.states[var_idx],
            VarState::Active,
            "BUG: mark_substituted on non-active var {var_idx} (state: {:?})",
            self.states[var_idx]
        );
        self.states[var_idx] = VarState::Substituted;
    }

    /// Reactivate a previously removed variable.
    ///
    /// Only Eliminated and Substituted variables can be reactivated.
    ///
    /// CaDiCaL: `Internal::reactivate` in `flags.cpp:82-133`
    pub(crate) fn reactivate(&mut self, var_idx: usize) {
        debug_assert!(
            self.states[var_idx].can_reactivate(),
            "BUG: reactivate on var {var_idx} in non-reactivatable state {:?}",
            self.states[var_idx]
        );
        self.states[var_idx] = VarState::Active;
    }

    /// Number of tracked variables.
    pub(crate) fn len(&self) -> usize {
        self.states.len()
    }

    /// Whether a specific variable can be reactivated.
    pub(crate) fn can_reactivate(&self, var_idx: usize) -> bool {
        self.states[var_idx].can_reactivate()
    }

    /// Add a new variable (extends the array with Active state).
    pub(crate) fn push_active(&mut self) {
        self.states.push(VarState::Active);
    }

    /// Ensure the lifecycle array covers at least `num_vars` variables.
    pub(crate) fn ensure_num_vars(&mut self, num_vars: usize) {
        if self.states.len() < num_vars {
            self.states.resize(num_vars, VarState::Active);
        }
    }

    /// Heap-backed bytes used by the lifecycle state array.
    #[cfg(test)]
    pub(crate) fn heap_bytes(&self) -> usize {
        use std::mem::size_of;

        self.states.capacity() * size_of::<VarState>()
    }

    /// Revert all Fixed variables to Active.
    ///
    /// Called during `reset_search_state()` when all assignments are cleared.
    /// Fixed is a search-time concept; when the search is reset, previously
    /// fixed variables become unassigned and must be Active for the next solve.
    pub(crate) fn reset_fixed(&mut self) {
        for state in &mut self.states {
            if *state == VarState::Fixed {
                *state = VarState::Active;
            }
        }
    }

    /// Count variables removed by inprocessing (Eliminated + Substituted).
    ///
    /// Does not count Fixed variables — they are still in clauses.
    pub(crate) fn count_removed(&self) -> usize {
        self.states.iter().filter(|s| s.is_removed()).count()
    }

    /// Count variables still Active (not Fixed, Eliminated, or Substituted).
    ///
    /// This is the exact live-variable count (`num_vars - fixed - eliminated -
    /// substituted`) used by the post-collapse BVE eligibility re-derivation.
    /// It avoids the double-subtraction hazard of `num_vars - trail.len() -
    /// count_removed()`: removed variables can later receive level-0
    /// assignments (conditioning/sweep after BVE) and would then be counted
    /// twice. Matches CaDiCaL's `active()`.
    pub(crate) fn count_active(&self) -> usize {
        self.states
            .iter()
            .filter(|s| matches!(s, VarState::Active))
            .count()
    }

    /// Iterate over states with indices.
    pub(crate) fn iter_enumerated(&self) -> impl Iterator<Item = (usize, VarState)> + '_ {
        self.states.iter().enumerate().map(|(i, &s)| (i, s))
    }

    /// Provide a slice view for passing to external engines that still
    /// need a `&[VarState]`.
    pub(crate) fn as_slice(&self) -> &[VarState] {
        &self.states
    }
}
