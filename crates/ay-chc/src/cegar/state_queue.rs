// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Priority queue for CEGAR state expansion scheduling
//!
//! Reference: `reference/eldarica/src/main/scala/lazabs/horn/bottomup/AbstractState.scala:98-144`

use super::abstract_state::AbstractState;
use std::cmp::Ordering;
use std::collections::BinaryHeap;

/// Penalty added to postponed expansions to push them to the back of the queue.
/// Reference: Eldarica CEGAR.scala:70 `POSTPONED_EXPANSION_PENALTY = 1000000`
const POSTPONED_EXPANSION_PENALTY: i64 = 1_000_000;

/// An expansion to be processed by CEGAR
///
/// Contains the source states, clause index, and birth time
pub(super) struct Expansion {
    /// Source abstract states (clause body instantiation)
    pub(super) states: Vec<AbstractState>,

    /// Index of the clause being applied
    pub(super) clause_index: usize,

    /// Birth time for FIFO ordering within same priority
    pub(super) birth_time: u32,

    /// Whether this expansion leads to False (query clause)
    pub(super) is_query: bool,

    /// Priority penalty for postponed expansions (Eldarica-style).
    /// When refinement fails for a counterexample, the expansion is
    /// re-enqueued with a penalty instead of being discarded.
    /// Reference: `reference/eldarica/src/main/scala/lazabs/horn/bottomup/CEGAR.scala:374-388`
    penalty: i64,
}

impl Expansion {
    /// Create a new expansion
    pub(super) fn new(
        states: Vec<AbstractState>,
        clause_index: usize,
        birth_time: u32,
        is_query: bool,
    ) -> Self {
        Self {
            states,
            clause_index,
            birth_time,
            is_query,
            penalty: 0,
        }
    }

    /// Compute priority for this expansion
    ///
    /// Lower values = higher priority
    /// - Query clauses (leading to False) have highest priority (-10000)
    /// - Fewer predicates in source states = higher priority
    /// - Earlier birth time = higher priority
    /// - Penalty from postponed expansions pushes items to the back
    fn priority(&self) -> i64 {
        let query_bonus: i64 = if self.is_query { -10000 } else { 0 };

        let predicate_count: i64 = self.states.iter().map(|s| s.predicates.len() as i64).sum();

        query_bonus + predicate_count + i64::from(self.birth_time) + self.penalty
    }
}

/// Wrapper for BinaryHeap ordering (max-heap, so we negate priority)
struct PrioritizedExpansion(Expansion);

impl PartialEq for PrioritizedExpansion {
    fn eq(&self, other: &Self) -> bool {
        self.0.priority() == other.0.priority()
    }
}

impl Eq for PrioritizedExpansion {}

impl PartialOrd for PrioritizedExpansion {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for PrioritizedExpansion {
    fn cmp(&self, other: &Self) -> Ordering {
        // Reverse ordering: lower priority value = higher priority in heap
        other.0.priority().cmp(&self.0.priority())
    }
}

/// Priority queue for scheduling CEGAR state expansions
///
/// Prioritizes:
/// 1. Query clauses (can find counterexample)
/// 2. States with fewer predicates (more general)
/// 3. Earlier birth time (FIFO for same priority)
pub(super) struct StateQueue {
    /// Priority queue of pending expansions
    queue: BinaryHeap<PrioritizedExpansion>,

    /// Current time counter for birth timestamps
    time: u32,
}

impl StateQueue {
    /// Create a new empty state queue
    pub(super) fn new() -> Self {
        Self {
            queue: BinaryHeap::new(),
            time: 0,
        }
    }

    /// Check if the queue is empty
    pub(super) fn is_empty(&self) -> bool {
        self.queue.is_empty()
    }

    /// Increment the time counter
    pub(super) fn inc_time(&mut self) {
        self.time = self.time.saturating_add(1);
    }

    /// Number of pending expansions
    pub(super) fn len(&self) -> usize {
        self.queue.len()
    }

    /// Enqueue a new expansion
    pub(super) fn enqueue(
        &mut self,
        states: Vec<AbstractState>,
        clause_index: usize,
        is_query: bool,
    ) {
        let expansion = Expansion::new(states, clause_index, self.time, is_query);
        self.queue.push(PrioritizedExpansion(expansion));
    }

    /// Re-enqueue a counterexample expansion with a priority penalty.
    ///
    /// When refinement fails to produce new predicates, the expansion is
    /// pushed to the back of the queue instead of being discarded.
    /// This allows the solver to explore other paths first and revisit
    /// the postponed expansion later if needed.
    ///
    /// Reference: Eldarica CEGAR.scala:374-388 (POSTPONED_EXPANSION_PENALTY)
    pub(super) fn enqueue_postponed(
        &mut self,
        states: Vec<AbstractState>,
        clause_index: usize,
        is_query: bool,
    ) {
        let mut expansion = Expansion::new(states, clause_index, self.time, is_query);
        expansion.penalty += POSTPONED_EXPANSION_PENALTY;
        self.queue.push(PrioritizedExpansion(expansion));
    }

    /// Dequeue the highest-priority expansion
    pub(super) fn dequeue(&mut self) -> Option<Expansion> {
        self.queue.pop().map(|p| p.0)
    }
}

impl Default for StateQueue {
    fn default() -> Self {
        Self::new()
    }
}

#[allow(clippy::unwrap_used)]
#[cfg(test)]
#[path = "state_queue_tests.rs"]
mod tests;
