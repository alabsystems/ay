// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Proof obligation types for PDR solver.

use crate::smt::SmtValue;
use crate::{ChcExpr, PredicateId};
use ay_core::kani_compat::DetHashMap as FxHashMap;
use std::cmp::Ordering;

use super::derivation::DerivationId;

/// Kind of proof obligation (GSpacer global guidance, CAV'20).
///
/// `Must` pobs are the classic PDR obligations: root query states and their
/// predecessors. Blocking all of them is required for Safe; reaching init
/// through a query-derived must-pob chain yields a counterexample.
///
/// `MaySubsume` / `MayConjecture` pobs are speculative generalizations posted
/// by the global generalizer (cluster SUBSUME / CONJECTURE rules). Blocking
/// one yields an extra lemma through the normal inductiveness-checked path;
/// failing to block one is silently ignored.
///
/// SOUNDNESS-CRITICAL: may-pobs must NEVER contribute to counterexample
/// reconstruction — Unsafe verdicts flow only through must-pob traces
/// (see the `is_may()` guards in `solver/strengthen.rs`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum PobKind {
    /// Classic PDR obligation (query-derived or predecessor).
    Must,
    /// GSpacer SUBSUME rule: conjectured generalization of a lemma cluster.
    MaySubsume,
    /// GSpacer CONJECTURE rule: pob split along a cluster's mono-var literal.
    MayConjecture,
}

/// `AY_CHC_MAY_POB` kill-switch (default ON; only the literal "0" disables).
pub(crate) fn may_pob_env_enabled() -> bool {
    // B27: CLI-owned (--chc-no-may-pob); env retired.
    crate::ab_switches::get().may_pob
}

/// Pure parser for the `AY_CHC_MAY_POB` kill-switch value (unit-testable
/// without process-global env mutation).
#[cfg(test)]
pub(crate) fn may_pob_enabled_from_env_value(value: Option<&str>) -> bool {
    value != Some("0")
}

/// A proof obligation: state to prove unreachable
#[derive(Debug, Clone)]
pub(crate) struct ProofObligation {
    /// Predicate
    pub(crate) predicate: PredicateId,
    /// State condition
    pub(crate) state: ChcExpr,
    /// Monotonic ID assigned when enqueued (deterministic tie-breaker).
    pub(crate) queue_id: u64,
    /// Frame level
    pub(crate) level: usize,
    /// Depth in search (for prioritization)
    pub(crate) depth: usize,
    /// Clause index (in `ChcProblem::clauses()`) used to derive this fact.
    /// None indicates a root obligation (e.g., query state).
    pub(crate) incoming_clause: Option<usize>,
    /// Clause index (in `ChcProblem::clauses()`) for the query that introduced this obligation.
    /// Set only on the root of an obligation chain.
    pub(crate) query_clause: Option<usize>,
    /// Parent obligation (for counterexample construction)
    pub(crate) parent: Option<Box<Self>>,
    /// SMT model for this state (for counterexample assignment extraction)
    pub(crate) smt_model: Option<FxHashMap<String, SmtValue>>,
    /// Optional derivation handle for multi-body clause tracking.
    /// When set, this POB is part of a derivation that tracks progress
    /// through a hyperedge (rule with multiple body predicates).
    /// Scaffolding for #1275; will be used when derivation tracking completes.
    pub(crate) derivation_id: Option<DerivationId>,
    /// Obligation kind: classic MUST pob or speculative MAY pob (GSpacer).
    pub(crate) kind: PobKind,
    /// Remaining gas for MAY-pob work (child descent / level promotion).
    /// Always 0 for MUST pobs; a MAY pob with exhausted gas is dropped
    /// silently instead of descending further.
    pub(crate) gas: u32,
    /// Frame level the spawning heuristic ultimately wants a lemma at.
    /// Defaults to `level`; only meaningful when `kind != Must`.
    pub(crate) desired_level: usize,
}

impl ProofObligation {
    /// Maximum weakness level for spurious CEX retries (same as Z3 Spacer).
    pub(crate) const MAX_WEAKNESS: u8 = 10;

    pub(crate) fn new(predicate: PredicateId, state: ChcExpr, level: usize) -> Self {
        Self {
            predicate,
            state,
            queue_id: 0,
            level,
            depth: 0,
            incoming_clause: None,
            query_clause: None,
            parent: None,
            smt_model: None,
            derivation_id: None,
            kind: PobKind::Must,
            gas: 0,
            desired_level: level,
        }
    }

    /// Turn this obligation into a MAY pob (GSpacer SUBSUME/CONJECTURE).
    ///
    /// `desired_level` is clamped up to the pob's own level so promotion
    /// (`may_promotion_after_block`) never targets below where the pob starts.
    pub(crate) fn with_may(mut self, kind: PobKind, gas: u32, desired_level: usize) -> Self {
        debug_assert!(
            kind != PobKind::Must,
            "BUG: with_may requires a MAY kind, got {kind:?}"
        );
        self.kind = kind;
        self.gas = gas;
        self.desired_level = desired_level.max(self.level);
        self
    }

    /// Whether this is a speculative MAY pob (never a counterexample source).
    pub(crate) fn is_may(&self) -> bool {
        self.kind != PobKind::Must
    }

    /// MAY-pob level promotion after a successful block at `applied_level`.
    ///
    /// Mirrors Spacer's re-enqueue of a blocked may-pob toward its
    /// `desired_level`: returns a copy at `applied_level + 1` (one unit of
    /// gas spent) as long as gas remains and the desired level (clamped to
    /// the current frame ceiling `max_level`) has not been reached. Each
    /// promoted copy is re-verified by the normal blocking machinery, so
    /// this is verdict-neutral.
    pub(crate) fn may_promotion_after_block(
        &self,
        applied_level: usize,
        max_level: usize,
    ) -> Option<Self> {
        if !self.is_may() || self.gas == 0 {
            return None;
        }
        if applied_level >= self.desired_level.min(max_level) {
            return None;
        }
        let mut promoted = self.clone();
        promoted.level = applied_level + 1;
        promoted.gas -= 1;
        Some(promoted)
    }

    /// Scaffolding for #1275; will be used when derivation tracking completes.
    pub(crate) fn with_derivation_id(mut self, id: DerivationId) -> Self {
        self.derivation_id = Some(id);
        self
    }

    pub(crate) fn with_incoming_clause(mut self, clause_index: usize) -> Self {
        self.incoming_clause = Some(clause_index);
        self
    }

    pub(crate) fn with_query_clause(mut self, clause_index: usize) -> Self {
        self.query_clause = Some(clause_index);
        self
    }

    pub(crate) fn with_parent(mut self, parent: Self) -> Self {
        self.depth = parent.depth + 1;
        self.parent = Some(Box::new(parent));
        self
    }

    pub(crate) fn with_smt_model(mut self, model: FxHashMap<String, SmtValue>) -> Self {
        self.smt_model = Some(model);
        self
    }

    /// Priority key: (level, predicate, queue_id). Lower tuple values are higher priority.
    pub(crate) fn priority_key(&self) -> (usize, usize, u64) {
        (self.level, self.predicate.index(), self.queue_id)
    }
}

/// Wrapper for POB in priority queue - lower levels processed first
#[derive(Debug)]
pub(crate) struct PriorityPob(pub(crate) ProofObligation);

impl PartialEq for PriorityPob {
    fn eq(&self, other: &Self) -> bool {
        self.0.priority_key() == other.0.priority_key()
    }
}

impl Eq for PriorityPob {}

impl PartialOrd for PriorityPob {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for PriorityPob {
    fn cmp(&self, other: &Self) -> Ordering {
        // Reverse ordering: lower level = higher priority (comes out first from max-heap)
        // Also use predicate as tiebreaker (consistent with Golem)
        other.0.priority_key().cmp(&self.0.priority_key())
    }
}

/// Custom Drop to prevent stack overflow on deep obligation chains.
/// Default drop would recursively drop Box<ProofObligation> parents,
/// using O(N) stack frames for a chain of length N. This iterative
/// implementation uses O(1) stack space.
impl Drop for ProofObligation {
    fn drop(&mut self) {
        let mut current = self.parent.take();
        while let Some(mut boxed) = current {
            current = boxed.parent.take();
            // boxed drops here with no parent, so no recursion
        }
    }
}

#[allow(clippy::unwrap_used)]
#[cfg(test)]
mod tests;
