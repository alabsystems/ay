// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Facade for entry-related inductiveness checks.
//!
//! Preserves the `PdrSolver` method surface while moving the implementation
//! into focused sibling modules.

mod cegar;
mod conditioned_self;
mod entry_check;
mod predecessor_context;
mod strict_self;

use crate::pdr::solver::{EntryCegarDischarge, PdrSolver};
use crate::{ChcExpr, PredicateId};

impl PdrSolver {
    /// Strict self-inductiveness check WITHOUT frame strengthening.
    ///
    /// Unlike `is_self_inductive_blocking`, this does NOT retry with frame[1] lemmas
    /// when the base check fails. A lemma must be self-inductive purely from its own
    /// semantics. Used in model construction to avoid including lemmas that are only
    /// inductive relative to other (potentially non-inductive) frame lemmas.
    ///
    /// Part of #2059 - fix model verification for multi-predicate benchmarks.
    pub(in crate::pdr::solver) fn is_strictly_self_inductive_blocking(
        &mut self,
        blocking_formula: &ChcExpr,
        predicate: PredicateId,
    ) -> bool {
        strict_self::is_strictly_self_inductive_blocking(self, blocking_formula, predicate)
    }

    /// Check if a blocking formula is self-inductive, with an optional entry domain constraint.
    ///
    /// For predicates without fact clauses (phase-chain predicates), adding the entry domain
    /// constraint restricts the pre-state space to reachable states from predecessor predicates.
    /// This enables discovery of invariants that are only valid on the reachable domain, not
    /// on all syntactic states.
    ///
    /// Part of #1545 - entry-domain conditioned invariants.
    ///
    /// # Arguments
    /// * `blocking_formula` - The blocking formula to check
    /// * `predicate` - The predicate ID
    /// * `entry_domain` - Optional entry domain constraint (in canonical variable names)
    ///
    /// Returns true if `NOT(blocking_formula)` is preserved by all self-loop transitions
    /// when starting from states satisfying `entry_domain`.
    pub(in crate::pdr::solver) fn is_self_inductive_blocking_with_entry_domain(
        &mut self,
        blocking_formula: &ChcExpr,
        predicate: PredicateId,
        entry_domain: Option<&ChcExpr>,
    ) -> bool {
        conditioned_self::is_self_inductive_blocking_with_entry_domain(
            self,
            blocking_formula,
            predicate,
            entry_domain,
        )
    }

    /// Check if an invariant is inductive across inter-predicate entry transitions.
    ///
    /// Query at entry depth `level`: `clause_constraint ∧ pre_states(level-1) ∧ ¬I(head)` is UNSAT.
    /// If SAT, Entry-CEGAR may try to discharge predecessor reachability before rejecting.
    pub(in crate::pdr::solver) fn is_entry_inductive(
        &mut self,
        invariant: &ChcExpr,
        predicate: PredicateId,
        level: usize,
    ) -> bool {
        entry_check::is_entry_inductive(self, invariant, predicate, level)
    }

    /// Attempt to prove a predecessor state unreachable using local blocking.
    ///
    /// Entry-CEGAR (#1605): When `is_entry_inductive` finds a SAT model suggesting the
    /// invariant fails, we extract the predecessor cube and try to prove it unreachable.
    /// If unreachable, we learn blocking lemmas and the outer loop retries the entry check.
    ///
    /// Phase 2 (#1624): Added timeout to bound worst-case discharge overhead.
    ///
    /// Returns:
    /// - `Unreachable`: state proven unreachable, blocking lemmas learned
    /// - `Reachable`: state reaches level 0 (true counterexample)
    /// - `Unknown`: couldn't determine or timeout (conservative: reject invariant)
    pub(in crate::pdr::solver) fn entry_cegar_discharge_state(
        &mut self,
        predicate: PredicateId,
        state: ChcExpr,
        level: usize,
        timeout_ms: u64,
    ) -> EntryCegarDischarge {
        cegar::entry_cegar_discharge_state(self, predicate, state, level, timeout_ms)
    }
}
