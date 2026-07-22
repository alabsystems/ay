// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Inductiveness checks and Entry-CEGAR refinements.
//!
//! Contains the core inductiveness verification logic for PDR:
//! - `is_inductive_blocking`: frame-relative inductiveness
//! - `is_self_inductive_blocking`: self-inductiveness checks
//! - `is_entry_inductive`: inter-predicate entry-CEGAR
//! - `add_discovered_invariant`: invariant insertion with validation
//! - `blocks_initial_states`: init-blocking verification

mod entry;
mod inductive_blocking;
mod insertion;
mod parity;
mod self_inductive;

#[allow(clippy::unwrap_used, clippy::panic)]
#[cfg(test)]
mod tests;

use super::PdrSolver;
use crate::{ChcExpr, PredicateId};

impl PdrSolver {
    fn check_hyperedge_inductive_query(
        &mut self,
        predicate: PredicateId,
        clause_index: usize,
        hyperedge_query: &super::hyperedge::HyperedgeInductiveQuery,
    ) -> crate::smt::SmtResult {
        inductive_blocking::check_hyperedge_inductive_query(
            self,
            predicate,
            clause_index,
            hyperedge_query,
        )
    }

    /// Check if a blocking formula is inductive relative to a frame
    ///
    /// Returns true if: frame[level-1] /\ T => blocking_formula
    /// (i.e., the blocking formula blocks states reachable from frame[level-1])
    ///
    /// IMPORTANT: Also checks that the lemma (NOT(blocking_formula)) doesn't exclude
    /// all initial states - this prevents learning lemmas incompatible with init.
    pub(in crate::pdr) fn is_inductive_blocking(
        &mut self,
        blocking_formula: &ChcExpr,
        predicate: PredicateId,
        level: usize,
    ) -> bool {
        // Cooperative deadline backstop. Candidate-inductiveness checks fire one
        // SMT query each inside O(vars^2) generalization-enumeration loops that
        // do NOT themselves consult the solve deadline; on a non-synthesizable
        // invariant (e.g. n%3 in {0,1,2}) those loops enumerate fruitlessly and
        // the wall-clock `solve_timeout` is otherwise only observed many minutes
        // later at the next outer-loop boundary. Returning `false` (= "not
        // inductive") once cancelled is sound at EVERY call site — every caller
        // treats it as "reject this candidate" (skip / try another / fall back),
        // never as a Safe/Unsafe conclusion — so the enumeration drains with
        // only cheap deadline checks (no further SMT) and the solve degrades to
        // Unknown (fail-closed) instead of hanging.
        if self.is_cancelled() {
            return false;
        }
        inductive_blocking::is_inductive_blocking(self, blocking_formula, predicate, level)
    }

    /// Uncached implementation of is_inductive_blocking.
    pub(in crate::pdr::solver) fn is_inductive_blocking_uncached(
        &mut self,
        blocking_formula: &ChcExpr,
        predicate: PredicateId,
        level: usize,
    ) -> bool {
        inductive_blocking::is_inductive_blocking_uncached(self, blocking_formula, predicate, level)
    }

    // is_self_inductive_blocking and is_self_inductive_blocking_uncached
    // are in self_inductive.rs
}
