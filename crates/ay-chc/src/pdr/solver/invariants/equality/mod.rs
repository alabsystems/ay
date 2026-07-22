// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Equality invariant discovery for PDR solver.
//!
//! This module contains methods for discovering and verifying equality invariants
//! of the form `var_i = var_j` (two variables are always equal) or `var_i = var_j + k`
//! (variables differ by a constant offset).
//!
//! ## Key Methods
//!
//! - [`PdrSolver::discover_equality_invariants`] - Main discovery entry point
//! - [`PdrSolver::is_equality_preserved_by_transitions_with_entry`] - Check if equality
//!   is preserved across all self-loop transitions
//!
//! ## Algorithm
//!
//! 1. For each predicate, enumerate all pairs of integer variables
//! 2. Check if equality is implied by fact clauses (initialization)
//! 3. Verify equality is preserved by all transition clauses
//! 4. If both hold, add `var_i = var_j` as a discovered invariant
//!
//! The preservation check uses SMT to verify: `pre_i = pre_j ∧ constraint ⇒ post_i = post_j`

use super::super::PdrSolver;
use super::MAX_PAIRWISE_DISCOVERY_VARS;

use ay_core::kani_compat::DetHashMap as FxHashMap;

use crate::pdr::types::VarOffset;
use crate::smt::SmtResult;
use crate::{ChcExpr, ChcOp, ChcSort, ChcVar, PredicateId};

mod discovery;
mod preservation;
mod transition;
mod transition_utils;

#[cfg(test)]
mod tests;

fn same_equality_candidate_sort(lhs: &ChcSort, rhs: &ChcSort) -> bool {
    match (lhs, rhs) {
        (ChcSort::Int, ChcSort::Int) => true,
        (ChcSort::BitVec(w1), ChcSort::BitVec(w2)) => w1 == w2,
        // D1 (LIA-Lin-Arrays): Array-sorted predicate-argument pairs are
        // equality candidates too. llreve-style relational CHCs need lockstep
        // array equalities `(= a1 a2)` between predicate args (e.g. memchr's
        // unblockable POB contains `(not (= __p1_a3 __p1_a7))`). Candidates
        // are still gated by the same init-validity / entry-inductiveness /
        // self-inductiveness SMT checks as Int equalities; those queries are
        // QF_ALIA and route through the executor backend (reject-on-Unknown).
        (ChcSort::Array(k1, v1), ChcSort::Array(k2, v2)) => k1 == k2 && v1 == v2,
        _ => false,
    }
}
