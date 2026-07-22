// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! MaxSMT result types for the AY Solver API.
//!
//! MaxSMT extends SMT solving with soft constraints: hard constraints must be
//! satisfied, while the solver maximizes the total weight of satisfied soft
//! constraints. This is the SMT-level analogue of Weighted Partial MAX-SAT.
//!
//! ## Use Cases
//!
//! - **Maximum exploitability**: Hard constraints encode program semantics; soft
//!   constraints encode individual vulnerability conditions. The solver finds the
//!   input that triggers the most vulnerabilities simultaneously.
//! - **Minimum patch synthesis**: Hard constraints require a vulnerability to be
//!   unreachable; soft constraints prefer each program statement to stay unchanged.
//!   The solver finds the smallest patch.
//!
//! ## Current exact contract
//!
//! AY reduces each soft term to a Boolean relaxation indicator and minimizes
//! the total activated weight with an exact weighted-at-most-bound search. The
//! native API shares the executor implementation used by SMT-LIB
//! `(assert-soft ...)`; it does not maintain a second optimizer. Results outside
//! the bounded exact encoding, inconclusive probes, arithmetic overflow, and
//! grouped (`:id`) objectives are reported as `Unknown`, never as an optimum.
//! Grouped objectives require a richer result type than the single flat
//! satisfied/violated-weight partition represented here.

use super::handles::Term;

/// Status of a MaxSMT solve.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum MaxSmtStatus {
    /// Found an optimal solution: the maximum total weight of satisfiable soft
    /// constraints has been achieved.
    Optimal,
    /// The hard constraints are unsatisfiable regardless of soft constraints.
    HardUnsatisfiable,
    /// The solver could not determine the result (timeout, resource limit, etc.).
    Unknown,
}

impl std::fmt::Display for MaxSmtStatus {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Optimal => write!(f, "optimal"),
            Self::HardUnsatisfiable => write!(f, "hard-unsatisfiable"),
            Self::Unknown => write!(f, "unknown"),
        }
    }
}

/// Result of a MaxSMT solve.
///
/// Contains the status, the total weight of satisfied soft constraints,
/// and the indices of soft constraints that were violated in the optimal
/// solution.
#[derive(Debug, Clone)]
#[non_exhaustive]
#[must_use = "MaxSMT results should be inspected"]
pub struct MaxSmtResult {
    /// The solve status.
    pub status: MaxSmtStatus,
    /// Total weight of satisfied soft constraints in the optimal solution.
    /// Zero when status is not `Optimal`.
    pub satisfied_weight: u64,
    /// Total weight of violated soft constraints in the optimal solution.
    /// Zero when status is not `Optimal`.
    pub violated_weight: u64,
    /// Indices of soft constraints that were violated (unsatisfied) in the
    /// optimal solution. Empty when all softs are satisfied or when status
    /// is not `Optimal`.
    pub violated_softs: Vec<usize>,
}

impl MaxSmtResult {
    /// Create an optimal result.
    pub(crate) fn optimal(
        satisfied_weight: u64,
        violated_weight: u64,
        violated_softs: Vec<usize>,
    ) -> Self {
        Self {
            status: MaxSmtStatus::Optimal,
            satisfied_weight,
            violated_weight,
            violated_softs,
        }
    }

    /// Create a hard-unsatisfiable result.
    pub(crate) fn hard_unsatisfiable() -> Self {
        Self {
            status: MaxSmtStatus::HardUnsatisfiable,
            satisfied_weight: 0,
            violated_weight: 0,
            violated_softs: vec![],
        }
    }

    /// Create an unknown result.
    pub(crate) fn unknown() -> Self {
        Self {
            status: MaxSmtStatus::Unknown,
            satisfied_weight: 0,
            violated_weight: 0,
            violated_softs: vec![],
        }
    }

    /// Whether the result is optimal.
    #[must_use]
    pub fn is_optimal(&self) -> bool {
        self.status == MaxSmtStatus::Optimal
    }

    /// Whether the hard constraints are unsatisfiable.
    #[must_use]
    pub fn is_hard_unsatisfiable(&self) -> bool {
        self.status == MaxSmtStatus::HardUnsatisfiable
    }

    /// Whether the result is unknown.
    #[must_use]
    pub fn is_unknown(&self) -> bool {
        self.status == MaxSmtStatus::Unknown
    }

    /// Total weight of violated (unsatisfied) soft constraints.
    #[must_use]
    pub fn violated_weight(&self) -> u64 {
        self.violated_weight
    }
}

impl std::fmt::Display for MaxSmtResult {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "MaxSmtResult({}, satisfied_weight={}, violated_weight={}, violated={})",
            self.status,
            self.satisfied_weight,
            self.violated_weight,
            self.violated_softs.len()
        )
    }
}

/// A soft constraint registered with the solver.
///
/// Stored internally; not directly exposed to users. Users interact
/// via `Solver::assert_soft()` and `Solver::check_sat_max()`.
#[derive(Debug, Clone)]
pub(crate) struct SoftConstraint {
    /// The Boolean term that should ideally be satisfied.
    pub(crate) term: Term,
    /// Weight of this soft constraint (higher = more important to satisfy).
    pub(crate) weight: u64,
    /// Optional group label for categorizing soft constraints.
    #[allow(dead_code)]
    pub(crate) group: Option<String>,
}
