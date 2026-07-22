// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Core types for the IntSat CDCL-style ILP solver.
//!
//! Based on: Nieuwenhuis, Oliveras, Rodriguez-Carbonell.
//! "IntSat: Integer Linear Programming by Conflict-Driven Constraint-Learning."
//! arXiv:2402.15522, February 2024.

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::DetHashMap as HashMap;
use num_bigint::BigInt;

/// Variable identifier in the IntSat solver (contiguous index).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct VarId(pub u32);

/// A bound on a variable: either lower (x >= value) or upper (x <= value).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct BoundEntry {
    /// The variable this bound applies to.
    pub(crate) var: VarId,
    /// The bound value.
    pub(crate) value: BigInt,
    /// True if this is an upper bound (x <= value), false if lower (x >= value).
    pub(crate) is_upper: bool,
    /// Why this bound was derived.
    pub(crate) reason: BoundReason,
    /// Decision level at which this bound was placed on the trail.
    pub(crate) level: u32,
}

/// Reason for a bound on the trail.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum BoundReason {
    /// A decision bound (splitting the domain).
    Decision,
    /// Propagated from a constraint (index into the constraint database).
    Propagation { constraint_idx: usize },
    /// An input constraint bound (level 0, no backtracking).
    Input,
}

/// A linear constraint in normalized <= form: sum(coeffs\[i\] * x_i) <= rhs.
///
/// All constraints are stored in this canonical form. Equalities become two
/// constraints, lower bounds are negated.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Constraint {
    /// Variable-coefficient pairs. Sorted by VarId for determinism.
    pub coeffs: Vec<(VarId, BigInt)>,
    /// Right-hand side of the inequality.
    pub rhs: BigInt,
}

/// Result of the IntSat solver.
#[derive(Debug)]
pub enum IntSatResult {
    /// Satisfiable with a model mapping each variable to an integer value.
    Sat(HashMap<VarId, BigInt>),
    /// Unsatisfiable (conflict at decision level 0).
    Unsat,
    /// Resource limit exceeded (iteration cap).
    Unknown,
}

/// Outcome of propagation: either new bounds were derived, or a conflict occurred.
#[derive(Debug)]
pub(crate) enum PropagationResult {
    /// Propagation succeeded (possibly with new trail entries).
    Ok,
    /// A constraint was falsified: the constraint index and the conflicting constraint.
    Conflict { constraint_idx: usize },
}

/// Result of conflict analysis.
#[derive(Debug)]
pub(crate) struct AnalysisResult {
    /// The learned constraint (1UIP cut).
    pub(crate) learned: Constraint,
    /// The decision level to backjump to.
    pub(crate) backjump_level: u32,
}
