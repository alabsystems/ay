// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Propagator trait: the interface all CP constraints implement.
//!
//! A propagator is a constraint-specific inference engine. Given the current
//! variable domains, it prunes values that cannot participate in any solution.
//! Critically, every pruning must produce an **explanation** — a set of
//! SAT literals that justify the pruning. This enables CDCL conflict analysis.
//!
//! # Example: AllDifferent Bounds Propagator
//!
//! Given `alldiff(x, y, z)` with `x ∈ [1,3], y ∈ [1,3], z ∈ [1,3]`:
//! - No bounds propagation possible (all can take distinct values).
//!
//! Given `alldiff(x, y, z)` with `x ∈ [1,2], y ∈ [1,2], z ∈ [1,3]`:
//! - x and y must use {1, 2}, so z cannot be 1 or 2.
//! - Propagate: `z ∈ [3,3]`.
//! - Explanation: `[x <= 2] ∧ [y <= 2] ∧ [x >= 1] ∧ [y >= 1] → [z >= 3]`.

use ay_sat::Literal;

use crate::encoder::IntegerEncoder;
use crate::trail::IntegerTrail;
use crate::variable::IntVarId;

/// An explanation is a set of SAT literals (a clause) that justifies
/// a propagation. The clause has the form:
///   `¬reason1 ∨ ¬reason2 ∨ ... ∨ conclusion`
///
/// Equivalently: `(reason1 ∧ reason2 ∧ ...) → conclusion`.
#[derive(Debug, Clone)]
pub struct Explanation {
    /// The reason literals (all must be true for the conclusion to hold).
    pub reasons: Vec<Literal>,
}

impl Explanation {
    /// Create a new explanation from reason literals.
    pub fn new(reasons: Vec<Literal>) -> Self {
        Self { reasons }
    }

    /// Convert to a SAT clause: `¬reason1 ∨ ¬reason2 ∨ ... ∨ conclusion`.
    /// Consumes self, reusing the reasons Vec allocation.
    pub fn into_clause(self, conclusion: Literal) -> Vec<Literal> {
        let mut clause = self.reasons;
        for lit in clause.iter_mut() {
            *lit = lit.negated();
        }
        clause.push(conclusion);
        clause
    }

    /// Convert to a conflict clause (all reasons must be true, but together
    /// they're contradictory): `¬reason1 ∨ ¬reason2 ∨ ...`.
    /// Consumes self, reusing the reasons Vec allocation.
    pub fn into_conflict_clause(self) -> Vec<Literal> {
        let mut clause = self.reasons;
        for lit in clause.iter_mut() {
            *lit = lit.negated();
        }
        clause
    }
}

/// Result of propagation.
#[derive(Debug)]
pub enum PropagationResult {
    /// No propagation was possible.
    NoChange,
    /// Domain(s) were narrowed. The returned clauses should be added to SAT.
    Propagated(Vec<Vec<Literal>>),
    /// A domain wipeout (conflict) was detected. The returned clause is the
    /// conflict explanation.
    Conflict(Vec<Literal>),
}

/// Priority for propagator scheduling.
///
/// Lower-priority propagators run first (they're cheaper).
/// Higher-priority propagators run only at fixpoint.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum PropagatorPriority {
    /// Unary constraints, clausal constraints (very cheap)
    Unary = 0,
    /// Binary constraints (cheap)
    Binary = 1,
    /// Linear constraints, element, table (moderate)
    Linear = 2,
    /// Global constraints: alldifferent_ac, cumulative, disjunctive (expensive)
    Global = 3,
}

/// Trait that all constraint propagators must implement.
///
/// Propagators are the heart of the CP solver. They:
/// 1. Watch for domain changes on their variables
/// 2. Infer tighter bounds based on the constraint semantics
/// 3. Explain every inference via a clause (for CDCL learning)
pub trait Propagator: std::fmt::Debug {
    /// The variables this propagator watches.
    fn variables(&self) -> &[IntVarId];

    /// Scheduling priority. Lower = runs first.
    fn priority(&self) -> PropagatorPriority;

    /// Propagate: tighten variable bounds based on current domains.
    ///
    /// Called when at least one watched variable has changed.
    /// Returns clauses to add to the SAT solver, or a conflict clause.
    ///
    /// The propagator uses `trail` to read current bounds and `encoder`
    /// to look up pre-allocated SAT literals for bound changes. The encoder
    /// is immutable — all literals must be pre-created before solving.
    fn propagate(&mut self, trail: &IntegerTrail, encoder: &IntegerEncoder) -> PropagationResult;

    /// Human-readable name for debugging.
    fn name(&self) -> &'static str;
}

/// A constraint in the CP model, before compilation into propagators.
///
/// The engine compiles constraints into one or more propagators
/// and registers them with the propagation queue.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum Constraint {
    /// `x1 != x2 != ... != xn` (all values distinct)
    AllDifferent(Vec<IntVarId>),

    /// `a1*x1 + a2*x2 + ... + an*xn <= rhs`
    LinearLe {
        coeffs: Vec<i64>,
        vars: Vec<IntVarId>,
        rhs: i64,
    },

    /// `a1*x1 + a2*x2 + ... + an*xn = rhs`
    LinearEq {
        coeffs: Vec<i64>,
        vars: Vec<IntVarId>,
        rhs: i64,
    },

    /// `a1*x1 + a2*x2 + ... + an*xn >= rhs`
    LinearGe {
        coeffs: Vec<i64>,
        vars: Vec<IntVarId>,
        rhs: i64,
    },

    /// `result = array[index]` (element constraint)
    Element {
        index: IntVarId,
        array: Vec<IntVarId>,
        result: IntVarId,
    },

    /// Table constraint: `(x1, x2, ..., xn) ∈ tuples`
    Table {
        vars: Vec<IntVarId>,
        tuples: Vec<Vec<i64>>,
    },

    /// Cumulative scheduling constraint.
    ///
    /// Durations and demands are `IntVarId` (integer variables). For constant
    /// durations/demands, create singleton-domain variables. This supports both
    /// the common all-constant case and variable-duration cumulative (e.g.,
    /// yumi-dynamic in the MiniZinc Challenge).
    Cumulative {
        starts: Vec<IntVarId>,
        durations: Vec<IntVarId>,
        demands: Vec<IntVarId>,
        capacity: i64,
    },

    /// Circuit constraint (Hamiltonian cycle)
    Circuit(Vec<IntVarId>),

    /// Inverse constraint: `x[y[i]] = i` for all i
    Inverse { x: Vec<IntVarId>, y: Vec<IntVarId> },

    /// Boolean clause: disjunction of literals
    BoolClause {
        pos: Vec<IntVarId>,
        neg: Vec<IntVarId>,
    },

    /// x = abs(y)
    Abs { result: IntVarId, arg: IntVarId },

    /// x = max(y1, y2, ..., yn)
    Maximum {
        result: IntVarId,
        args: Vec<IntVarId>,
    },

    /// x = min(y1, y2, ..., yn)
    Minimum {
        result: IntVarId,
        args: Vec<IntVarId>,
    },

    /// `x - y != offset` (pairwise value exclusion, no auxiliary variables)
    PairwiseNeq {
        x: IntVarId,
        y: IntVarId,
        offset: i64,
    },

    /// Non-overlapping rectangles (diffn constraint).
    ///
    /// `n` rectangles with origins `(x[i], y[i])` and dimensions `(dx[i], dy[i])`.
    /// No two rectangles may overlap (they may share edges but not interiors).
    Diffn {
        x: Vec<IntVarId>,
        y: Vec<IntVarId>,
        dx: Vec<IntVarId>,
        dy: Vec<IntVarId>,
    },

    /// `a1*x1 + a2*x2 + ... + an*xn != rhs`
    ///
    /// Native propagator replacing Big-M linearization. Only propagates when
    /// n-1 variables are fixed (removes the single forbidden value from the
    /// remaining variable) or when all n are fixed (detects conflict).
    LinearNotEqual {
        coeffs: Vec<i64>,
        vars: Vec<IntVarId>,
        rhs: i64,
    },

    /// Disjunctive (unary resource) scheduling constraint.
    ///
    /// `n` tasks on a single machine: task `i` occupies `[starts[i], starts[i] + durations[i])`.
    /// No two tasks may overlap. Uses O(n log n) edge-finding (Vilím 2008).
    Disjunctive {
        starts: Vec<IntVarId>,
        durations: Vec<i64>,
    },
}
