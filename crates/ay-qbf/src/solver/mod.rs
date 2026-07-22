// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! QBF solver internals.
//!
//! Quantified Conflict-Driven Clause Learning algorithm for QBF.
//!
//! ## Algorithm Overview
//!
//! QCDCL extends CDCL for quantified formulas:
//!
//! 1. **Quantifier-aware propagation**: A clause can only propagate an existential
//!    literal. Universal literals cannot be forced because the adversary controls them.
//!
//! 2. **Universal reduction**: Universal literals at the "tail" of a clause
//!    (with level >= max existential level) can be removed.
//!
//! 3. **Two-sided learning**: Learn clauses on existential conflicts,
//!    learn cubes on universal "wins".
//!
//! ## Current implementation status
//!
//! Public verdicts come from a budgeted, exact QDPLL evaluator. It follows the
//! prenex prefix directly (existential nodes are disjunctions; universal nodes
//! are conjunctions), prunes decided CNF matrices, and returns `Unknown` when
//! its node budget is exhausted.
//!
//! The QCDCL implementation in the sibling modules includes watched literals,
//! universal reduction, clause/cube learning, and VSIDS-like activity, but is
//! deliberately non-authoritative until proof-producing strategy validation is
//! available. Dependency learning, long-distance resolution, and authoritative
//! strategy-certificate extraction remain future work.
//!
//! ## References
//! - Zhang & Malik, "Conflict Driven Learning in a Quantified Boolean Satisfiability Solver"
//! - Lonsing & Biere, "DepQBF: A Dependency-Aware QBF Solver"
//!
//! ## Relationship to `ay-sat`
//!
//! QCDCL maintains its own watched-literal lists, VSIDS activity table,
//! trail / reasons / backtrack stack, and clause-database reducer. This is
//! NOT duplication of `ay-sat` internals — it is required because QCDCL
//! differs from CDCL on every one of these axes:
//!
//! - **Watched literals**: QBF `check_clause_unit` returns `UniversallyBlocked`
//!   when only universal literals remain unassigned. CDCL has no such state.
//! - **VSIDS**: QBF `pick_branch_var` filters to the outermost unassigned
//!   quantifier block first, then scores by activity. CDCL picks purely by
//!   activity.
//! - **Trail / reasons**: QBF tracks `Reason::CubePropagated` (cube-driven
//!   propagation) alongside clause propagation. CDCL has no cubes.
//! - **Learned database**: QBF learns both clauses (existential conflicts)
//!   and cubes (universal "wins"). CDCL learns only clauses.
//!
//! For the full analysis of why an `Extension`-trait port is infeasible,
//! see the development design notes.
//!
//! Primitives that ARE shared with `ay-sat`:
//! - `Literal` / `Variable` types (used everywhere)
//! - DIMACS parsing (`ay_sat::dimacs_core`)
//! - The `SolverContext` trait adapter (`QbfSolverContext`) exposing QBF
//!   solver state to downstream theory extensions via a stable API.

use crate::formula::QbfFormula;
use ay_sat::{Literal, SolverContext, Variable};
use std::collections::HashSet;

mod core;
mod database;
mod propagate;
mod search;
mod state;
#[cfg(test)]
mod tests;

/// Result of QBF solving
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum QbfResult {
    /// Formula is satisfiable (true for all universal assignments)
    Sat(Certificate),
    /// Formula is unsatisfiable (false for some universal assignment)
    Unsat(Certificate),
    /// Unknown result (timeout, resource limit)
    Unknown,
}

/// Certificate for QBF result
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Certificate {
    /// Experimental Skolem functions from the non-authoritative QCDCL path.
    Skolem(Vec<SkolemFunction>),
    /// Experimental Herbrand functions from the non-authoritative QCDCL path.
    Herbrand(Vec<HerbrandFunction>),
    /// No strategy certificate. This is used by authoritative exact-QDPLL verdicts.
    None,
}

/// A Skolem function for an existential variable
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SkolemFunction {
    /// The existential variable
    pub variable: u32,
    /// The function as a truth table (indexed by universal variable assignments)
    /// For now, just store a constant value
    pub value: bool,
}

/// A Herbrand function for a universal variable
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct HerbrandFunction {
    /// The universal variable
    pub variable: u32,
    /// The counterexample value
    pub value: bool,
}

/// Assignment state for a variable
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Assignment {
    /// Variable is unassigned
    Unassigned,
    /// Variable is assigned true
    True,
    /// Variable is assigned false
    False,
}

impl Assignment {
    fn to_bool(self) -> Option<bool> {
        match self {
            Self::True => Some(true),
            Self::False => Some(false),
            Self::Unassigned => None,
        }
    }

    fn is_assigned(self) -> bool {
        self != Self::Unassigned
    }
}

/// Reason for an assignment
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Reason {
    /// Decision (no reason)
    Decision,
    /// Propagated from clause (index into original or learned clauses)
    Propagated(usize),
    /// Propagated from a learned cube (index into `cubes`)
    CubePropagated(usize),
}

/// QCDCL Solver
pub struct QbfSolver {
    /// The formula
    formula: QbfFormula,
    /// Whether every native matrix literal names a variable in `1..=num_vars`.
    /// Parsed QDIMACS always satisfies this; direct native construction may not.
    input_valid: bool,
    /// Variable assignments (0-indexed)
    assignments: Vec<Assignment>,
    /// Decision level for each variable (0-indexed)
    levels: Vec<u32>,
    /// Reason for each assignment (0-indexed)
    reasons: Vec<Reason>,
    /// Assignment trail (in order of assignment)
    trail: Vec<Literal>,
    /// Decision level boundaries in trail
    trail_lim: Vec<usize>,
    /// Current decision level
    decision_level: u32,
    /// Learned clauses (disjunctions - block existential search paths)
    learned: Vec<Vec<Literal>>,
    /// Learned cubes (conjunctions - block universal search paths)
    /// A cube represents a winning strategy for the existential player
    cubes: Vec<Vec<Literal>>,
    /// Variables in quantifier order for decisions
    decision_order: Vec<u32>,
    /// Variable activity for VSIDS-style decisions (0-indexed by var-1)
    activity: Vec<f64>,
    /// VSIDS increment amount
    var_inc: f64,
    /// VSIDS decay factor (smaller => faster decay)
    var_decay: f64,
    /// Number of conflicts
    conflicts: u64,
    /// Number of propagations
    propagations: u64,
    /// Number of decisions
    decisions: u64,
    /// Two-watched literal data: watches[lit_idx] = list of (clause_idx, other_watch)
    /// lit_idx = var * 2 + (1 if negative else 0)
    watches: Vec<Vec<WatchInfo>>,
    /// Position in trail for propagation queue
    qhead: usize,
    /// "Used" flag for each learned clause (set during conflict analysis)
    clause_used: Vec<bool>,
    /// "Used" flag for each learned cube
    cube_used: Vec<bool>,
    /// Next conflict count at which to reduce the clause database
    next_reduce: u64,
    /// Number of clause reductions performed
    reductions: u64,
    /// Number of learned clauses deleted by reduction
    clauses_deleted: u64,
    /// Number of learned cubes deleted by reduction
    cubes_deleted: u64,
}

/// Watch information for a clause
#[derive(Debug, Clone, Copy)]
struct WatchInfo {
    /// Clause index (high bit indicates learned clause)
    clause_idx: usize,
    /// The other watched literal (for quick filtering)
    blocker: Literal,
}

/// Bit flag to distinguish learned clauses in watch lists
const LEARNED_CLAUSE_BIT: usize = 1 << (usize::BITS - 1);

/// Conflict count before first clause database reduction
const REDUCE_DB_INIT: u64 = 2000;

/// Conflicts between reductions
const REDUCE_DB_INC: u64 = 300;

/// Minimum clause length to consider for deletion (short clauses are protected)
const REDUCE_PROTECT_LEN: usize = 3;

/// Result of propagation
enum PropResult {
    Ok,
    Conflict(usize),
}

/// Result of cube learning
enum CubeResult {
    /// Learned a cube, backtrack to this level
    Learned(u32),
    /// Formula is solved (SAT for all universal paths)
    Solved,
}

/// Status of a clause during propagation
enum ClauseStatus {
    Satisfied,
    Falsified,
    /// Only universal literals remain unassigned - UNSAT player wins
    UniversallyBlocked,
    Unit(Literal),
    Unresolved,
}

/// QBF solver statistics
#[derive(Debug, Clone, Default)]
pub struct QbfStats {
    /// Number of conflicts
    pub conflicts: u64,
    /// Number of propagations
    pub propagations: u64,
    /// Number of decisions
    pub decisions: u64,
    /// Number of active (non-deleted) learned clauses
    pub learned_clauses: u64,
    /// Number of active (non-deleted) learned cubes
    pub learned_cubes: u64,
    /// Number of clause database reductions performed
    pub reductions: u64,
    /// Total learned clauses deleted by reduction
    pub clauses_deleted: u64,
    /// Total learned cubes deleted by reduction
    pub cubes_deleted: u64,
}

/// Adapter exposing `QbfSolver` state through the `ay_sat::SolverContext` trait.
///
/// This lets downstream theory extensions (e.g., bit-vector quantifiers)
/// inspect QBF solver state using the same read-only API as SAT theory
/// extensions. The adapter is zero-cost: it borrows `QbfSolver` directly.
///
/// The QBF search loop itself is NOT driven by the `Extension` trait — see
/// the development design notes for why
/// (QCDCL's two-player game, universal reduction, cube learning, and
/// quantifier-ordered decisions have no CDCL analog). The adapter exists
/// so that future QBF-side theory plugins can reuse `ay-sat`'s trait
/// contract rather than inventing a new one.
pub struct QbfSolverContext<'a> {
    /// Borrowed reference to the QBF solver.
    solver: &'a QbfSolver,
}

impl<'a> QbfSolverContext<'a> {
    /// Create a new context view over a `QbfSolver`.
    pub(crate) fn new(solver: &'a QbfSolver) -> Self {
        Self { solver }
    }
}

impl SolverContext for QbfSolverContext<'_> {
    fn value(&self, var: Variable) -> Option<bool> {
        self.solver.value(var.id()).to_bool()
    }

    fn decision_level(&self) -> u32 {
        self.solver.decision_level
    }

    fn var_level(&self, var: Variable) -> Option<u32> {
        let id = var.id() as usize;
        if id == 0 || id > self.solver.levels.len() {
            return None;
        }
        // Level is only meaningful if the variable is assigned.
        if self.solver.assignments[id - 1].is_assigned() {
            Some(self.solver.levels[id - 1])
        } else {
            None
        }
    }

    fn trail(&self) -> &[Literal] {
        &self.solver.trail
    }

    fn activity(&self, var: Variable) -> f64 {
        let id = var.id() as usize;
        if id == 0 || id > self.solver.activity.len() {
            return 0.0;
        }
        self.solver.activity[id - 1]
    }

    fn conflicts(&self) -> u64 {
        self.solver.conflicts
    }

    fn decisions(&self) -> u64 {
        self.solver.decisions
    }

    fn propagations(&self) -> u64 {
        self.solver.propagations
    }
}

impl QbfSolver {
    /// Borrow a read-only `SolverContext`-compatible view of this solver.
    ///
    /// See `QbfSolverContext` for the rationale.
    pub fn as_context(&self) -> QbfSolverContext<'_> {
        QbfSolverContext::new(self)
    }
}

#[cfg(test)]
mod context_tests {
    use super::*;
    use crate::formula::{QbfFormula, QuantifierBlock};
    use ay_sat::{SolverContext, Variable};

    fn trivial_sat_solver() -> QbfSolver {
        // ∃x. (x)  — trivially SAT
        let formula = QbfFormula::new(
            1,
            vec![QuantifierBlock::exists(vec![1])],
            vec![vec![Literal::positive(Variable::new(1))]],
        );
        QbfSolver::new(formula)
    }

    #[test]
    fn context_initial_values_unassigned() {
        let solver = trivial_sat_solver();
        let ctx = solver.as_context();
        assert_eq!(ctx.decision_level(), 0);
        assert!(ctx.trail().is_empty());
        assert_eq!(ctx.value(Variable::new(1)), None);
        assert_eq!(ctx.var_level(Variable::new(1)), None);
        assert_eq!(ctx.conflicts(), 0);
        assert_eq!(ctx.decisions(), 0);
        assert_eq!(ctx.propagations(), 0);
    }

    #[test]
    fn context_out_of_range_vars_are_unassigned() {
        let solver = trivial_sat_solver();
        let ctx = solver.as_context();
        // Variable 999 is past the end of the allocated state.
        assert_eq!(ctx.value(Variable::new(999)), None);
        assert_eq!(ctx.var_level(Variable::new(999)), None);
        // Variable::new(0) is the id=0 sentinel — out of range.
        assert_eq!(ctx.activity(Variable::new(0)), 0.0);
    }

    #[test]
    fn context_reflects_solve_result() {
        let mut solver = trivial_sat_solver();
        let _ = solver.solve();
        let ctx = solver.as_context();
        // Trivial SAT: one existential variable assigned.
        assert_eq!(ctx.value(Variable::new(1)), Some(true));
        assert_eq!(ctx.var_level(Variable::new(1)), Some(0));
    }
}
