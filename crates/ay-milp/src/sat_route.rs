// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared exact boundary for MILP-to-CNF feasibility routes.
//!
//! A route owns the proof that its CNF is equivalent to the caller's model and
//! supplies an exact lift from a Boolean assignment.  This module owns only the
//! common CDCL execution boundary: one pinned deadline, complete clause import,
//! and a final [`Model::check_point`] against the original model before a SAT
//! witness may escape.

use std::time::Instant;

use ay_sat::{Literal, SatResult, Solver};
use num_rational::BigRational;

use crate::Model;

/// A source-model point that crossed this module's exact [`Model::check_point`]
/// boundary before the pinned deadline.
///
/// The field is private so a route cannot manufacture the token and then use a
/// session's prechecked finalizer to skip primal validation. Consumers may
/// move the checked values out, but only this module's checked lift boundary
/// can create them.
pub(crate) struct CheckedSatPoint(Vec<BigRational>);

impl CheckedSatPoint {
    pub(crate) fn into_values(self) -> Vec<BigRational> {
        self.0
    }
}

/// A conclusive result from an exact CNF reduction.
pub(crate) enum SatDecision {
    /// A feasible point in the original model's column order.
    Sat(CheckedSatPoint),
    /// The equivalent CNF is unsatisfiable.
    Unsat,
}

/// Lift one solver assignment and check the exact source-model point.
///
/// Proof-producing routes use this after a single SAT-or-refutation solve, so
/// they cross exactly the same private point boundary as ordinary CDCL.
pub(crate) fn lift_and_check_assignment<F>(
    model: &Model,
    assignment: &[bool],
    deadline: Option<Instant>,
    lift: F,
) -> Option<CheckedSatPoint>
where
    F: FnOnce(&[bool]) -> Option<Vec<BigRational>>,
{
    if deadline_reached(deadline) {
        return None;
    }
    let point = lift(assignment)?;
    if deadline_reached(deadline) || model.check_point(&point).is_err() {
        return None;
    }
    // Exact witness validation can itself be material on a large model. Never
    // publish a verdict that completed after the caller's pinned deadline.
    if deadline_reached(deadline) {
        return None;
    }
    Some(CheckedSatPoint(point))
}

/// Solve `clauses`, lift a SAT assignment, and re-check it against `model`.
///
/// `None` is deliberately overloaded only at this outer orchestration seam: it
/// means deadline/interrupt, solver `Unknown`, or a rejected lift.  Admission
/// itself remains typed in each route so an unsupported model cannot be
/// confused with a conclusive answer.
pub(crate) fn solve_and_lift<F>(
    model: &Model,
    num_vars: usize,
    clauses: &[Vec<Literal>],
    deadline: Option<Instant>,
    lift: F,
) -> Option<SatDecision>
where
    F: FnOnce(&[bool]) -> Option<Vec<BigRational>>,
{
    if deadline_reached(deadline) {
        return None;
    }

    let mut solver = Solver::new(num_vars);
    solver.set_solve_deadline(deadline);
    for (index, clause) in clauses.iter().enumerate() {
        if index & 0x3ff == 0 && deadline_reached(deadline) {
            return None;
        }
        let _ = solver.add_clause(clause.clone());
    }
    if deadline_reached(deadline) {
        return None;
    }

    let result = solver
        .solve_interruptible(|| deadline_reached(deadline))
        .into_inner();
    if deadline_reached(deadline) {
        return None;
    }

    match result {
        SatResult::Sat(assignment) => {
            lift_and_check_assignment(model, &assignment, deadline, lift).map(SatDecision::Sat)
        }
        SatResult::Unsat(_) => Some(SatDecision::Unsat),
        SatResult::Unknown => None,
        _ => None,
    }
}

pub(crate) fn deadline_reached(deadline: Option<Instant>) -> bool {
    deadline.is_some_and(|limit| Instant::now() >= limit)
}
