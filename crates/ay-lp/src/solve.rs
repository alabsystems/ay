// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Top-level MIP/LP solve driver.
//!
//! Resolves the LP relaxation with [`crate::simplex::solve_lp_relaxation`]; if
//! any integer variable is fractional, recursively branches on it. Depth-first
//! with incumbent pruning — adequate for Phase 1 MIP fixtures.

use crate::error::LpError;
use crate::model::{Problem, RowKind, Sense, Solution, VarKind, Variable};
use crate::simplex::solve_lp_relaxation;

const INT_TOL: f64 = 1e-6;
const MAX_NODES: usize = 4096;

/// Solves `problem`, returning an optimal [`Solution`].
///
/// Integer variables are handled via depth-first branch-and-bound over the
/// LP relaxation. Continuous problems go straight through the simplex.
///
/// # Errors
///
/// Returns [`LpError::Infeasible`] if the problem has no feasible solution,
/// [`LpError::Unbounded`] if a continuous problem is unbounded along a
/// feasible ray. For integer problems, an unbounded LP relaxation is not by
/// itself an integer-feasible ray certificate, so the solver fails closed with
/// [`LpError::Unsupported`] instead of claiming MIP unboundedness.
pub fn solve(problem: &Problem) -> Result<Solution, LpError> {
    solve_with_incumbents(problem, &mut |_| {})
}

/// [`solve`], reporting every improving integer-feasible incumbent to
/// `on_incumbent` as soon as branch-and-bound finds it.
///
/// Each reported point has passed the same bound and row feasibility check
/// that admits it as an incumbent. When the search later stops with an error
/// (node or iteration limit, [`LpError::ResourceLimit`]), the last reported
/// point is still a feasible solution; it is only not proven optimal.
///
/// # Errors
///
/// As [`solve`].
pub fn solve_with_incumbents(
    problem: &Problem,
    on_incumbent: &mut dyn FnMut(&Solution),
) -> Result<Solution, LpError> {
    if !problem.has_integer_vars() {
        return solve_lp_relaxation(problem);
    }
    let mut state = BnbState {
        incumbent: None,
        nodes_explored: 0,
        on_incumbent,
    };
    branch_and_bound(problem, &mut state)?;
    state.incumbent.ok_or(LpError::Infeasible)
}

/// Absolute tolerance of [`check_point`], scaled by the row's magnitude.
const POINT_TOL: f64 = 1e-9;

/// Checks that `values` (one per variable, in `problem` order) is a feasible
/// point of `problem` and returns its objective value.
///
/// Stricter than the branch-and-bound acceptance test, and independent of
/// whichever solver produced the point: every value must be finite; integer
/// and binary variables must hold exact integers inside their bounds; other
/// bounds and every row must hold within `1e-9` times the magnitude of the
/// row (at least 1). The MIPLIB checker the competitions use accepts at
/// `1e-6`. A point that passes here therefore passes there when `problem`
/// is the checker's model of the file: for MPS input that is
/// [`crate::parse_mps`]'s reading, which applies the checker's defaults (an
/// integer column of a marker section with no BOUNDS entry is in `[0, 1]`)
/// and refuses the constructs on which MPS readers disagree. For a
/// `Problem` built some other way the check is against that `Problem` only.
///
/// # Errors
///
/// A message naming the first variable or row that fails.
pub fn check_point(problem: &Problem, values: &[f64]) -> Result<f64, String> {
    if values.len() != problem.variables.len() {
        return Err(format!(
            "{} values for {} variables",
            values.len(),
            problem.variables.len()
        ));
    }
    for (var, &value) in problem.variables.iter().zip(values) {
        if !value.is_finite() {
            return Err(format!("variable '{}' is not finite", var.name));
        }
        if var.is_integral() && value.fract() != 0.0 {
            return Err(format!("variable '{}' = {value} is not integral", var.name));
        }
        let (lower, upper) = effective_solution_bounds(var);
        let tol = POINT_TOL * value.abs().max(1.0);
        if (lower.is_finite() && value < lower - tol) || (upper.is_finite() && value > upper + tol)
        {
            return Err(format!(
                "variable '{}' = {value} is outside [{lower}, {upper}]",
                var.name
            ));
        }
    }
    for row in &problem.constraints {
        let mut lhs = 0.0f64;
        let mut scale = row.rhs.abs().max(1.0);
        for &(idx, coef) in &row.coeffs {
            let term = coef * values.get(idx).copied().unwrap_or(f64::NAN);
            lhs += term;
            scale = scale.max(term.abs());
        }
        if !lhs.is_finite() {
            return Err(format!("row '{}' activity is not finite", row.name));
        }
        let tol = POINT_TOL * scale;
        let ok = match row.kind {
            RowKind::Le => lhs <= row.rhs + tol,
            RowKind::Ge => lhs >= row.rhs - tol,
            RowKind::Eq => (lhs - row.rhs).abs() <= tol,
        };
        if !ok {
            return Err(format!(
                "row '{}' activity {lhs} violates {:?} {}",
                row.name, row.kind, row.rhs
            ));
        }
    }
    objective_from_values(problem, values).ok_or_else(|| "objective is not finite".to_string())
}

struct BnbState<'a> {
    incumbent: Option<Solution>,
    nodes_explored: usize,
    on_incumbent: &'a mut dyn FnMut(&Solution),
}

fn branch_and_bound(problem: &Problem, state: &mut BnbState<'_>) -> Result<(), LpError> {
    state.nodes_explored += 1;
    if state.nodes_explored > MAX_NODES {
        return Err(LpError::IterationLimit);
    }

    let relaxation = match solve_lp_relaxation(problem) {
        Ok(s) => s,
        Err(LpError::Infeasible) => return Ok(()),
        Err(LpError::Unbounded) => {
            return Err(LpError::Unsupported(
                "integer search cannot certify unboundedness from an LP relaxation alone".into(),
            ));
        }
        Err(e) => return Err(e),
    };

    // Prune by incumbent bound.
    if let Some(inc) = &state.incumbent {
        if prune_by_bound(problem.sense, relaxation.objective, inc.objective) {
            return Ok(());
        }
    }

    // Find a fractional integer variable (most-fractional rule).
    let frac_var = pick_fractional(problem, &relaxation.values);
    let Some((idx, value)) = frac_var else {
        // Feasible integer solution. Materialize the actual integer point
        // before recording it; a tolerance-integral relaxation value is not
        // itself a MIP incumbent.
        let Some(candidate) = integer_candidate_from_relaxation(problem, &relaxation) else {
            return Ok(());
        };
        if is_better_incumbent(problem.sense, &state.incumbent, candidate.objective) {
            (state.on_incumbent)(&candidate);
            state.incumbent = Some(candidate);
        }
        return Ok(());
    };

    let floor = value.floor();
    let ceil = value.ceil();

    // Down branch: x <= floor.
    let mut down = problem.clone();
    down.variables[idx].upper = floor.min(down.variables[idx].upper);
    if down.variables[idx].upper >= down.variables[idx].lower - INT_TOL {
        branch_and_bound(&down, state)?;
    }

    // Up branch: x >= ceil.
    let mut up = problem.clone();
    up.variables[idx].lower = ceil.max(up.variables[idx].lower);
    if up.variables[idx].lower <= up.variables[idx].upper + INT_TOL {
        branch_and_bound(&up, state)?;
    }

    Ok(())
}

fn pick_fractional(problem: &Problem, values: &[f64]) -> Option<(usize, f64)> {
    let mut best: Option<(usize, f64, f64)> = None;
    for (i, v) in problem.variables.iter().enumerate() {
        if !v.is_integral() {
            continue;
        }
        let val = values.get(i).copied().unwrap_or(0.0);
        let rounded = val.round();
        let diff = (val - rounded).abs();
        if diff > INT_TOL {
            let score = fractional_score(val);
            match best {
                Some((_, _, best_score)) if score <= best_score => {}
                _ => best = Some((i, val, score)),
            }
        }
    }
    best.map(|(i, v, _)| (i, v))
}

fn fractional_score(value: f64) -> f64 {
    let below = value.floor();
    let above = value.ceil();
    (value - below).min(above - value)
}

fn integer_candidate_from_relaxation(problem: &Problem, relaxation: &Solution) -> Option<Solution> {
    let values = rounded_integer_values(problem, &relaxation.values)?;
    if !solution_values_feasible(problem, &values) {
        return None;
    }
    let objective = objective_from_values(problem, &values)?;
    Some(Solution { objective, values })
}

fn rounded_integer_values(problem: &Problem, values: &[f64]) -> Option<Vec<f64>> {
    if values.len() != problem.variables.len() {
        return None;
    }
    let mut rounded_values = values.to_vec();
    for (i, var) in problem.variables.iter().enumerate() {
        let value = values[i];
        if !value.is_finite() {
            return None;
        }
        if !var.is_integral() {
            continue;
        }
        let rounded = value.round();
        if (value - rounded).abs() > INT_TOL {
            return None;
        }
        let (lower, upper) = checked_effective_integer_bounds(var)?;
        if lower.is_finite() && rounded < lower {
            return None;
        }
        if upper.is_finite() && rounded > upper {
            return None;
        }
        rounded_values[i] = rounded;
    }
    Some(rounded_values)
}

fn effective_integer_bounds(var: &Variable) -> (f64, f64) {
    match var.kind {
        VarKind::Binary => (var.lower.max(0.0), var.upper.min(1.0)),
        VarKind::Integer => (var.lower, var.upper),
        VarKind::Continuous => (f64::NEG_INFINITY, f64::INFINITY),
    }
}

fn checked_effective_integer_bounds(var: &Variable) -> Option<(f64, f64)> {
    valid_bounds(effective_integer_bounds(var))
}

fn objective_from_values(problem: &Problem, values: &[f64]) -> Option<f64> {
    if values.len() != problem.variables.len() || !problem.obj_constant.is_finite() {
        return None;
    }
    let mut objective = problem.obj_constant;
    for (var, &value) in problem.variables.iter().zip(values) {
        if !var.obj_coeff.is_finite() || !value.is_finite() {
            return None;
        }
        let term = var.obj_coeff * value;
        if !term.is_finite() {
            return None;
        }
        objective += term;
        if !objective.is_finite() {
            return None;
        }
    }
    Some(objective)
}

fn solution_values_feasible(problem: &Problem, values: &[f64]) -> bool {
    if values.len() != problem.variables.len() {
        return false;
    }
    for (var, &value) in problem.variables.iter().zip(values) {
        if !value.is_finite() {
            return false;
        }
        let Some((lower, upper)) = checked_effective_solution_bounds(var) else {
            return false;
        };
        if lower.is_finite() && value < lower - INT_TOL {
            return false;
        }
        if upper.is_finite() && value > upper + INT_TOL {
            return false;
        }
    }
    for constraint in &problem.constraints {
        if !constraint.rhs.is_finite() {
            return false;
        }
        let mut lhs = 0.0;
        for &(idx, coef) in &constraint.coeffs {
            if !coef.is_finite() {
                return false;
            }
            let Some(&value) = values.get(idx) else {
                return false;
            };
            let term = coef * value;
            if !term.is_finite() {
                return false;
            }
            lhs += term;
            if !lhs.is_finite() {
                return false;
            }
        }
        let tol = INT_TOL * (1.0 + lhs.abs().max(constraint.rhs.abs()));
        let ok = match constraint.kind {
            RowKind::Le => lhs <= constraint.rhs + tol,
            RowKind::Ge => lhs >= constraint.rhs - tol,
            RowKind::Eq => (lhs - constraint.rhs).abs() <= tol,
        };
        if !ok {
            return false;
        }
    }
    true
}

fn effective_solution_bounds(var: &Variable) -> (f64, f64) {
    match var.kind {
        VarKind::Binary => (var.lower.max(0.0), var.upper.min(1.0)),
        VarKind::Integer | VarKind::Continuous => (var.lower, var.upper),
    }
}

fn checked_effective_solution_bounds(var: &Variable) -> Option<(f64, f64)> {
    valid_bounds(effective_solution_bounds(var))
}

fn valid_bounds((lower, upper): (f64, f64)) -> Option<(f64, f64)> {
    if lower.is_nan() || upper.is_nan() {
        return None;
    }
    if lower.is_infinite() && lower.is_sign_positive() {
        return None;
    }
    if upper.is_infinite() && upper.is_sign_negative() {
        return None;
    }
    if lower.is_finite() && upper.is_finite() && upper < lower {
        return None;
    }
    Some((lower, upper))
}

fn prune_by_bound(sense: Sense, relaxation_obj: f64, incumbent_obj: f64) -> bool {
    match sense {
        Sense::Min => relaxation_obj >= incumbent_obj - INT_TOL,
        Sense::Max => relaxation_obj <= incumbent_obj + INT_TOL,
    }
}

fn is_better_incumbent(sense: Sense, incumbent: &Option<Solution>, candidate: f64) -> bool {
    match incumbent {
        None => true,
        Some(inc) => match sense {
            Sense::Min => candidate < inc.objective - INT_TOL,
            Sense::Max => candidate > inc.objective + INT_TOL,
        },
    }
}

#[cfg(test)]
mod tests;
