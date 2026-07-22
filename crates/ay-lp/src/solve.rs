// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Top-level MIP/LP solve driver.
//!
//! Resolves the LP relaxation with [`crate::simplex::solve_lp_relaxation`]; if
//! any integer variable is fractional, recursively branches on it. Depth-first
//! with incumbent pruning — adequate for Phase 1 MIP fixtures.

use crate::error::LpError;
use crate::model::{Problem, Sense, Solution};
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
/// [`LpError::Unbounded`] if the objective is unbounded along a feasible ray.
pub fn solve(problem: &Problem) -> Result<Solution, LpError> {
    if !problem.has_integer_vars() {
        return solve_lp_relaxation(problem);
    }
    let mut state = BnbState {
        incumbent: None,
        nodes_explored: 0,
    };
    branch_and_bound(problem, &mut state)?;
    state.incumbent.ok_or(LpError::Infeasible)
}

struct BnbState {
    incumbent: Option<Solution>,
    nodes_explored: usize,
}

fn branch_and_bound(problem: &Problem, state: &mut BnbState) -> Result<(), LpError> {
    state.nodes_explored += 1;
    if state.nodes_explored > MAX_NODES {
        return Err(LpError::IterationLimit);
    }

    let relaxation = match solve_lp_relaxation(problem) {
        Ok(s) => s,
        Err(LpError::Infeasible) => return Ok(()),
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
        // Feasible integer solution.
        if is_better_incumbent(problem.sense, &state.incumbent, relaxation.objective) {
            state.incumbent = Some(relaxation);
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
            let score = (val.fract()).min(1.0 - val.fract());
            if best.is_none() || score > best.unwrap().2 {
                best = Some((i, val, score));
            }
        }
    }
    best.map(|(i, v, _)| (i, v))
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
mod tests {
    use super::*;
    use crate::model::{Constraint, RowKind, Sense, VarKind, Variable};

    #[test]
    fn test_solve_continuous() {
        // min x + y s.t. x + y >= 4, x,y >= 0. Optimal at x+y=4 with obj=4.
        let mut p = Problem::new();
        p.sense = Sense::Min;
        p.variables.push(Variable {
            name: "x".into(),
            obj_coeff: 1.0,
            lower: 0.0,
            upper: f64::INFINITY,
            kind: VarKind::Continuous,
        });
        p.variables.push(Variable {
            name: "y".into(),
            obj_coeff: 1.0,
            lower: 0.0,
            upper: f64::INFINITY,
            kind: VarKind::Continuous,
        });
        p.constraints.push(Constraint {
            name: "c".into(),
            kind: RowKind::Ge,
            coeffs: vec![(0, 1.0), (1, 1.0)],
            rhs: 4.0,
        });
        let sol = solve(&p).expect("solve");
        assert!((sol.objective - 4.0).abs() < 1e-4);
    }

    #[test]
    fn test_solve_integer_knapsack() {
        // max 3x + 4y s.t. 2x + 3y <= 6, x,y in {0,1,2}, integer.
        // Exhaustive: (0,0)=0, (0,1)=4, (0,2)=8, (1,0)=3, (1,1)=7, (2,0)=6, (1,2)=11 (infeas 2+6=8), (2,1)=10.
        // Feasible: x=0,y=2 -> obj=8; x=2,y=0 -> 6; x=1,y=1 -> 7; x=2,y=1 -> 10 via 4+3=7<=6? 4+3=7>6 INFEAS.
        // Let's recompute: 2*2 + 3*1 = 7 > 6, infeasible. 2*0 + 3*2 = 6 feasible, obj=8. So max=8.
        let mut p = Problem::new();
        p.sense = Sense::Max;
        p.variables.push(Variable {
            name: "x".into(),
            obj_coeff: 3.0,
            lower: 0.0,
            upper: 2.0,
            kind: VarKind::Integer,
        });
        p.variables.push(Variable {
            name: "y".into(),
            obj_coeff: 4.0,
            lower: 0.0,
            upper: 2.0,
            kind: VarKind::Integer,
        });
        p.constraints.push(Constraint {
            name: "c".into(),
            kind: RowKind::Le,
            coeffs: vec![(0, 2.0), (1, 3.0)],
            rhs: 6.0,
        });
        let sol = solve(&p).expect("solve");
        assert!((sol.objective - 8.0).abs() < 1e-4, "got {}", sol.objective);
        assert!((sol.values[1] - 2.0).abs() < 1e-4);
    }

    #[test]
    fn test_solve_upper_only_integer_bound() {
        let mut p = Problem::new();
        p.sense = Sense::Max;
        p.variables.push(Variable {
            name: "x".into(),
            obj_coeff: 1.0,
            lower: f64::NEG_INFINITY,
            upper: 3.2,
            kind: VarKind::Integer,
        });
        let sol = solve(&p).expect("solve");
        assert!((sol.objective - 3.0).abs() < 1e-4, "got {}", sol.objective);
        assert!((sol.values[0] - 3.0).abs() < 1e-4, "x = {}", sol.values[0]);
    }
}
