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

    #[test]
    fn test_integer_incumbent_materializes_rounded_values() {
        let mut p = Problem::new();
        p.sense = Sense::Max;
        p.variables.push(Variable {
            name: "x".into(),
            obj_coeff: 1.0,
            lower: 0.0,
            upper: 1.0000004,
            kind: VarKind::Integer,
        });

        let sol = solve(&p).expect("solve");

        assert_eq!(sol.values[0], 1.0);
        assert_eq!(sol.objective, 1.0);
    }

    #[test]
    fn test_integer_search_does_not_claim_unbounded_from_relaxation_only() {
        let mut p = Problem::new();
        p.sense = Sense::Max;
        p.variables.push(Variable {
            name: "x".into(),
            obj_coeff: 0.0,
            lower: 0.5,
            upper: 0.5,
            kind: VarKind::Integer,
        });
        p.variables.push(Variable {
            name: "y".into(),
            obj_coeff: 1.0,
            lower: 0.0,
            upper: f64::INFINITY,
            kind: VarKind::Continuous,
        });

        // The LP relaxation is unbounded via y at x = 0.5, but the integer
        // model has no feasible assignment for x. Without an integer-feasible
        // ray certificate, branch-and-bound must not report MIP unboundedness.
        assert!(matches!(
            solve(&p),
            Err(LpError::Unsupported(msg))
                if msg.contains("cannot certify unboundedness")
        ));
    }

    #[test]
    fn test_near_integer_value_outside_exact_box_is_not_an_incumbent() {
        let mut p = Problem::new();
        p.variables.push(Variable {
            name: "x".into(),
            obj_coeff: 0.0,
            lower: 1.0000004,
            upper: 1.0000004,
            kind: VarKind::Integer,
        });

        assert!(matches!(solve(&p), Err(LpError::Infeasible)));
    }

    #[test]
    fn test_binary_near_integer_value_outside_effective_box_is_not_an_incumbent() {
        let mut p = Problem::new();
        p.variables.push(Variable {
            name: "x".into(),
            obj_coeff: 0.0,
            lower: 1.0000004,
            upper: f64::INFINITY,
            kind: VarKind::Binary,
        });

        assert!(matches!(solve(&p), Err(LpError::Infeasible)));
    }

    #[test]
    fn test_integer_candidate_rejects_malformed_direct_inputs() {
        let mut p = Problem::new();
        p.variables.push(Variable {
            name: "x".into(),
            obj_coeff: 1.0,
            lower: 0.0,
            upper: 1.0,
            kind: VarKind::Integer,
        });
        let relaxation = Solution {
            objective: 1.0,
            values: vec![1.0],
        };

        assert!(integer_candidate_from_relaxation(
            &p,
            &Solution {
                objective: 0.0,
                values: vec![],
            },
        )
        .is_none());

        p.obj_constant = f64::NAN;
        assert!(integer_candidate_from_relaxation(&p, &relaxation).is_none());

        p.obj_constant = 0.0;
        p.variables[0].obj_coeff = f64::INFINITY;
        assert!(integer_candidate_from_relaxation(&p, &relaxation).is_none());

        p.variables[0].obj_coeff = 1.0;
        p.constraints.push(Constraint {
            name: "bad".into(),
            kind: RowKind::Le,
            coeffs: vec![(0, f64::INFINITY)],
            rhs: 1.0,
        });
        assert!(integer_candidate_from_relaxation(&p, &relaxation).is_none());
    }

    #[test]
    fn test_pick_fractional_scores_negative_values_symmetrically() {
        let mut p = Problem::new();
        p.variables.push(Variable {
            name: "x".into(),
            obj_coeff: 0.0,
            lower: f64::NEG_INFINITY,
            upper: f64::INFINITY,
            kind: VarKind::Integer,
        });
        p.variables.push(Variable {
            name: "y".into(),
            obj_coeff: 0.0,
            lower: f64::NEG_INFINITY,
            upper: f64::INFINITY,
            kind: VarKind::Integer,
        });

        assert!((fractional_score(-2.4) - 0.4).abs() < 1e-12);
        assert!((fractional_score(2.4) - 0.4).abs() < 1e-12);
        assert_eq!(pick_fractional(&p, &[-2.4, 3.1]), Some((0, -2.4)));
    }
}
