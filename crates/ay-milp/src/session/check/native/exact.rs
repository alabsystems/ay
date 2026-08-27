// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact-rational anchor for continuous models.

use super::super::*;

pub(super) fn solve(session: &BabSession, state: &CheckState) -> Outcome {
    if !state.has_objective {
        return solve_feasibility(session);
    }
    if !deadline_expired(&session.opts) {
        if let Some(outcome) = continuous_float_first_optimum(
            &session.model,
            &state.objective,
            session.opts.deadline,
            &session.opts,
        ) {
            return outcome;
        }
    }
    solve_objective(session, state)
}

fn solve_objective(session: &BabSession, state: &CheckState) -> Outcome {
    let budget = budget_for(&session.model, &session.opts);
    let mut lp = ExactLp::new(&session.model);
    let objective = exact_objective_for_rim(state);
    let sense = session.model.sense();
    let minimization: Vec<(u32, Rational)> = match sense {
        Sense::Minimize => objective.clone(),
        Sense::Maximize => objective
            .iter()
            .map(|(column, coefficient)| (*column, -coefficient.clone()))
            .collect(),
    };
    match lp.minimize(&minimization, &budget) {
        LpOptimum::Optimal { value, multipliers } => {
            let bound = match sense {
                Sense::Minimize => value,
                Sense::Maximize => -value,
            };
            let offset = state.exact_objective.as_ref().map_or_else(
                || session.model.obj_offset_exact(),
                |(_, offset)| offset.clone(),
            );
            let cert = OptimalityCertificate {
                sense,
                objective: objective
                    .iter()
                    .map(|(column, coefficient)| (*column, coefficient.to_big()))
                    .collect(),
                bound: bound.clone(),
                multipliers,
            };
            // The common finish gate repeats this check in release builds.
            debug_assert!(cert.verify(&session.model).is_ok());
            Outcome::Optimal {
                value: bound + offset,
                model_values: lp.structural_values(),
                cert: Some(cert),
            }
        }
        LpOptimum::Unbounded => Outcome::Unbounded,
        LpOptimum::Infeasible(cert) => Outcome::Infeasible {
            cert: Some(cert),
            tree_cert: None,
        },
        LpOptimum::Unknown(reason) => Outcome::Unknown { reason },
    }
}

fn exact_objective_for_rim(state: &CheckState) -> Vec<(u32, Rational)> {
    match &state.exact_objective {
        Some((coefficients, _)) => {
            let mut objective: Vec<(u32, Rational)> = coefficients
                .iter()
                .map(|(column, coefficient)| (*column, Rational::from_big(coefficient.clone())))
                .collect();
            objective.sort_unstable_by_key(|&(column, _)| column);
            objective
        }
        None => exact_obj(&state.objective),
    }
}

fn solve_feasibility(session: &BabSession) -> Outcome {
    let budget = budget_for(&session.model, &session.opts);
    let mut lp = ExactLp::new(&session.model);
    match lp.make_feasible(&budget) {
        LpFeasibility::Feasible => Outcome::Feasible {
            model_values: lp.structural_values(),
            incumbent_only: false,
            dual_bound: None,
        },
        LpFeasibility::Infeasible(cert) => Outcome::Infeasible {
            cert: Some(cert),
            tree_cert: None,
        },
        LpFeasibility::Unknown(reason) => Outcome::Unknown { reason },
    }
}
