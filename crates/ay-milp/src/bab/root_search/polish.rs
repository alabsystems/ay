// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Final feasibility-jump polish for an admitted root incumbent.

use super::*;

pub(super) fn run(
    context: &mut RootHeuristicContext<'_>,
    budget: RootHeuristicBudget,
    progress: &pump::PumpProgress,
) {
    let stalled = progress
        .last_gain
        .is_some_and(|gain| gain.elapsed() >= budget.stall);
    if stalled && context.policy.trace.enabled() {
        eprintln!(
            "--trace   root phase stalled ({:.2}s since last gain) — skipping FJ pass (at {:.2}s)",
            progress
                .last_gain
                .map_or(0.0, |gain| gain.elapsed().as_secs_f64()),
            context.phase_started.elapsed().as_secs_f64()
        );
    }
    let deadline = polish_deadline(context, budget, progress.last_gain);
    let gap_is_tight = root_gap_is_tight(context);
    if gap_is_tight && context.policy.trace.enabled() {
        eprintln!(
            "--trace   root gap already tight — skipping FJ polish (at {:.2}s)",
            context.phase_started.elapsed().as_secs_f64()
        );
    }
    let Some((point, old_value)) = context
        .state
        .incumbent
        .clone()
        .filter(|_| !stalled && context.suite.runs() && !gap_is_tight)
    else {
        return;
    };
    let model_value = match context.frame.sense {
        Sense::Minimize => old_value.clone(),
        Sense::Maximize => -old_value.clone(),
    };
    let moves = if context.policy.execution.is_cheap() {
        60_000
    } else {
        400_000
    };
    let improved = feasibility_jump(
        context.frame.model,
        context.frame.integer_columns,
        &point,
        context.state.root_lower,
        context.state.root_upper,
        &model_value,
        7,
        moves,
        deadline,
    )
    .map(|point| {
        if context.policy.execution.is_cheap() {
            point
        } else {
            swap_improve(
                context.frame.model,
                context.frame.integer_columns,
                point,
                deadline,
            )
        }
    });
    if let Some(point) = improved {
        let value = minimize_value(context.frame.lp, &point);
        if value < old_value {
            if context.policy.trace.enabled() {
                eprintln!("--trace root feasibility-jump incumbent = {value}");
            }
            *context.state.incumbent = Some((point, value));
        }
    }
    if context.policy.trace.enabled() {
        eprintln!(
            "--trace   root FJ pass done (at {:.2}s)",
            context.phase_started.elapsed().as_secs_f64()
        );
    }
}

fn polish_deadline(
    context: &RootHeuristicContext<'_>,
    budget: RootHeuristicBudget,
    last_gain: Option<Instant>,
) -> Option<Instant> {
    let deadline = match last_gain {
        Some(gain) => Some(
            budget
                .phase
                .or(context.frame.deadline)
                .map_or(gain + budget.stall, |limit| limit.min(gain + budget.stall)),
        ),
        None => budget.phase.or(context.frame.deadline),
    };
    let cap = fj_polish_cap();
    if cap <= 0.0 {
        return deadline;
    }
    let capped = Instant::now() + Duration::from_secs_f64(cap);
    Some(deadline.map_or(capped, |limit| limit.min(capped)))
}

fn root_gap_is_tight(context: &RootHeuristicContext<'_>) -> bool {
    context
        .state
        .incumbent
        .as_ref()
        .is_some_and(|(_, incumbent)| {
            let threshold = fj_skip_gap();
            if threshold <= 0.0 {
                return false;
            }
            let incumbent = to_f64(incumbent);
            let root_bound = (0..context.frame.lp.n)
                .map(|column| context.frame.lp.cost[column] * context.frame.root.values[column])
                .sum::<f64>();
            incumbent - root_bound <= threshold * (1.0 + incumbent.abs())
        })
}
