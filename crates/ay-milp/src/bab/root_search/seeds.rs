// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Ordered root-seed construction and exact admission.

use super::*;

pub(super) fn run(
    context: &mut RootHeuristicContext<'_>,
    budget: RootHeuristicBudget,
    root_work: Duration,
    mut progress: pump::PumpProgress,
) -> pump::PumpProgress {
    let seed = progress
        .seed
        .take()
        .or_else(|| set_partition_seed(context, root_work))
        .or_else(|| rens_seed(context, budget.phase));
    if crate::debug_flags::milp_debug_flags().trace {
        eprintln!(
            "--trace   pump+rens done (at {:.2}s)",
            context.phase_started.elapsed().as_secs_f64()
        );
    }
    let seed = finish_lp_seed(context, budget.phase, seed);
    let seed = seed.map(|point| lns::set_partition(context, point));
    let seed = seed.map(|point| lns::fixed_charge(context, point));
    let seed = market_share_seed(context, seed);
    admit(context, &mut progress, seed);
    progress
}

fn set_partition_seed(
    context: &RootHeuristicContext<'_>,
    root_work: Duration,
) -> Option<Vec<BigRational>> {
    if !context.suite.runs() {
        return None;
    }
    let mut window = Duration::ZERO;
    let deadline = context.frame.deadline.map(|limit| {
        let now = Instant::now();
        window = setpart_window(root_work, limit.saturating_duration_since(now));
        now + window
    });
    let seed = set_partition_construct(
        context.frame.model,
        &context.frame.root.values,
        0xA1_05,
        deadline,
    );
    if context.policy.trace.enabled() {
        eprintln!(
            "--trace   set-partition construct: found={} (window {:.2}s from root work {:.2}s)",
            seed.is_some(),
            window.as_secs_f64(),
            root_work.as_secs_f64(),
        );
    }
    seed
}

fn rens_seed(
    context: &RootHeuristicContext<'_>,
    deadline: Option<Instant>,
) -> Option<Vec<BigRational>> {
    if !context.suite.runs() {
        return None;
    }
    rens(
        context.frame.model,
        context.frame.lp,
        context.frame.integer_columns,
        &context.frame.root.values,
        &context.frame.root.duals,
        deadline,
    )
}

fn finish_lp_seed(
    context: &RootHeuristicContext<'_>,
    heuristic_deadline: Option<Instant>,
    seed: Option<Vec<BigRational>>,
) -> Option<Vec<BigRational>> {
    seed.map(|point| {
        let point = swap_improve(
            context.frame.model,
            context.frame.integer_columns,
            point,
            heuristic_deadline,
        );
        if context.policy.trace.enabled() {
            eprintln!(
                "--trace   seed swap_improve done (at {:.2}s)",
                context.phase_started.elapsed().as_secs_f64()
            );
        }
        point
    })
    .or_else(|| {
        context.suite.runs().then(|| {
            dive_for_incumbent(
                context.frame.model,
                context.frame.lp,
                context.frame.integer_columns,
                context.frame.minimize_objective,
                &context.frame.lp.lower,
                &context.frame.lp.upper,
                Some((
                    context.frame.root.basis.as_slice(),
                    context.frame.root.at.as_slice(),
                )),
                heuristic_deadline,
                context.frame.deadline,
            )
        })?
    })
    .or_else(|| {
        context.suite.runs().then(|| {
            round_to_incumbent(
                context.frame.model,
                context.frame.integer_columns,
                &context.frame.root.values,
            )
        })?
    })
}

fn market_share_seed(
    context: &RootHeuristicContext<'_>,
    seed: Option<Vec<BigRational>>,
) -> Option<Vec<BigRational>> {
    let allowed = context.suite.runs()
        && context.policy.execution.is_top_level()
        && !context.policy.execution.is_cheap()
        && !context.policy.execution.is_projected()
        && !in_rens()
        && !crate::tune::on(crate::tune::Knob::NoMsWalk);
    let walked = allowed
        .then(|| market_share_walk(context.frame.model, seed.as_deref(), context.frame.deadline))
        .flatten();
    match walked {
        Some(point) => {
            if context.policy.trace.enabled() {
                eprintln!(
                    "--trace   market-share walk displaced the seed (at {:.2}s)",
                    context.phase_started.elapsed().as_secs_f64()
                );
            }
            Some(point)
        }
        None => seed,
    }
}

fn admit(
    context: &mut RootHeuristicContext<'_>,
    progress: &mut pump::PumpProgress,
    seed: Option<Vec<BigRational>>,
) {
    // A heuristic point has no pruning authority until exact model validation.
    let seed = seed.filter(|point| {
        let valid = context.frame.model.check_point(point).is_ok();
        if !valid && context.policy.trace.enabled() {
            eprintln!("--trace !! root heuristic seed REJECTED by check_point — dropped");
        }
        valid
    });
    let Some(point) = seed else {
        if context.policy.trace.enabled() {
            eprintln!(
                "--trace root heuristic found nothing (in {:.2}s)",
                context.phase_started.elapsed().as_secs_f64()
            );
        }
        return;
    };
    let value = minimize_value(context.frame.lp, &point);
    if progress
        .seed_value
        .as_ref()
        .is_some_and(|pump_value| value < *pump_value)
    {
        progress.last_gain = Some(Instant::now());
    }
    if context.policy.trace.enabled() {
        eprintln!(
            "--trace root heuristic incumbent = {value} (in {:.2}s)",
            context.phase_started.elapsed().as_secs_f64()
        );
    }
    if context
        .state
        .incumbent
        .as_ref()
        .is_none_or(|(_, incumbent)| value < *incumbent)
    {
        *context.state.incumbent = Some((point, value));
    }
}
