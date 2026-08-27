// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Structure-specific root neighbourhood improvement.

use super::*;

pub(super) fn set_partition(
    context: &RootHeuristicContext<'_>,
    point: Vec<BigRational>,
) -> Vec<BigRational> {
    if !context.policy.execution.is_top_level()
        || in_rens()
        || crate::tune::on(crate::tune::Knob::NoSplns)
    {
        return point;
    }
    let wide_tall = context.frame.model.num_cols() >= 10 * context.frame.model.num_rows()
        && context.frame.model.num_rows() >= 200;
    let share = if wide_tall {
        SPLNS_TIME_SHARE
    } else {
        SPLNS_TIME_SHARE_FAST_TREE
    };
    let deadline = context.frame.deadline.map(|limit| {
        let now = Instant::now();
        let remaining = limit.saturating_duration_since(now);
        let mut window = remaining.mul_f64(share);
        if wide_tall {
            let tree_reserve = Duration::from_secs_f64(SPLNS_WIDE_TREE_RESERVE_SECS);
            window = window.min(remaining.saturating_sub(tree_reserve));
            window = window.min(Duration::from_secs_f64(SPLNS_WIDE_ABS_CAP_SECS));
        }
        now + window
    });
    let reduced_costs = root_reduced_costs(context);
    let improved = set_partition_improve(
        context.frame.model,
        &context.frame.root.values,
        &reduced_costs,
        &context.frame.root.duals,
        &point,
        0x5A17_C0DE,
        deadline,
    );
    if context.policy.trace.enabled() && improved.is_some() {
        eprintln!(
            "--trace   setpart LNS improved seed (at {:.2}s)",
            context.phase_started.elapsed().as_secs_f64()
        );
    }
    improved.unwrap_or(point)
}

fn root_reduced_costs(context: &RootHeuristicContext<'_>) -> Vec<f64> {
    (0..context.frame.lp.n)
        .map(|column| {
            let mut reduced = context.frame.lp.cost[column];
            for (row, coefficient) in context.frame.lp.column(column) {
                reduced -= coefficient * context.frame.root.duals.get(row).copied().unwrap_or(0.0);
            }
            reduced
        })
        .collect()
}

pub(super) fn fixed_charge(
    context: &RootHeuristicContext<'_>,
    point: Vec<BigRational>,
) -> Vec<BigRational> {
    let point_value = (0..context.frame.lp.n)
        .filter(|&column| context.frame.lp.cost[column] != 0.0)
        .map(|column| context.frame.lp.cost[column] * to_f64(&point[column]))
        .sum::<f64>();
    let root_bound = (0..context.frame.lp.n)
        .map(|column| context.frame.lp.cost[column] * context.frame.root.values[column])
        .sum::<f64>();
    let gap_is_wide = point_value - root_bound > 0.07 * (1.0 + point_value.abs());
    let requested_share = crate::tune::real_opt(crate::tune::Knob::FlipShare);
    if !context.policy.execution.is_top_level()
        || in_rens()
        || !gap_is_wide
        || requested_share.is_none()
    {
        return point;
    }
    let share = requested_share.unwrap_or(FLIP_LNS_TIME_SHARE);
    // The cap arm is retained exactly: an explicit share opts into the pure
    // fraction, while a future default arm may restore the lane-specific cap.
    let cap_seconds = if requested_share.is_none() && context.frame.lp.tall_lu() {
        let default = if crate::simplex::warm_lu_enabled() {
            FLIP_LNS_WARM_TALL_CAP_SECS
        } else {
            FLIP_LNS_TALL_CAP_SECS
        };
        Some(crate::tune::real(crate::tune::Knob::FlipCapSecs, default))
    } else {
        None
    };
    let deadline = context.frame.deadline.map(|limit| {
        let now = Instant::now();
        let mut window = limit.saturating_duration_since(now).mul_f64(share);
        if let Some(seconds) = cap_seconds {
            window = window.min(Duration::from_secs_f64(seconds));
        }
        now + window
    });
    let improved = flip_lns(
        context.frame.model,
        context.frame.lp,
        context.frame.integer_columns,
        context.frame.minimize_objective,
        &point,
        deadline,
        context.frame.deadline,
    );
    if context.policy.trace.enabled() && improved.is_some() {
        eprintln!(
            "--trace   flip-LNS improved seed (at {:.2}s)",
            context.phase_started.elapsed().as_secs_f64()
        );
    }
    improved.unwrap_or(point)
}
