// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Exact lazy Hoffman decomposition for fixed-charge network design.
//!
//! The integral design variables stay in AY's PB master.  Each candidate is
//! checked by an exact rational max flow over the eliminated continuous arcs.
//! A failed max flow returns its residual min-cut, which is reconstructed as a
//! globally valid Hoffman capacity row and installed only after the candidate
//! is checked to violate it.  A successful max flow supplies an exact original
//! witness, checked by [`Model::check_point`](crate::Model::check_point).
//!
//! This is the standard branch-and-cut/decomposition formulation, but kept at
//! a deliberately narrow proof boundary: recognition, min-cut separation,
//! cut reconstruction, lift, and objective equality are all exact.  Deadline
//! or resource exhaustion declines to the ordinary MILP path.

use std::time::{Duration, Instant};

use crate::network_design_pb::{NetworkDesignProjection, NetworkDesignSeparation};
use crate::pb_route::{try_solve_portfolio_trial, PbRouteDecision};
use crate::Model;

/// Independent replay/work envelope.  A model requiring one cut per design
/// assignment cannot consume unbounded memory before the native fallback gets
/// control.  Every installed cut is globally valid, so reaching this cap is a
/// decline rather than a weakened answer.
const MAX_LAZY_HOFFMAN_CUTS: usize = 4_096;

/// Continue lazy separation from a projection already built by the production
/// adapter.  Reusing this immutable recognition result avoids charging a model
/// a second exact matrix census merely because an eager symmetry attempt was
/// considered first.
pub(crate) fn try_solve_projection(
    model: &Model,
    mut projection: NetworkDesignProjection,
    trial_deadline: Instant,
) -> Option<PbRouteDecision> {
    let started = Instant::now();
    let initial_rows = projection.master.num_rows();
    if trace_enabled() {
        let balance_rows: usize = projection
            .components
            .iter()
            .map(|component| component.balance_rows.len())
            .sum();
        let flow_columns: usize = projection
            .components
            .iter()
            .map(|component| component.flow_columns.len())
            .sum();
        eprintln!(
            "AY_MILP_TRACE network-benders: admitted master-cols={} master-rows={} \
             seed-hoffman-rows={} components={} balance-rows={} flow-cols={}",
            projection.master.num_cols(),
            initial_rows,
            projection.hoffman_rows,
            projection.components.len(),
            balance_rows,
            flow_columns,
        );
    }

    let mut pb_wall = Duration::ZERO;
    let mut separation_wall = Duration::ZERO;
    let mut install_wall = Duration::ZERO;
    for cuts in 0..=MAX_LAZY_HOFFMAN_CUTS {
        if Instant::now() >= trial_deadline {
            return None;
        }
        let pb_started = Instant::now();
        let decision = try_solve_portfolio_trial(&projection.master, trial_deadline)?;
        pb_wall += pb_started.elapsed();
        match decision {
            PbRouteDecision::Infeasible
            | PbRouteDecision::CertifiedSingleRowInfeasible { .. }
            | PbRouteDecision::CertifiedMultiRowInfeasible { .. } => {
                trace_result(
                    &projection,
                    initial_rows,
                    cuts,
                    "INFEASIBLE",
                    started,
                    pb_wall,
                    separation_wall,
                    install_wall,
                );
                return Some(PbRouteDecision::Infeasible);
            }
            PbRouteDecision::Feasible {
                model_values,
                incumbent_only,
            } => {
                let separation_started = Instant::now();
                let separation = projection
                    .separate_exact(model, &model_values, Some(trial_deadline))
                    .ok()?;
                separation_wall += separation_started.elapsed();
                match separation {
                    NetworkDesignSeparation::Feasible(original_values) => {
                        trace_result(
                            &projection,
                            initial_rows,
                            cuts,
                            "FEASIBLE",
                            started,
                            pb_wall,
                            separation_wall,
                            install_wall,
                        );
                        return Some(PbRouteDecision::Feasible {
                            model_values: original_values,
                            incumbent_only,
                        });
                    }
                    NetworkDesignSeparation::Violated(cut) => {
                        if cuts == MAX_LAZY_HOFFMAN_CUTS {
                            return None;
                        }
                        let install_started = Instant::now();
                        projection
                            .install_cut(cut, &model_values, Some(trial_deadline))
                            .ok()?;
                        install_wall += install_started.elapsed();
                        trace_iteration(
                            &projection,
                            cuts + 1,
                            started,
                            pb_wall,
                            separation_wall,
                            install_wall,
                        );
                    }
                }
            }
            PbRouteDecision::Optimal {
                value,
                model_values,
            } => {
                let separation_started = Instant::now();
                let separation = projection
                    .separate_exact(model, &model_values, Some(trial_deadline))
                    .ok()?;
                separation_wall += separation_started.elapsed();
                match separation {
                    NetworkDesignSeparation::Feasible(original_values) => {
                        if model.objective_value_at(&original_values) != value {
                            return None;
                        }
                        trace_result(
                            &projection,
                            initial_rows,
                            cuts,
                            "OPTIMAL",
                            started,
                            pb_wall,
                            separation_wall,
                            install_wall,
                        );
                        return Some(PbRouteDecision::Optimal {
                            value,
                            model_values: original_values,
                        });
                    }
                    NetworkDesignSeparation::Violated(cut) => {
                        if cuts == MAX_LAZY_HOFFMAN_CUTS {
                            return None;
                        }
                        let install_started = Instant::now();
                        projection
                            .install_cut(cut, &model_values, Some(trial_deadline))
                            .ok()?;
                        install_wall += install_started.elapsed();
                        trace_iteration(
                            &projection,
                            cuts + 1,
                            started,
                            pb_wall,
                            separation_wall,
                            install_wall,
                        );
                    }
                }
            }
        }
    }
    None
}

fn trace_result(
    projection: &crate::network_design_pb::NetworkDesignProjection,
    initial_rows: usize,
    cuts: usize,
    verdict: &str,
    started: Instant,
    pb_wall: Duration,
    separation_wall: Duration,
    install_wall: Duration,
) {
    if trace_enabled() {
        eprintln!(
            "AY_MILP_TRACE network-benders: master-cols={} initial-rows={} components={} \
             lazy-cuts={} verdict={} pb-wall={:.6}s separation-wall={:.6}s \
             install-wall={:.6}s wall={:.6}s",
            projection.master.num_cols(),
            initial_rows,
            projection.components.len(),
            cuts,
            verdict,
            pb_wall.as_secs_f64(),
            separation_wall.as_secs_f64(),
            install_wall.as_secs_f64(),
            started.elapsed().as_secs_f64(),
        );
    }
}

fn trace_iteration(
    projection: &crate::network_design_pb::NetworkDesignProjection,
    cuts: usize,
    started: Instant,
    pb_wall: Duration,
    separation_wall: Duration,
    install_wall: Duration,
) {
    if trace_enabled() {
        eprintln!(
            "AY_MILP_TRACE network-benders: lazy-cuts={} master-rows={} pb-wall={:.6}s \
             separation-wall={:.6}s install-wall={:.6}s wall={:.6}s",
            cuts,
            projection.master.num_rows(),
            pb_wall.as_secs_f64(),
            separation_wall.as_secs_f64(),
            install_wall.as_secs_f64(),
            started.elapsed().as_secs_f64(),
        );
    }
}

fn trace_enabled() -> bool {
    // Cached: the ratchet in `tests/env_ledger.rs` counts a bare `env::var_os`
    // on the solve path as a LIVE read — a fresh `getenv` a concurrent
    // `set_var` can race, which priming cannot help. `OnceLock` is the shape
    // that ratchet asks for and `simplex.rs` already uses.
    static ENABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ENABLED.get_or_init(|| std::env::var_os("AY_MILP_TRACE").is_some())
}

/// Force this module's cached env accessor at solve entry, so a consumer that
/// rewrites its environment between window solves cannot race it. Called from
/// `bab::prime_env_all`.
pub(crate) fn prime_env() {
    let _ = trace_enabled();
}
