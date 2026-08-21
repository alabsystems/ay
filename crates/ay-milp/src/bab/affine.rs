// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact affine-aggregation routing and caller-frame postsolve.

use super::*;

/// Try the adjacent exact affine-aggregation and duplicate-column reductions.
///
/// Affine aggregation is default-off and exact: fixed columns are projected
/// out and an implied-free equality pivot becomes an affine form, all in
/// `BigRational`, behind a fail-closed exact-`f64` emit gate. The reduced
/// objective differs by one exact constant. Every eliminated column has an
/// exact reverse recovery, and every recovered point is re-checked and
/// re-scored against the caller model before a verdict leaves.
///
/// Reduced-frame proof objects travel only through the typed replay artifact;
/// they are never relabelled as caller-frame `Outcome` evidence. The session
/// drains and independently verifies that artifact against its own model.
/// Infeasibility still reaches `harvest_tree_cert_by_resolve`, which obtains a
/// literal caller-frame tree when capture is armed. The reduction remains an
/// opt-in measurement arm until corpus evidence supports enabling it.
pub(super) fn solve_aggregation_or_dedup(
    model: &Model,
    opts: &SolveOpts,
    full: SearchMode,
    reductions_run: bool,
    entry_deadline: Option<Instant>,
) -> Option<Outcome> {
    if reductions_run && crate::presolve::implied_free::enabled() {
        if let Some((reduced, post)) = crate::presolve::aggregate_implied_free_equalities(
            model,
            entry_deadline,
            opts.memory_budget,
        ) {
            let outcome = solve_milp_in(&reduced, opts, full, None, &[], &[], &[]);
            let expanded = expand_affine_aggregation_outcome(
                &outcome,
                &post,
                model,
                entry_deadline,
                opts.memory_budget,
            );
            let source_primal = match &expanded {
                Outcome::Optimal { model_values, .. } | Outcome::Feasible { model_values, .. } => {
                    Some(model_values.clone())
                }
                _ => None,
            };
            if let Some(certificate) = post.certificate_for_outcome_with_source_primal(
                &outcome,
                &reduced,
                model,
                source_primal,
                entry_deadline,
                opts.memory_budget,
            ) {
                // The session drains and independently replays this once
                // against its source model.
                crate::presolve::implied_free::set_pending_certificate(certificate);
            }
            return Some(harvest_tree_cert_by_resolve(
                expanded,
                model,
                opts,
                full,
                entry_deadline,
            ));
        }
    }
    if reductions_run && dedup_enabled() {
        if let Some((reduced, map)) = dedup_columns(model) {
            let outcome = solve_milp_in(&reduced, opts, full, None, &[], &[], &[]);
            return Some(harvest_tree_cert_by_resolve(
                expand_dedup_outcome_certified(outcome, &map, model),
                model,
                opts,
                full,
                entry_deadline,
            ));
        }
    }
    None
}

/// Lift an exact affine-aggregation solve to the caller's literal frame.
///
/// The reduction is an objective-preserving bijection up to `const_delta`, so
/// rigorous bounds and verdicts transfer. Integer columns can disappear,
/// however, and a reduced split on the survivors need not be complete in the
/// caller's frame. Reduced evidence therefore travels only in the typed replay
/// artifact. Primal points are widened exactly, checked against the original
/// model, and re-scored there before an optimal verdict leaves; ordinary
/// reduced-frame proof fields are stripped fail-closed.
pub(super) fn expand_affine_aggregation_outcome(
    outcome: &Outcome,
    post: &crate::presolve::AffineAggregationPostsolve,
    original: &Model,
    deadline: Option<Instant>,
    memory_budget: Option<usize>,
) -> Outcome {
    let rejected = |detail: String| Outcome::Unknown {
        reason: UnknownReason::WitnessRejected { detail },
    };
    let widen_and_check = |values: &[BigRational], what: &str| {
        let full = post.widen(values, deadline, memory_budget).ok_or_else(|| {
            format!(
                "equality aggregation: {what} has {} values in the wrong reduced frame",
                values.len()
            )
        })?;
        original.check_point(&full).map_err(|violation| {
            format!(
                "equality aggregation: recovered {what} is not feasible for the caller's model: \
                 {violation:?}"
            )
        })?;
        Ok::<_, String>(full)
    };
    let constant = post.const_delta();
    match outcome {
        Outcome::Optimal {
            value,
            model_values,
            ..
        } => {
            let full = match widen_and_check(model_values, "optimal point") {
                Ok(full) => full,
                Err(detail) => return rejected(detail),
            };
            let claimed = value + constant;
            let restated = original.objective_value_at(&full);
            if claimed != restated {
                return rejected(format!(
                    "equality aggregation: reduced optimum lifts to {claimed}, but the caller's \
                     objective scores the recovered point at {restated}"
                ));
            }
            Outcome::Optimal {
                value: restated,
                model_values: full,
                cert: None,
            }
        }
        Outcome::Feasible {
            model_values,
            incumbent_only,
            dual_bound,
        } => match widen_and_check(model_values, "incumbent") {
            Ok(full) => Outcome::Feasible {
                model_values: full,
                incumbent_only: *incumbent_only,
                dual_bound: dual_bound.as_ref().map(|bound| bound + constant),
            },
            Err(detail) => rejected(detail),
        },
        Outcome::Bound {
            dual_bound,
            rigorous,
        } => Outcome::Bound {
            dual_bound: dual_bound + constant,
            rigorous: *rigorous,
        },
        Outcome::Infeasible { .. } => Outcome::Infeasible {
            // Reduced indices never travel in caller-frame outcome fields.
            cert: None,
            tree_cert: None,
        },
        other => other.clone(),
    }
}
