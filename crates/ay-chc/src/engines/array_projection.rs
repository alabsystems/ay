// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Bounded Safe-candidate search over projected array predicate arguments.
//! Argument erasure never supplies an original counterexample. Only a lifted
//! model admitted by the existing original-clause verifier can return Safe.
//! No source-bound shared hints, caches, tracing or progress are reused across
//! the changed signatures. Unsupported cases retain the ordinary PDR route.

use super::{
    enforce_pdr_proof_return_boundary, validate_pdr_proof_result, ChcEngineResult, ChcProblem,
    InvariantModel, PdrConfig, PdrResult, PdrSolver, ValidationEvidence, VerifiedChcResult,
};
use ay_core::time::Instant;
use control::Owner;
use projection::Projection;

pub(super) mod control;
pub(super) mod expression;
mod lift;
mod projection;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Phase {
    Projection,
    Search,
    Lift,
    Validation,
    Validated,
    Publication,
    Cleanup,
}

fn unknown() -> VerifiedChcResult {
    VerifiedChcResult::from_validated(
        ChcEngineResult::Unknown,
        ValidationEvidence::FullVerification,
    )
}

pub(super) fn source_bound_channels(config: &PdrConfig) -> bool {
    !config.user_hints.is_empty() || untranslated_source_bound_channels(config)
}

/// Static user hints require a separate authenticated bridge. Every other
/// original-position/shared channel still declines across either projection.
pub(super) fn untranslated_source_bound_channels(config: &PdrConfig) -> bool {
    config.enable_tla_trace
        || config.tla_trace_path.is_some()
        || !config.user_hint_providers.0.is_empty()
        || config.lemma_hints.is_some()
        || config.lemma_cache.is_some()
        || config.blackboard.is_some()
        || !config.bv_bit_groups.is_empty()
        || !config.array_scalarization_extra_indices.is_empty()
        || config.bv_to_int_relaxed
        || config.progress_snapshot.is_some()
}

/// None permits original search fallback. An observed caller stop is terminal
/// Some(Unknown), including cancellation observed during cleanup.
pub(super) fn run(
    problem: &ChcProblem,
    config: &PdrConfig,
    solve_deadline: Option<Instant>,
) -> Option<VerifiedChcResult> {
    run_observed(
        problem,
        config,
        solve_deadline,
        &mut |source, configured| PdrSolver::solve_problem(source, configured),
        &mut |model, configured, deadline| {
            validate_pdr_proof_result(problem, PdrResult::Safe(model), configured, deadline)
        },
        &mut |_| {},
    )
}

fn run_observed(
    problem: &ChcProblem,
    config: &PdrConfig,
    solve_deadline: Option<Instant>,
    search: &mut dyn FnMut(&ChcProblem, PdrConfig) -> PdrResult,
    validate: &mut dyn FnMut(InvariantModel, &PdrConfig, Option<Instant>) -> VerifiedChcResult,
    observe: &mut dyn FnMut(Phase),
) -> Option<VerifiedChcResult> {
    let mut owner = Owner::capture(config, solve_deadline);
    let _ambient_lane = owner.install_lane();
    let _memory = owner.memory().install();
    let _original_deadline = crate::smt::ScopedSolveDeadline::new(owner.deadline());
    let result = (|| {
        if !owner.open() {
            return Some(unknown());
        }
        // These capabilities refer to the caller's variable positions or
        // result surface. Until they can be translated, leave that route alone.
        if source_bound_channels(config) {
            return None;
        }
        let probe_deadline = owner.probe_deadline()?;
        observe(Phase::Projection);
        let projection = Projection::new(problem, &mut || {
            owner.open() && Instant::now() < probe_deadline
        })?;
        observe(Phase::Search);
        if !owner.open() || Instant::now() >= probe_deadline {
            return None;
        }
        let search_config = owner.search_config(config, probe_deadline);
        let raw = {
            // Only this speculative phase gets the shorter clock. Its expiry
            // must not latch as caller cancellation or poison ordinary fallback.
            let _solve = crate::smt::ScopedSolveDeadline::new(Some(probe_deadline));
            let _smt = crate::smt::ScopedSmtDeadline::install_until(probe_deadline);
            search(projection.reduced(), search_config)
        };
        if !owner.open() || Instant::now() >= probe_deadline {
            return None;
        }
        let PdrResult::Safe(model) = raw else {
            // Unsafe on an over-approximation has no original witness authority.
            return None;
        };
        observe(Phase::Lift);
        let lifted = projection.lift(&model, &mut || owner.open())?;
        drop(model);
        drop(projection);
        observe(Phase::Validation);
        if !owner.open() {
            return Some(unknown());
        }
        let validation_config = owner.validation_config(config);
        let result = validate(lifted, &validation_config, owner.deadline());
        observe(Phase::Validated);
        if !owner.open() {
            return Some(unknown());
        }
        if !matches!(&result, VerifiedChcResult::Safe(_)) {
            return None;
        }
        observe(Phase::Publication);
        if !owner.open() {
            return Some(unknown());
        }
        Some(enforce_pdr_proof_return_boundary(
            result,
            &validation_config,
            owner.deadline(),
        ))
    })();
    // Every temporary projected owner has been dropped before this final poll.
    // Opaque cloning/allocation/cleanup are bracketed, not hard-latency bounded.
    observe(Phase::Cleanup);
    if owner.open() {
        result
    } else {
        drop(result);
        let _ = owner.open();
        Some(unknown())
    }
}

#[cfg(test)]
mod tests;
