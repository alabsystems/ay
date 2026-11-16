// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Bounded original-clause reachability before the ordinary cyclic PDR search.
//! Concrete forward candidates and existing BMC witness replay require the
//! unchanged strict ORIGINAL PDR validator. No projected verdict/model is input.
//! The speculative clock reserves ordinary fallback; its expiry is not a
//! caller stop. Opaque graph analysis/cloning/drop are bracketed, not metered.

use super::{
    array_projection::source_bound_channels, downgrade_unsafe_if_overapproximated,
    enforce_pdr_proof_return_boundary, validate_pdr_proof_result, ChcEngineResult, ChcProblem,
    Counterexample, PdrConfig, PdrResult, ValidationEvidence, VerifiedChcResult,
};
use ay_core::time::Instant;
use std::time::Duration;

mod control;
mod search;
use control::Owner;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Phase {
    Eligibility,
    Search,
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

/// Only None permits fallback. An observed original stop remains terminal even
/// when a parent token resets or a temporary memory scope has been dropped.
pub(super) fn run(
    problem: &ChcProblem,
    config: &PdrConfig,
    solve_deadline: Option<Instant>,
) -> Option<VerifiedChcResult> {
    run_owned(
        problem,
        config,
        solve_deadline,
        &mut |original, _, configured, owner, probe| {
            search::original(original, configured, owner, probe)
        },
        &mut |candidate, configured, deadline| {
            validate_pdr_proof_result(problem, PdrResult::Unsafe(candidate), configured, deadline)
        },
        &mut |_| {},
    )
}

fn eligible(
    problem: &ChcProblem,
    config: &PdrConfig,
    owner: &mut Owner,
    probe_deadline: Instant,
) -> bool {
    // Do not consume source-bound side channels that this auxiliary engine
    // cannot honor, or search an over-approximation for a refutation.
    if source_bound_channels(config)
        || config.disable_cex_replay
        || problem.has_stripped_body_forall()
        || problem.predicates().is_empty()
        || problem.queries().next().is_none()
    {
        return false;
    }
    for clause in problem.clauses() {
        if !owner.open() || Instant::now() >= probe_deadline {
            return false;
        }
        if clause.body.predicates.len() > 1 {
            return false;
        }
    }
    // Existing syntactic graph analysis; no fresh theory classification or
    // rewrite of the original clauses/signatures is needed for eligibility.
    problem.has_cycles() && owner.open() && Instant::now() < probe_deadline
}

#[cfg(test)]
fn run_observed(
    problem: &ChcProblem,
    config: &PdrConfig,
    solve_deadline: Option<Instant>,
    search: &mut dyn FnMut(&ChcProblem, Duration, &PdrConfig) -> Option<Counterexample>,
    validate: &mut dyn FnMut(Counterexample, &PdrConfig, Option<Instant>) -> VerifiedChcResult,
    observe: &mut dyn FnMut(Phase),
) -> Option<VerifiedChcResult> {
    run_owned(
        problem,
        config,
        solve_deadline,
        &mut |original, budget, configured, _, _| search(original, budget, configured),
        validate,
        observe,
    )
}

fn run_owned(
    problem: &ChcProblem,
    config: &PdrConfig,
    solve_deadline: Option<Instant>,
    search: &mut dyn FnMut(
        &ChcProblem,
        Duration,
        &PdrConfig,
        &mut Owner,
        Instant,
    ) -> Option<Counterexample>,
    validate: &mut dyn FnMut(Counterexample, &PdrConfig, Option<Instant>) -> VerifiedChcResult,
    observe: &mut dyn FnMut(Phase),
) -> Option<VerifiedChcResult> {
    let mut owner = Owner::capture(config, solve_deadline);
    let _ambient_lane = owner.install_lane();
    let _memory = owner.memory().install();
    let _original = crate::smt::ScopedSolveDeadline::new(owner.deadline());
    let _smt = owner
        .deadline()
        .map(crate::smt::ScopedSmtDeadline::install_until);
    let result = (|| {
        if !owner.open() {
            return Some(unknown());
        }
        let probe_deadline = owner.probe_deadline()?;
        observe(Phase::Eligibility);
        if !owner.open() {
            return Some(unknown());
        }
        if !eligible(problem, config, &mut owner, probe_deadline) {
            return None;
        }
        observe(Phase::Search);
        if !owner.open() {
            return Some(unknown());
        }
        let budget = probe_deadline.saturating_duration_since(Instant::now());
        if budget < Duration::from_millis(250) {
            return None;
        }
        let configured = owner.configured(config);
        let candidate = {
            // This includes the helper's own fresh strict replay. Its relative
            // verifier timeout cannot replace either installed absolute clock.
            let _solve = crate::smt::ScopedSolveDeadline::new(Some(probe_deadline));
            let _smt = crate::smt::ScopedSmtDeadline::install_until(probe_deadline);
            search(problem, budget, &configured, &mut owner, probe_deadline)
        };
        if !owner.open() || Instant::now() >= probe_deadline {
            return None;
        }
        let candidate = candidate?;
        observe(Phase::Validation);
        if !owner.open() {
            return Some(unknown());
        }
        // Keep confirm_counterexample: it publishes what actually passed,
        // including any original witness substitution performed by validation.
        let result = validate(candidate, &configured, owner.deadline());
        observe(Phase::Validated);
        if !owner.open() {
            return Some(unknown());
        }
        let result =
            downgrade_unsafe_if_overapproximated(result, problem.has_stripped_body_forall());
        if !matches!(&result, VerifiedChcResult::Unsafe(_)) {
            return None;
        }
        observe(Phase::Publication);
        if !owner.open() {
            return Some(unknown());
        }
        Some(enforce_pdr_proof_return_boundary(
            result,
            &configured,
            owner.deadline(),
        ))
    })();
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
