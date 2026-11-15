// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Finite array observations propose Safe models, never original verdicts.
//! The existing constant-key scalarizer is a candidate generator only. A
//! complete, checked lift must pass the unchanged original-clause verifier.
//! No projected Unsafe or search-model validation flags cross this boundary.
//! Read-over-write semantics: SMT-LIB ArraysEx,
//! https://smt-lib.org/theories-ArraysEx.shtml (Tinelli, 2010; SMT-LIB 2.7).
//! The source verifier, not this abstraction, supplies proof.
//! Iterative admission limits opaque existing clone/rewrite work, not RSS or
//! hard cancellation latency. Only bounded static scalar hints are rebased;
//! other source-bound side channels decline unchanged.

use super::{
    array_projection::{control::Owner, untranslated_source_bound_channels},
    enforce_pdr_proof_return_boundary, validate_pdr_proof_result, ChcEngineResult, ChcProblem,
    InvariantModel, PdrConfig, PdrResult, PdrSolver, ValidationEvidence, VerifiedChcResult,
};
use ay_core::time::Instant;
use projection::Projection;

mod admission;
mod hints;
mod lift;
mod map;
mod projection;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Phase {
    HintAdmission,
    Projection,
    HintRebase,
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

/// None allows ordinary fallback; an observed caller stop is terminal Unknown.
pub(super) fn run(
    original: &ChcProblem,
    config: &PdrConfig,
    deadline: Option<Instant>,
) -> Option<VerifiedChcResult> {
    run_observed(
        original,
        config,
        deadline,
        &mut |reduced, configured| PdrSolver::solve_problem(reduced, configured),
        &mut |lifted, configured, until| {
            validate_pdr_proof_result(original, PdrResult::Safe(lifted), configured, until)
        },
        &mut |_| {},
    )
}

fn run_observed(
    original: &ChcProblem,
    config: &PdrConfig,
    deadline: Option<Instant>,
    search: &mut dyn FnMut(&ChcProblem, PdrConfig) -> PdrResult,
    validate: &mut dyn FnMut(InvariantModel, &PdrConfig, Option<Instant>) -> VerifiedChcResult,
    observe: &mut dyn FnMut(Phase),
) -> Option<VerifiedChcResult> {
    let mut owner = Owner::capture(config, deadline);
    let _ambient_lane = owner.install_lane();
    let _memory = owner.memory().install();
    let _original_clock = crate::smt::ScopedSolveDeadline::new(owner.deadline());
    let result = (|| {
        if !owner.open() {
            return Some(unknown());
        }
        // No source-position state is cleared to make this attempt applicable.
        if config.disable_array_scalarization || untranslated_source_bound_channels(config) {
            return None;
        }
        let probe = owner.probe_deadline()?;
        let (projected, rebased) =
            project_with_hints(original, config, probe, &mut owner, observe)?;
        observe(Phase::Search);
        if !owner.open() || Instant::now() >= probe {
            return None;
        }
        let mut configured = owner.search_config(config, probe);
        // Only the owned search copy changes. Original validation below
        // retains all original hints and signatures; hints remain candidates.
        configured.user_hints = rebased;
        configured.strict_proofs = true;
        configured.preserve_original_clauses = true;
        configured.disable_array_scalarization = true;
        if !owner.open() || Instant::now() >= probe {
            return None;
        }
        let raw = {
            let _solve = crate::smt::ScopedSolveDeadline::new(Some(probe));
            let _smt = crate::smt::ScopedSmtDeadline::install_until(probe);
            search(projected.reduced(), configured)
        };
        if !owner.open() || Instant::now() >= probe {
            return None;
        }
        let PdrResult::Safe(candidate) = raw else {
            return None;
        };
        observe(Phase::Lift);
        let lifted = projected.lift(&candidate, &mut || owner.open())?;
        drop(candidate);
        drop(projected);
        observe(Phase::Validation);
        if !owner.open() {
            return Some(unknown());
        }
        let configured = owner.validation_config(config);
        let verified = validate(lifted, &configured, owner.deadline());
        observe(Phase::Validated);
        if !owner.open() {
            return Some(unknown());
        }
        if !matches!(&verified, VerifiedChcResult::Safe(_)) {
            return None;
        }
        observe(Phase::Publication);
        if !owner.open() {
            return Some(unknown());
        }
        Some(enforce_pdr_proof_return_boundary(
            verified,
            &configured,
            owner.deadline(),
        ))
    })();
    // All temporary candidate owners drop before the terminal observation.
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

fn project_with_hints<'a>(
    original: &'a ChcProblem,
    config: &PdrConfig,
    probe: Instant,
    owner: &mut Owner,
    observe: &mut dyn FnMut(Phase),
) -> Option<(Projection<'a>, Vec<crate::LemmaHint>)> {
    observe(Phase::HintAdmission);
    let hints = hints::Admitted::new(&config.user_hints, &mut || {
        owner.open() && Instant::now() < probe
    })?;
    observe(Phase::Projection);
    let projected = Projection::new(original, &mut || owner.open() && Instant::now() < probe)?;
    observe(Phase::HintRebase);
    let rebased = hints.rebase(&projected, &mut || owner.open() && Instant::now() < probe)?;
    Some((projected, rebased))
}
