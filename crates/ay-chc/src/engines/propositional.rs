// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Attempt-local progress for the original-clause ground-refutation prepass.
//! Polls bracket opaque evaluation, validation and cleanup; they are not a
//! hard cancellation-latency or process-memory guarantee.

use super::*;
use crate::bmc::memory::Budget;
use crate::ground_derivation::propositional::ground_nullary_refutation;
use ay_core::time::Instant;

struct Owner {
    deadline: Option<Instant>,
    cancellation: Option<CancellationToken>,
    memory: Budget,
    stopped: bool,
}

impl Owner {
    fn capture(config: &PdrConfig, solve_deadline: Option<Instant>) -> Self {
        let mut cancellation = config
            .cancellation_token
            .as_ref()
            .map(CancellationToken::sticky_child);
        if let Some(external) = &config.external_cancellation_token {
            let external = external.sticky_child();
            if let Some(cancellation) = &mut cancellation {
                cancellation.link_upstream(&external);
            } else {
                cancellation = Some(external);
            }
        }
        Self {
            deadline: [
                solve_deadline,
                crate::smt::current_thread_solve_deadline(),
                crate::smt::deadline::current_smt_deadline(),
            ]
            .into_iter()
            .flatten()
            .min(),
            cancellation,
            memory: Budget::capture(None, None),
            stopped: false,
        }
    }

    fn open(&mut self) -> bool {
        self.open_at(Instant::now())
    }

    fn open_at(&mut self, now: Instant) -> bool {
        self.stopped |= self
            .cancellation
            .as_ref()
            .is_some_and(CancellationToken::is_cancelled)
            || self.deadline.is_some_and(|deadline| now >= deadline)
            || !self.memory.open()
            || !Budget::capture(None, None).open();
        !self.stopped
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Phase {
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

/// None alone permits ordinary search fallback. A stopped attempt returns
/// Some(Unknown), so recovery of a token or memory reading cannot restart it.
pub(super) fn run(
    problem: &ChcProblem,
    config: &PdrConfig,
    solve_deadline: Option<Instant>,
) -> Option<VerifiedChcResult> {
    run_observed(problem, config, solve_deadline, &mut |_| {})
}

fn run_observed(
    problem: &ChcProblem,
    config: &PdrConfig,
    solve_deadline: Option<Instant>,
    observe: &mut dyn FnMut(Phase),
) -> Option<VerifiedChcResult> {
    let mut owner = Owner::capture(config, solve_deadline);
    let _memory = owner.memory.install();
    // Under an effort a validated refutation is the count's: a stop observed
    // after validation (a backstop clock, a cancel) does not discard it, as at
    // `enforce_pdr_proof_return_boundary` (P4a slice 8). A stop during the
    // search or the validation still ends the attempt.
    let keep_decided = config.effort.is_some();
    let result = (|| {
        observe(Phase::Search);
        if !owner.open() {
            return Some(unknown());
        }
        let derivation = match ground_nullary_refutation(problem, &mut || owner.open()) {
            Ok(derivation) => derivation?,
            Err(_) => {
                // In particular, Interrupted must never become missing evidence
                // followed by another engine. Keep the stop sticky through cleanup.
                owner.stopped = true;
                return Some(unknown());
            }
        };
        observe(Phase::Validation);
        if !owner.open() {
            return Some(unknown());
        }
        let candidate = Counterexample::new(Vec::new()).with_ground_derivation(derivation);
        // The existing validator inherits its primary token. Bind both caller
        // channels to that same attempt-local observation, so even a stop seen
        // inside validation survives a later reset of the original parent.
        let mut owned_config = config.clone();
        owned_config.cancellation_token = owner.cancellation.clone();
        if !owner.open() {
            return Some(unknown());
        }
        // Preserve the exact original-source validator, not a producer shortcut.
        let result = validate_pdr_proof_result(
            problem,
            PdrResult::Unsafe(candidate),
            &owned_config,
            solve_deadline,
        );
        observe(Phase::Validated);
        if !keep_decided && !owner.open() {
            return Some(unknown());
        }
        let result =
            downgrade_unsafe_if_overapproximated(result, problem.has_stripped_body_forall());
        if !matches!(result, VerifiedChcResult::Unsafe(_)) {
            return None;
        }
        observe(Phase::Publication);
        if !keep_decided && !owner.open() {
            return Some(unknown());
        }
        Some(enforce_pdr_proof_return_boundary(
            result,
            config,
            solve_deadline,
        ))
    })();
    observe(Phase::Cleanup);
    let decided = matches!(result, Some(VerifiedChcResult::Unsafe(_)));
    if (keep_decided && decided) || owner.open() {
        result
    } else {
        Some(unknown())
    }
}

#[cfg(test)]
mod tests;
