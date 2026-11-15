// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Fair, bounded-work dovetailing of original-source candidates and SAT retries.
//! Scheduling gives no verdict authority; only a complete native SAT probe can
//! produce a counterexample. Retiring an UNSAT candidate never establishes Safe.
//! Slices are metered in the searching thread's CPU time (see `clock`).

use std::sync::Arc;
use std::time::Duration;

use ay_core::time::Instant;

use super::replay::Probe;
use super::{derivation, render, replay, search_trees, CancellationToken, Derivation};
use super::{QuantifiedChcCounterexample, QuantifiedChcProblem, SourceControl};

mod clock;
mod policy;

struct Prepared {
    derivation: Derivation,
    obligation: String,
    topology: [u8; 32],
}

enum Discovery<C> {
    Pending,
    Candidate(C),
    Exhausted,
}

pub(super) fn run(
    problem: &QuantifiedChcProblem,
    deadline: Instant,
    memory: Option<usize>,
    cancellation: &CancellationToken,
) -> Option<QuantifiedChcCounterexample> {
    let control = SourceControl::new(deadline, cancellation);
    let clock = clock::SearchClock::start();
    // Drop the generator, pending candidates and all parsing/solver scratch
    // before final source-copy admission. No failed retry clones its script.
    let result = {
        let mut search = search_trees::Search::new(problem, &control)?;
        policy::explore(
            deadline,
            &control,
            || clock.now(),
            || match search.step(&control)? {
                search_trees::Step::Pending => Some(Discovery::Pending),
                search_trees::Step::Exhausted => Some(Discovery::Exhausted),
                search_trees::Step::Candidate(derivation) => prepare(problem, derivation, &control),
            },
            |candidate: &Prepared, child_deadline| {
                replay::probe(
                    &candidate.obligation,
                    clock.budget(child_deadline, deadline),
                    memory,
                    cancellation,
                    &control,
                )
            },
        )
    };
    control.poll()?;
    let candidate = result?;
    control.bytes(problem.source_smtlib().len())?;
    let source = Arc::from(problem.source_smtlib());
    control.poll()?;
    Some(QuantifiedChcCounterexample {
        source,
        clause_indices: candidate.derivation.clause_indices,
        premise_steps: candidate.derivation.premise_steps,
        topology_sha256: candidate.topology,
        obligation: candidate.obligation,
        memory_budget: memory,
    })
}

fn prepare(
    problem: &QuantifiedChcProblem,
    derivation: Derivation,
    control: &SourceControl<'_>,
) -> Option<Discovery<Prepared>> {
    let obligation = match render::render_derivation(
        problem,
        &derivation.clause_indices,
        &derivation.premise_steps,
        control,
    ) {
        Ok(obligation) => obligation,
        Err(_) => {
            // A structurally unrenderable candidate proves nothing. A terminal
            // shared refusal must not be hidden by trying another candidate.
            control.poll()?;
            return Some(Discovery::Pending);
        }
    };
    let topology = derivation::fingerprint(
        &derivation.clause_indices,
        &derivation.premise_steps,
        control,
    )?;
    Some(Discovery::Candidate(Prepared {
        derivation,
        obligation,
        topology,
    }))
}

/// Advice only chooses a candidate. Acquisition and canonical original pinned
/// replay must finish within the ORIGINAL owner after the search slice drops.
pub(super) fn run_complete(
    problem: &QuantifiedChcProblem,
    search_deadline: Instant,
    deadline: Instant,
    memory: Option<usize>,
    cancellation: &CancellationToken,
    control: &SourceControl<'_>,
) -> Option<super::QuantifiedChcCompleteTrace> {
    let result = {
        let _search_scope = crate::smt::ScopedSmtDeadline::install_until(search_deadline);
        let clock = clock::SearchClock::start();
        let mut search = search_trees::Search::new(problem, control)?;
        policy::explore(
            search_deadline,
            control,
            || clock.now(),
            || match search.step(control)? {
                search_trees::Step::Pending => Some(Discovery::Pending),
                search_trees::Step::Exhausted => Some(Discovery::Exhausted),
                search_trees::Step::Candidate(derivation) => {
                    prepare_advice(problem, derivation, control)
                }
            },
            |candidate: &Prepared, child_deadline| {
                replay::probe(
                    &candidate.obligation,
                    clock.budget(child_deadline, search_deadline),
                    memory,
                    cancellation,
                    control,
                )
            },
        )
    };
    // Local search TLS deadline and all candidate-generator scratch are gone.
    control.poll()?;
    let candidate = result?;
    drop(candidate.obligation);
    super::QuantifiedChcCompleteTrace::from_discovery(
        problem,
        candidate.derivation,
        candidate.topology,
        deadline,
        memory,
        cancellation,
        control,
    )
}

fn prepare_advice(
    problem: &QuantifiedChcProblem,
    derivation: Derivation,
    control: &SourceControl<'_>,
) -> Option<Discovery<Prepared>> {
    let obligation = match render::render_advice(
        problem,
        &derivation.clause_indices,
        &derivation.premise_steps,
        control,
    ) {
        Ok(obligation) => obligation,
        Err(_) => {
            control.poll()?;
            return Some(Discovery::Pending);
        }
    };
    let topology = derivation::fingerprint(
        &derivation.clause_indices,
        &derivation.premise_steps,
        control,
    )?;
    Some(Discovery::Candidate(Prepared {
        derivation,
        obligation,
        topology,
    }))
}
