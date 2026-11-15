// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Strict original-source admission before datatype-expanding solver setup.

use crate::ground_derivation::compact::{CompactEvidence, Error, Owner};
use crate::{CancellationToken, ChcEngineResult, ChcProblem, Counterexample};
use ay_core::time::Instant;

#[cfg(test)]
mod tests;

/// None is inapplicability, never Safe. An observed control refusal is terminal.
pub(crate) fn run(
    problem: &ChcProblem,
    deadline: Option<Instant>,
    cancellation: Option<&CancellationToken>,
    memory: Option<usize>,
) -> Option<ChcEngineResult> {
    // Inapplicability is decided before any control is captured or polled: a
    // source without datatypes never enters this route, so an already-stopped
    // caller is observed (and reported) by the caller's own ordinary pipeline
    // rather than ended here as this route's terminal Unknown.
    if problem.datatype_defs().is_empty() {
        return None;
    }
    let memory = crate::bmc::memory::Budget::capture(memory, None);
    let _memory = memory.install();
    let _deadline = deadline.map(crate::smt::deadline::ScopedSmtDeadline::install_until);
    let token = linked_cancellation(cancellation);
    let _lane = token.as_ref().map(|token| {
        crate::smt::deadline::ScopedLaneCancellation::install(
            token.clone(),
            crate::smt::deadline::lane_interrupt_flag(),
        )
    });
    let mut owner = match Owner::capture() {
        Ok(owner) => owner,
        Err(_) => return Some(ChcEngineResult::Unknown),
    };
    let _owner_scope = owner.enter();
    match super::derive(problem, &mut owner) {
        Ok(Some(derivation)) => {
            // Independent native replay remains the acceptance anchor. Carry
            // the same owner into every later export/check; no cached boolean.
            if crate::ground_derivation::compact::validate(problem, &derivation, &mut owner)
                .is_err()
            {
                return Some(ChcEngineResult::Unknown);
            }
            let evidence = CompactEvidence::new(derivation, owner);
            Some(ChcEngineResult::Unsafe(
                Counterexample::new(Vec::new()).with_compact_ground_derivation(evidence),
            ))
        }
        Ok(None) | Err(Error::Unsupported | Error::InvalidValue | Error::InvalidDerivation) => {
            if owner.poll().is_ok() {
                None
            } else {
                Some(ChcEngineResult::Unknown)
            }
        }
        Err(Error::Stopped | Error::Resource | Error::InvalidSource) => {
            Some(ChcEngineResult::Unknown)
        }
    }
}

/// Recheck the complete candidate against this caller's ORIGINAL clauses.
/// Extra caller controls can only tighten the retained solve owner.
pub(crate) fn confirm(
    problem: &ChcProblem,
    candidate: &Counterexample,
    deadline: Option<Instant>,
    cancellation: Option<&CancellationToken>,
    memory: Option<usize>,
) -> Option<Counterexample> {
    let evidence = candidate.compact_evidence()?;
    let current = ay_core::resource::current_check_stop().ok()?;
    let guard = ay_core::resource::current_guard();
    let deadline = [deadline, crate::smt::deadline::effective_thread_deadline()]
        .into_iter()
        .flatten()
        .min();
    let interrupt = crate::smt::deadline::lane_interrupt_flag();
    let memory = crate::bmc::memory::Budget::capture(memory, None);
    let _memory = memory.install();
    let _deadline = deadline.map(crate::smt::deadline::ScopedSmtDeadline::install_until);
    let token = linked_cancellation(cancellation);
    let mut allowed = || {
        memory.open()
            && deadline.is_none_or(|end| Instant::now() < end)
            && token.as_ref().is_none_or(|token| !token.is_cancelled())
            && interrupt
                .as_ref()
                .is_none_or(|flag| !flag.load(std::sync::atomic::Ordering::Acquire))
            && guard.as_ref().is_none_or(|guard| guard.poll().is_none())
            && current.as_ref().is_none_or(|callback| !callback())
    };
    let retained = evidence.owner();
    let mut owner = retained.with_progress(&mut allowed);
    crate::ground_derivation::compact::validate(problem, evidence.derivation(), &mut owner).ok()?;
    owner.admit(1, 256).ok()?;
    // Legacy i64 state views cannot faithfully present complete datatype DAGs.
    // Preserve the checked artifact, never copy an unrelated placeholder trace.
    let mut confirmed = Counterexample::new(Vec::new());
    confirmed.compact_derivation = candidate.compact_derivation.clone();
    owner.poll().ok()?;
    Some(confirmed)
}

fn linked_cancellation(supplied: Option<&CancellationToken>) -> Option<CancellationToken> {
    let ambient = crate::smt::deadline::current_lane_token();
    match (supplied, ambient) {
        (Some(supplied), ambient) => {
            let mut token = supplied.sticky_child();
            if let Some(ambient) = ambient {
                token.link_upstream(&ambient);
            }
            Some(token)
        }
        (None, ambient) => ambient.map(|token| token.sticky_child()),
    }
}
