// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Candidate construction only; the caller's unchanged original validator
//! still decides whether any ground/BMC witness can be published.

use super::{ChcProblem, Counterexample, Instant, Owner, PdrConfig};
use crate::ground_derivation::forward::ground_linear_refutation;
use std::time::Duration;

pub(super) fn original(
    problem: &ChcProblem,
    configured: &PdrConfig,
    owner: &mut Owner,
    probe: Instant,
) -> Option<Counterexample> {
    // Eight transitions are the existing replay helper's minimum initial
    // unrolling. This candidate lane does not widen that search depth.
    let result =
        ground_linear_refutation(problem, 8, &mut || owner.open() && Instant::now() < probe);
    if !owner.open() || Instant::now() >= probe {
        drop(result);
        let _ = owner.open();
        return None;
    }
    match result {
        Ok(Some(derivation)) => {
            return Some(Counterexample::new(Vec::new()).with_ground_derivation(derivation));
        }
        Err(crate::ground_derivation::GroundDerivationError::Interrupted) => return None,
        Ok(None) | Err(_) => {}
    }
    // Ground search and BMC share the cached probe, rather than each receiving
    // another four seconds. Both installed absolute scopes are still active.
    let remaining = probe.saturating_duration_since(Instant::now());
    if remaining < Duration::from_millis(250) || !owner.open() {
        return None;
    }
    crate::bmc::BmcSolver::replay_confirm_unsafe_on_problem(
        problem,
        0,
        remaining,
        configured.cancellation_token.clone(),
        configured.verbose,
    )
}
