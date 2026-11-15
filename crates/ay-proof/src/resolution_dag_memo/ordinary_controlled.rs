// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Ordinary (inprocessing-on) proof memo with cancellation-only observation.

use super::*;
use ay_sat::{prove_unsat_resolution_dag_with_cancellation, ResolutionDagCancellationError};

#[cfg(test)]
mod tests;

fn observe(callback: &mut dyn FnMut() -> bool) -> Result<(), ResolutionDagCancellationError> {
    if callback() {
        Ok(())
    } else {
        Err(ResolutionDagCancellationError::Cancelled)
    }
}

/// The ordinary producer and exact ordinary memo key, with a borrowed stop.
///
/// The callback is sticky across key/hit copies, both ordinary SAT attempts,
/// retention and final admission. No bounded proof posture or new resource
/// policy is selected. It shares certificates with the compatibility entry
/// point because the actual producer's algorithm and complete input are the
/// same; it cannot consume a bounded or strategy-tagged memo entry.
///
/// Individual key/value copies and retention accounting remain opaque and
/// unpriced. A newly produced refutation may already be retained when a
/// post-retention observer refuses this caller; it is still a certificate
/// for this exact CNF, not a cancellation verdict or permission to publish.
/// Every returned success, including a memo hit, requires a final observation.
///
/// # Errors
/// Exactly [`ay_sat::prove_unsat_resolution_dag_with_cancellation`]'s errors.
/// A cancelled child is never stored; no error or refusal verdict is memoized.
pub fn prove_unsat_resolution_dag_with_cancellation_memoized(
    num_vars: usize,
    clauses: &[Vec<Literal>],
    keep_going: &mut dyn FnMut() -> bool,
) -> Result<ResolutionDag, ResolutionDagCancellationError> {
    // Latch before calling foreign code, including a callback panic that the
    // ordinary solver might catch. Never create a fresh accepting retry owner.
    let mut stopped = false;
    let mut sticky = || {
        if stopped {
            return false;
        }
        stopped = true;
        let accepted = keep_going();
        stopped = !accepted;
        accepted
    };
    observe(&mut sticky)?;
    if memo_disabled() {
        return prove_unsat_resolution_dag_with_cancellation(num_vars, clauses, &mut sticky);
    }
    let key = MemoKey {
        num_vars,
        clauses: clauses.to_vec(),
        limits: None,
        strategy: None,
    };
    observe(&mut sticky)?;
    let hit = lookup(&key);
    observe(&mut sticky)?;
    if let Some(dag) = hit {
        return Ok(dag);
    }
    let dag = prove_unsat_resolution_dag_with_cancellation(num_vars, clauses, &mut sticky)?;
    observe(&mut sticky)?;
    store(key, &dag);
    observe(&mut sticky)?;
    Ok(dag)
}
