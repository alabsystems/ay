// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The whole-proof revert gate under the executor's stop controls.

use ay_core::Proof;
use ay_proof::ProofCheckError;

use super::meter::StrictCheckMeter;
use super::poll::strided_memory_poll;
use crate::executor::Executor;

/// Run the whole-proof REVERT GATE (`ay_proof::check_proof`) under the
/// executor's envelope.
///
/// #diagnostic-envelope — `Executor::split_euf_congruence_lemmas`,
/// `split_shadowed_store_equality_lemmas`, the rewritten-assertion bridge and
/// the congruence-explanation rebuild all use the same idiom: rebuild part of a
/// proof, re-check the WHOLE proof, and put the original back if the check
/// fails. On a triangular resolution proof that whole-proof re-check is the
/// dominant cost of the solve, and it ran with no meter and no cancellation
/// poll at all.
///
/// A refused/cancelled check returns `Err`, which is precisely the branch those
/// gates already take to discard their surgery and restore the original proof.
pub(in crate::executor) fn check_proof_gate_with_executor_progress(
    executor: &Executor,
    proof: &Proof,
) -> Result<(), ProofCheckError> {
    let should_stop = executor.make_strict_check_stop();
    check_proof_gate_under_controls(
        proof,
        &executor.ctx.terms,
        &should_stop,
        executor.memory_limit(),
    )
}

/// As [`check_proof_gate_with_executor_progress`], for the surgery passes that
/// already hold `&mut ctx.terms` and therefore cannot also borrow the executor.
/// The caller lifts the two controls out first (`make_strict_check_stop()`,
/// `memory_limit()`); both are owned values, so no borrow conflict remains.
///
/// #completed-check-accepted — the stop is polled when the walk is admitted
/// and at the checker's callbacks, never after it: a surgery whose re-check
/// validated every step is kept, not reverted because the deadline arrived
/// during the last step. (The admission poll is what stops a caller that is
/// already stopping: a proof of unmetered `ProofStep::Resolution` steps makes
/// no callback at all.)
pub(in crate::executor) fn check_proof_gate_under_controls(
    proof: &Proof,
    terms: &ay_core::TermStore,
    should_stop: &dyn Fn() -> bool,
    memory_limit: Option<usize>,
) -> Result<(), ProofCheckError> {
    let mut meter = StrictCheckMeter::production();
    let sampled_stop = strided_memory_poll(&should_stop, memory_limit);
    let outcome = {
        let mut progress = |work_delta: usize, byte_delta: usize| {
            meter.charge_while_running(
                work_delta,
                byte_delta,
                || sampled_stop.poll(),
                || "interrupt, solve deadline, or memory limit".to_string(),
                // A surgery gate reverts on a stop and publishes nothing.
                || None,
            )
        };
        if progress(0, 0) {
            ay_proof::check_proof_with_progress(proof, terms, &mut progress)
        } else {
            Err(ProofCheckError::ResourceLimit)
        }
    };
    meter.settle(outcome)
}
