// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Strict checking of borrowed, ALREADY prepared proof/context inputs.
//!
//! This component forwards the checker's actual offers to a caller sink, in
//! addition to the unchanged production meter and executor stop controls. It
//! does not prepare/copy declarations, signatures or authored premise scope,
//! price caller payload destruction, retain an owner, or execute a native solve.
//! A caller using OriginalAdmission must latch internal allocation/local-meter
//! ResourceLimit in its SAME WorkBudget before returning or retrying. Its later
//! cleanup/consumption fence is distinct from the completed document fact here.

use super::*;

/// The original callback is invoked only after the independent local ceiling
/// admits the offer, but always BEFORE checker work, including zero polls.
/// False (or a caught callback unwind) is sticky for this walk; no subsequent
/// offer invokes the sink again. No callback follows a completed last step.
pub(in crate::executor::proof::check) fn check_with_caller_progress(
    executor: &Executor,
    walk: StrictWalk<'_>,
    should_stop: &dyn Fn() -> bool,
    original_progress: &mut dyn FnMut(usize, usize) -> bool,
) -> (Result<ProofQuality, ProofCheckError>, usize) {
    run_with_meter(
        executor,
        walk,
        should_stop,
        original_progress,
        StrictCheckMeter::production(),
    )
}

fn run_with_meter(
    executor: &Executor,
    walk: StrictWalk<'_>,
    should_stop: &dyn Fn() -> bool,
    original_progress: &mut dyn FnMut(usize, usize) -> bool,
    mut meter: StrictCheckMeter,
) -> (Result<ProofQuality, ProofCheckError>, usize) {
    let stopped = strided_memory_poll(&should_stop, executor.memory_limit());
    let mut original_refused = false;
    let outcome = {
        let mut progress = |work_delta: usize, byte_delta: usize| {
            if original_refused {
                return false;
            }
            if !meter.charge_while_running(
                work_delta,
                byte_delta,
                || stopped.poll(),
                || describe_stop_signal(executor),
                || {
                    Some(
                        stopped
                            .reason()
                            .unwrap_or_else(|| typed_stop_signal(executor)),
                    )
                },
            ) {
                return false;
            }
            // Arm before user code: catching a callback panic cannot resume
            // this walk through a later permissive callback.
            original_refused = true;
            if !original_progress(work_delta, byte_delta) {
                return false;
            }
            original_refused = false;
            true
        };
        if progress(0, 0) {
            ay_proof::check_proof_strict_with_typed_context_and_progress(
                walk.proof,
                &executor.ctx.terms,
                walk.datatype_decls,
                walk.selector_decls,
                walk.datatype_member_signatures,
                walk.problem_assertions,
                &mut progress,
            )
        } else {
            Err(ProofCheckError::ResourceLimit)
        }
    };
    // Do not poll after validation. Historical completed proof facts keep
    // their meaning; an owning caller separately fences its later cleanup.
    record_walk_stop(executor, &meter);
    let outcome = if original_refused {
        Err(ProofCheckError::ResourceLimit)
    } else {
        meter.settle(outcome)
    };
    (outcome, meter.work())
}

#[cfg(all(test, feature = "proof-checker"))]
#[path = "caller/tests.rs"]
mod tests;
