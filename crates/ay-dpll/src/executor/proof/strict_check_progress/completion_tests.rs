// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! #completed-check-accepted: every metered wrapper honours the stop until the
//! checker's final step, and never after it.

use std::cell::Cell;

use super::tests::valid_empty_clause_proof;
use super::*;
use crate::api::proofs::EnvelopeStop;

/// #completed-check-accepted — one metered wrapper's whole stop contract.
///
/// `run` drives the wrapper under a stop control; `checker_callbacks` is how
/// many callbacks the UNWRAPPED checker makes on the same document, counted
/// independently of the wrapper. The wrapper must poll once to admit the walk
/// and otherwise only at the checker's callbacks, so nothing polls after the
/// final step. A stop raised after the last of them is therefore never
/// observed and the completed validation is accepted; a stop raised at the
/// last callback, mid-walk or before admission cancels (negative controls).
fn assert_stop_honoured_only_until_the_final_step(
    checker_callbacks: usize,
    run: impl Fn(&dyn Fn() -> bool) -> Result<(), ProofCheckError>,
) {
    assert!(
        checker_callbacks > 0,
        "the fixture must reach a metered validator"
    );
    let polls = Cell::new(0usize);
    let never = || {
        polls.set(polls.get() + 1);
        false
    };
    assert_eq!(run(&never), Ok(()), "the fixture is a valid refutation");
    let total = polls.get();
    assert_eq!(
        total,
        checker_callbacks + 1,
        "one admission poll, then only the checker's own callbacks: nothing may poll after the \
         final step"
    );
    for clear in [total, total - 1, total / 2, 0] {
        polls.set(0);
        // The deadline lands after exactly `clear` polls and stays expired.
        let stop = || {
            polls.set(polls.get() + 1);
            polls.get() > clear
        };
        let expected = if clear == total {
            Ok(())
        } else {
            Err(ProofCheckError::Cancelled)
        };
        assert_eq!(
            run(&stop),
            expected,
            "stop raised after {clear} of {total} polls"
        );
    }
}

fn assumed_terms(proof: &Proof) -> Vec<TermId> {
    proof
        .steps
        .iter()
        .filter_map(|step| match step {
            ay_core::ProofStep::Assume(term) => Some(*term),
            _ => None,
        })
        .collect()
}

#[test]
fn strict_walk_is_accepted_when_the_stop_follows_its_last_step() {
    let mut executor = Executor::new();
    let proof = valid_empty_clause_proof(&mut executor);
    let problem = assumed_terms(&proof);
    let mut checker_callbacks = 0;
    ay_proof::check_proof_strict_with_typed_context_and_progress(
        &proof,
        &executor.ctx.terms,
        None,
        None,
        &[],
        Some(&problem),
        &mut |_, _| {
            checker_callbacks += 1;
            true
        },
    )
    .expect("the fixture is a valid strict refutation");
    assert_stop_honoured_only_until_the_final_step(checker_callbacks, |should_stop| {
        let walk = StrictWalk {
            proof: &proof,
            datatype_decls: None,
            selector_decls: None,
            datatype_member_signatures: &[],
            problem_assertions: Some(&problem),
        };
        check_strict_under_controls(&executor, walk, should_stop)
            .0
            .map(|_| ())
    });
}

#[test]
fn diagnostic_walk_is_accepted_when_the_stop_follows_its_last_step() {
    let mut executor = Executor::new();
    let proof = valid_empty_clause_proof(&mut executor);
    for want_quality in [WantQuality::No, WantQuality::Yes] {
        let mut checker_callbacks = 0;
        let mut count = |_: usize, _: usize| {
            checker_callbacks += 1;
            true
        };
        let error = match want_quality {
            WantQuality::No => {
                ay_proof::check_proof_partial_with_progress(&proof, &executor.ctx.terms, &mut count)
                    .1
            }
            WantQuality::Yes => {
                ay_proof::check_proof_partial_with_quality_and_progress(
                    &proof,
                    &executor.ctx.terms,
                    &mut count,
                )
                .2
            }
        };
        assert_eq!(error, None);
        assert_stop_honoured_only_until_the_final_step(checker_callbacks, |should_stop| {
            let outcome = check_partial_under_controls(
                &executor,
                &proof,
                want_quality,
                StrictCheckMeter::production(),
                should_stop,
            );
            match outcome.error {
                None => {
                    assert_eq!(outcome.quality.is_some(), want_quality == WantQuality::Yes);
                    Ok(())
                }
                Some(error) => {
                    assert!(outcome.quality.is_none());
                    Err(error)
                }
            }
        });
    }
}

#[test]
fn proof_revert_gate_keeps_a_walk_the_stop_follows() {
    let mut executor = Executor::new();
    let proof = valid_empty_clause_proof(&mut executor);
    let mut checker_callbacks = 0;
    ay_proof::check_proof_with_progress(&proof, &executor.ctx.terms, &mut |_, _| {
        checker_callbacks += 1;
        true
    })
    .expect("the fixture is a valid refutation");
    assert_stop_honoured_only_until_the_final_step(checker_callbacks, |should_stop| {
        check_proof_gate_under_controls(&proof, &executor.ctx.terms, should_stop, None)
    });
}

/// #completed-check-accepted — what a returned walk's verdict becomes. A
/// refusal the walk observed stays final under both limbs, including behind
/// an `Ok` (a validator that swallowed it), while a walk that observed no
/// refusal keeps its own verdict, error or acceptance, unchanged.
#[test]
fn settle_keeps_observed_refusals_final_and_nothing_else() {
    let genuine = ProofCheckError::NoClauseProducingSteps;
    let mut meter = StrictCheckMeter::with_limits(1, 1);
    assert_eq!(meter.settle(Ok(7)), Ok(7));
    assert_eq!(
        meter.settle::<()>(Err(genuine.clone())),
        Err(genuine.clone())
    );

    assert!(!meter.charge_while_running(2, 0, || false, String::new, || None));
    assert_eq!(meter.refusal, Some(StrictCheckRefusal::BudgetRefused));
    assert_eq!(meter.settle(Ok(7)), Err(ProofCheckError::ResourceLimit));
    assert_eq!(
        meter.settle::<()>(Err(ProofCheckError::ResourceLimit)),
        Err(ProofCheckError::ResourceLimit)
    );
    assert_eq!(
        meter.settle::<()>(Err(genuine.clone())),
        Err(genuine.clone())
    );

    let mut meter = StrictCheckMeter::production();
    assert!(!meter.charge_while_running(
        0,
        0,
        || true,
        String::new,
        || Some(EnvelopeStop::Interrupt)
    ));
    assert_eq!(meter.refusal, Some(StrictCheckRefusal::Cancelled));
    assert_eq!(meter.stop, Some(EnvelopeStop::Interrupt));
    assert_eq!(meter.settle(Ok(7)), Err(ProofCheckError::Cancelled));
    assert_eq!(
        meter.settle::<()>(Err(ProofCheckError::ResourceLimit)),
        Err(ProofCheckError::Cancelled)
    );
    assert_eq!(meter.settle::<()>(Err(genuine.clone())), Err(genuine));
}

/// T-c, the walk's `Cancelled` limb: a stop the walk observed is recorded as
/// a TYPED stop on the executor at the moment it was seen, so publication can
/// report it after the signal has cleared (RSS that fell back), instead of
/// reading the cancelled walk as a rejection.
#[test]
fn a_cancelled_walk_keeps_its_typed_stop_after_the_signal_clears() {
    let mut executor = Executor::new();
    let proof = valid_empty_clause_proof(&mut executor);
    let problem = assumed_terms(&proof);
    let walk = StrictWalk {
        proof: &proof,
        datatype_decls: None,
        selector_decls: None,
        datatype_member_signatures: &[],
        problem_assertions: Some(&problem),
    };
    // Memory is observed at the walk's admission poll; the force is lowered
    // as soon as the walk returns, as RSS would fall.
    ay_sys::force_process_memory_exceeded_for_testing(true);
    let outcome = check_strict_under_controls(&executor, walk, &|| false).0;
    ay_sys::force_process_memory_exceeded_for_testing(false);
    assert_eq!(outcome, Err(ProofCheckError::Cancelled));
    assert_eq!(
        executor.certification_stop.get(),
        Some(EnvelopeStop::ProcessMemory)
    );

    let fresh = Executor::new();
    let diagnostic = check_partial_under_controls(
        &fresh,
        &proof,
        WantQuality::No,
        StrictCheckMeter::production(),
        &|| true,
    );
    assert_eq!(diagnostic.error, Some(ProofCheckError::Cancelled));
    assert_eq!(
        fresh.certification_stop.get(),
        Some(EnvelopeStop::Caller),
        "an opaque stop must not invent a memory-breach cause"
    );
    assert!(
        Executor::new().certification_stop.get().is_none(),
        "a walk that was never stopped records nothing"
    );
}
