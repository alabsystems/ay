// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

#[test]
fn final_admission_checks_the_original_deadline_after_the_caller_poll() {
    let mut calls = 0;
    let expired = admit_success(Instant::now(), &mut || {
        calls += 1;
        Ok(())
    });
    assert_eq!(calls, 1);
    // The hang guard stops the attempt; it is not a verdict, so it is never
    // `Rejected` (the one failure the checker may remember).
    assert_eq!(
        expired,
        Err(Failure::Stopped(format!(
            "surfaced bit-blast refutation failed replay: {}",
            BvBlastValidateError::DeadlineExceeded
        )))
    );
    assert_eq!(
        admit_success(Instant::now(), &mut || Err(ProofCheckError::ResourceLimit)),
        Err(Failure::Cancelled)
    );
    assert_eq!(admit_success(deadline(), &mut || Ok(())), Ok(()));
}

/// Only a rejection that ended before the hang guard is the counted
/// envelope's; one that ended at or after it may have been the guard's, so it
/// is re-labelled a stop. Every other outcome passes through unchanged.
#[test]
fn a_rejection_at_the_hang_guard_is_a_stop_not_a_verdict() {
    let reason = || "proof resource `resolution conflicts` exceeds limit 1 (actual 2)".to_owned();
    assert_eq!(
        stopped_by_hang_guard(Err(Failure::Rejected(reason())), deadline()),
        Err(Failure::Rejected(reason()))
    );
    assert_eq!(
        stopped_by_hang_guard(Err(Failure::Rejected(reason())), Instant::now()),
        Err(Failure::Stopped(reason()))
    );
    for passed in [
        Ok(()),
        Err(Failure::Cancelled),
        Err(Failure::Stopped(reason())),
    ] {
        assert_eq!(
            stopped_by_hang_guard(passed.clone(), Instant::now()),
            passed
        );
    }
}

/// The verdict is the counted caps', not the clock's. A caller poll that
/// stalls past the retired three-second deadline stands in for a validation
/// thread descheduled under contention: the valid lemma is still accepted.
/// With the deadline, lowering resumed after the stall into
/// `proof-producing lowering deadline exceeded` and rejected the lemma.
#[test]
fn a_stall_past_the_retired_deadline_does_not_reject_a_valid_lemma() {
    let (terms, root, _) = raw_identity();
    let mut polls = 0;
    let result = validate(&terms, &[root], &mut || {
        polls += 1;
        // The first poll precedes the envelope; the second is inside lowering.
        if polls == 2 {
            std::thread::sleep(Duration::from_millis(3_100));
        }
        Ok(())
    });
    assert!(polls > 2);
    assert_eq!(result, Ok(()));
}

#[test]
fn refusal_inside_the_fallback_is_terminal_and_cannot_publish_a_memo() {
    let (terms, root, _) = raw_identity();
    let mut fallback_calls = 0;
    let mut calls = 0;
    let mut stop = usize::MAX;
    let result = semantic_control::run(
        &mut |_, _| {
            calls += 1;
            calls != stop
        },
        |poll| {
            validate_bv_bitblast_semantics_with_fallback(
                &terms,
                ProofId(0),
                &[root],
                poll,
                |poll| {
                    fallback_calls += 1;
                    // A downstream typed refusal must not become a combined schema
                    // error even if a later caller poll would accept again.
                    poll().map_err(|_| Failure::Cancelled)?;
                    Err(Failure::Cancelled)
                },
            )
        },
    );
    assert_eq!(result, Err(ProofCheckError::ResourceLimit));
    assert_eq!(fallback_calls, 1);
    assert!(!terms.strict_bv_semantics_validated(&[root]));
    // Target the actual shared fallback poll rather than an outer wrapper.
    stop = calls;
    calls = 0;
    let result = semantic_control::run(
        &mut |_, _| {
            calls += 1;
            calls != stop
        },
        |poll| {
            validate_bv_bitblast_semantics_with_fallback(
                &terms,
                ProofId(0),
                &[root],
                poll,
                |poll| poll().map_err(|_| Failure::Cancelled),
            )
        },
    );
    assert_eq!(result, Err(ProofCheckError::ResourceLimit));
    assert_eq!(calls, stop);
    assert!(!terms.strict_bv_semantics_validated(&[root]));
}

#[test]
fn fallback_precancel_precedes_schema_and_never_starts_a_solver() {
    let (terms, root, _) = raw_identity();
    for clause in [vec![], vec![root]] {
        let mut calls = 0;
        assert_eq!(
            validate(&terms, &clause, &mut || {
                calls += 1;
                Err(ProofCheckError::ResourceLimit)
            }),
            Err(Failure::Cancelled)
        );
        assert_eq!(calls, 1);
    }
}

#[test]
fn real_fallback_proves_and_replays_the_identity_and_rejects_a_false_claim() {
    let (mut terms, root, _) = raw_identity();
    assert!(bv_bitblast_requires_proof_producer(&terms, &[root]));
    validate_bv_bitblast_with_progress(&terms, ProofId(0), &[root], None, &mut |_, _| true)
        .unwrap();
    assert!(terms.strict_bv_semantics_validated(&[root]));
    let x = terms.mk_var("false-wide", Sort::bitvec(9));
    let zero = terms.mk_bitvec(0.into(), 9);
    let false_claim = terms.mk_app(Symbol::named("="), [x, zero], Sort::Bool);
    assert!(matches!(
        validate_bv_bitblast_with_progress(
            &terms,
            ProofId(1),
            &[false_claim],
            None,
            &mut |_, _| true
        ),
        Err(ProofCheckError::InvalidTheoryLemma { .. })
    ));
    assert!(!terms.strict_bv_semantics_validated(&[false_claim]));
}
