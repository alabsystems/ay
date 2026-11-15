// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![cfg(test)]

use std::cell::Cell;
use std::panic::{catch_unwind, AssertUnwindSafe};

use ay_core::AletheRule;

use super::*;

mod fixtures;
mod oracle;

use fixtures::{contradiction, datatype, skolem};

fn assert_same(
    expected: Result<BundleReCheck, ProofCheckError>,
    actual: Result<BundleReCheck, ProofCheckError>,
) {
    match (expected, actual) {
        (Ok(expected), Ok(actual)) => {
            assert_eq!(actual.quality, expected.quality);
            assert_eq!(actual.assume_terms, expected.assume_terms);
        }
        (Err(expected), Err(actual)) => assert_eq!(actual, expected),
        (expected, actual) => panic!("reader mismatch: {expected:?} versus {actual:?}"),
    }
}

#[test]
fn always_continue_matches_old_reader_for_real_boolean_datatype_and_skolem_proofs() {
    for bundle in [
        contradiction(false),
        contradiction(true),
        datatype(),
        skolem(),
    ] {
        let before = serde_json::to_vec(&bundle).unwrap();
        let expected = oracle::recheck(&bundle);
        assert!(
            expected.is_ok(),
            "fixture must genuinely prove contradiction"
        );
        assert_same(
            expected,
            re_check_bundle_strict_with_cancellation(&bundle, &mut || true),
        );
        assert_same(oracle::recheck(&bundle), re_check_bundle_strict(&bundle));
        assert_eq!(serde_json::to_vec(&bundle).unwrap(), before);
    }
}

#[test]
fn assumptions_retain_order_and_duplicate_slots() {
    let bundle = contradiction(true);
    let positive = bundle.obligation_assertions[0];
    let negative = bundle.obligation_assertions[1];
    let result = re_check_bundle_strict_with_cancellation(&bundle, &mut || true).unwrap();
    assert_eq!(
        result.assume_terms,
        [positive, positive, negative, positive]
    );
    assert_eq!(result.quality.assume_count, 4);
}

#[test]
fn every_checkpoint_refusal_is_sticky_and_allows_only_a_fresh_attempt_to_retry() {
    for bundle in [contradiction(false), datatype(), skolem()] {
        let before = serde_json::to_vec(&bundle).unwrap();
        let mut total = 0;
        re_check_bundle_strict_with_cancellation(&bundle, &mut || {
            total += 1;
            true
        })
        .unwrap();
        assert!(total > bundle.steps.len() + bundle.term_entries.len());
        for stop in 1..=total {
            let mut calls = 0;
            let result = re_check_bundle_strict_with_cancellation(&bundle, &mut || {
                calls += 1;
                calls != stop
            });
            assert!(
                matches!(result, Err(ProofCheckError::ResourceLimit)),
                "{stop}"
            );
            assert_eq!(calls, stop, "no retry after a transient false");
        }
        assert_eq!(serde_json::to_vec(&bundle).unwrap(), before);
        assert_same(
            oracle::recheck(&bundle),
            re_check_bundle_strict_with_cancellation(&bundle, &mut || true),
        );
    }
}

#[test]
fn last_checkpoint_refusal_prevents_success_publication() {
    let bundle = contradiction(true);
    let mut total = 0;
    re_check_bundle_strict_with_cancellation(&bundle, &mut || {
        total += 1;
        true
    })
    .unwrap();
    let mut remaining = total;
    let result = re_check_bundle_strict_with_cancellation(&bundle, &mut || {
        remaining -= 1;
        remaining != 0
    });
    assert!(matches!(result, Err(ProofCheckError::ResourceLimit)));
    assert_eq!(remaining, 0);
}

#[test]
fn malformed_source_and_proof_errors_preserve_old_reason_when_live() {
    let base = contradiction(false);
    let mut bad_schema = base.clone();
    bad_schema.schema = "not-a-proof-bundle".repeat(10);
    let mut missing_root = base.clone();
    missing_root.steps[0] = ProofStep::Assume(TermId::SENTINEL);
    let mut bad_sort = base.clone();
    bad_sort.term_entries[base.obligation_assertions[0].index()].1 = Sort::Int;
    let mut unauthorized = base.clone();
    unauthorized.obligation_assertions = vec![base.true_term.unwrap()];
    let mut missing_terminal = base.clone();
    missing_terminal.steps.pop();
    let mut bad_premise = base.clone();
    let ProofStep::Resolution { clause1, .. } = bad_premise.steps.last_mut().unwrap() else {
        panic!("resolution fixture")
    };
    *clause1 = ProofId(u32::MAX);
    for bundle in [
        bad_schema,
        missing_root,
        bad_sort,
        unauthorized,
        missing_terminal,
        bad_premise,
    ] {
        let expected = oracle::recheck(&bundle);
        assert!(expected.is_err());
        assert_same(
            expected,
            re_check_bundle_strict_with_cancellation(&bundle, &mut || true),
        );
    }
}

#[test]
fn precancel_wins_before_schema_missing_ids_or_empty_proof() {
    let base = contradiction(false);
    let mut schema = base.clone();
    schema.schema.clear();
    let mut missing = base.clone();
    missing.true_term = Some(TermId::SENTINEL);
    let mut empty = base.clone();
    empty.steps.clear();
    for bundle in [base, schema, missing, empty] {
        let before = serde_json::to_vec(&bundle).unwrap();
        let mut calls = 0;
        let result = re_check_bundle_strict_with_cancellation(&bundle, &mut || {
            calls += 1;
            false
        });
        assert!(matches!(result, Err(ProofCheckError::ResourceLimit)));
        assert_eq!(calls, 1);
        assert_eq!(serde_json::to_vec(&bundle).unwrap(), before);
    }
}

#[test]
fn trust_and_hole_stay_rejected_without_a_fallback_lane() {
    for rule in [AletheRule::Trust, AletheRule::Hole] {
        let mut bundle = contradiction(false);
        bundle.steps.push(ProofStep::Step {
            rule,
            clause: vec![],
            premises: vec![],
            args: vec![],
        });
        let expected = oracle::recheck(&bundle);
        assert!(matches!(
            expected,
            Err(ProofCheckError::TrustStep { .. } | ProofCheckError::HoleStep { .. })
        ));
        assert_same(
            expected,
            re_check_bundle_strict_with_cancellation(&bundle, &mut || true),
        );
    }
}

#[test]
fn exact_datatype_context_and_nullary_binding_mutations_remain_invalid() {
    let base = datatype();
    let mut wrong_sort = base.clone();
    wrong_sort.datatype_member_signatures[0].result_sort = Sort::Int;
    let mut wrong_binding = base.clone();
    wrong_binding.datatype_member_signatures[0].nullary_term =
        base.datatype_member_signatures[2].nullary_term;
    let mut missing_signature = base.clone();
    missing_signature.datatype_member_signatures.pop();
    for bundle in [wrong_sort, wrong_binding, missing_signature] {
        let expected = oracle::recheck(&bundle);
        assert!(expected.is_err());
        assert_same(
            expected,
            re_check_bundle_strict_with_cancellation(&bundle, &mut || true),
        );
    }
}

#[test]
fn unused_skolem_name_collision_and_choice_mutation_do_not_restore_authority() {
    let base = skolem();
    let mut collision = base.clone();
    collision.term_entries.push((
        TermData::Var("cancel-witness".to_owned(), 90_000),
        Sort::Int,
    ));
    let mut bad_choice = base.clone();
    let ProofStep::Step { args, .. } = &mut bad_choice.steps[0] else {
        panic!("Skolem fixture")
    };
    args[0] = base.obligation_assertions[0];
    for bundle in [collision, bad_choice] {
        let expected = oracle::recheck(&bundle);
        assert!(expected.is_err());
        assert_same(
            expected,
            re_check_bundle_strict_with_cancellation(&bundle, &mut || true),
        );
    }
}

#[test]
fn callback_panic_is_not_caught_by_the_public_reader() {
    let bundle = contradiction(false);
    let before = serde_json::to_vec(&bundle).unwrap();
    let result = catch_unwind(AssertUnwindSafe(|| {
        re_check_bundle_strict_with_cancellation(&bundle, &mut || std::panic::panic_any(317u32))
    }));
    assert_eq!(*result.unwrap_err().downcast::<u32>().unwrap(), 317);
    assert_eq!(serde_json::to_vec(&bundle).unwrap(), before);
    assert!(re_check_bundle_strict(&bundle).is_ok());
}

#[test]
fn an_inner_guard_catching_callback_panic_cannot_retry_or_publish() {
    for proposed in [Ok(()), Err(ProofCheckError::EmptyProof)] {
        let mut calls = 0;
        let mut callback = || {
            calls += 1;
            if calls == 2 {
                std::panic::panic_any(318u32);
            }
            true
        };
        let result = Cancellation {
            progress: &mut callback,
            refused: false,
        }
        .run(|progress| {
            let panic = catch_unwind(AssertUnwindSafe(|| progress(0, 0))).unwrap_err();
            assert_eq!(*panic.downcast::<u32>().unwrap(), 318);
            assert!(
                !progress(0, 0),
                "caught panic must keep the attempt refused"
            );
            proposed
        });
        assert!(matches!(result, Err(ProofCheckError::ResourceLimit)));
        assert_eq!(calls, 2);
    }
}

/// #completed-check-accepted. A stop that arrives after the operation's last
/// callback (here: once its private frame is gone) is never consulted: a
/// completed re-check is returned, and a genuine validation error is not
/// replaced by `ResourceLimit`. The latch still refuses anything the operation
/// itself observed (see the inner-guard test above).
#[test]
fn a_stop_after_the_operation_completed_does_not_replace_its_result() {
    struct Finished<'a>(&'a Cell<bool>);
    impl Drop for Finished<'_> {
        fn drop(&mut self) {
            self.0.set(true);
        }
    }
    for proposed in [Ok(()), Err(ProofCheckError::EmptyProof)] {
        let finished = Cell::new(false);
        let mut calls = 0;
        let mut callback = || {
            calls += 1;
            !finished.get()
        };
        let result = Cancellation {
            progress: &mut callback,
            refused: false,
        }
        .run(|_| {
            let _owned = Finished(&finished);
            proposed.clone()
        });
        assert!(finished.get());
        assert_eq!(result, proposed);
        assert_eq!(
            calls, 1,
            "only the admission poll; nothing after completion"
        );
    }
}
