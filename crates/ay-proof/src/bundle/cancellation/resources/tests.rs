// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::AletheRule;

mod refusal;

use super::super::super::cancellation_fixtures as fixtures;
use super::super::oracle;
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

fn trace(bundle: &SerializableProofBundle) -> Vec<(usize, usize)> {
    let mut charges = Vec::new();
    re_check_bundle_strict_with_resource_control(bundle, &mut |work, bytes| {
        charges.push((work, bytes));
        true
    })
    .expect("the fixture has a genuine strict refutation");
    charges
}

fn totals(charges: &[(usize, usize)]) -> (usize, usize) {
    charges.iter().fold((0usize, 0usize), |(w, b), (dw, db)| {
        (w.checked_add(*dw).unwrap(), b.checked_add(*db).unwrap())
    })
}

fn within(used: &mut (usize, usize), cap: (usize, usize), delta: (usize, usize)) -> bool {
    let Some(work) = used.0.checked_add(delta.0) else {
        return false;
    };
    let Some(bytes) = used.1.checked_add(delta.1) else {
        return false;
    };
    if work > cap.0 || bytes > cap.1 {
        return false;
    }
    *used = (work, bytes);
    true
}

fn bounded(
    bundle: &SerializableProofBundle,
    cap: (usize, usize),
) -> Result<BundleReCheck, ProofCheckError> {
    let mut used = (0, 0);
    re_check_bundle_strict_with_resource_control(bundle, &mut |work, bytes| {
        within(&mut used, cap, (work, bytes))
    })
}

fn assert_resource(result: Result<BundleReCheck, ProofCheckError>) {
    assert!(matches!(result, Err(ProofCheckError::ResourceLimit)));
}

#[test]
fn real_boolean_datatype_and_skolem_proofs_keep_results_and_legacy_checkpoints() {
    for bundle in [
        contradiction(false),
        contradiction(true),
        datatype(),
        skolem(),
    ] {
        let before = serde_json::to_vec(&bundle).unwrap();
        let expected = oracle::recheck(&bundle);
        assert!(expected.is_ok());
        let charges = trace(&bundle);
        let mut legacy_calls = 0;
        let legacy = re_check_bundle_strict_with_cancellation(&bundle, &mut || {
            legacy_calls += 1;
            true
        });
        assert_eq!(legacy_calls, charges.len());
        assert_eq!(charges.first(), Some(&(0, 0)));
        // #completed-check-accepted: the strict check's final step is the last
        // callback; no zero-delta poll follows the completed re-check.
        assert_ne!(charges.last(), Some(&(0, 0)));
        assert_same(expected, legacy);
        assert_same(oracle::recheck(&bundle), bounded(&bundle, totals(&charges)));
        assert_eq!(serde_json::to_vec(&bundle).unwrap(), before);
    }
    let duplicate = contradiction(true);
    let charges = trace(&duplicate);
    assert!(
        charges.contains(&(4, 4 * size_of::<TermId>())),
        "the owning assumption vector must be prepaid, including duplicate slots"
    );
    let result = bounded(&duplicate, totals(&charges)).unwrap();
    let [positive, negative] = duplicate.obligation_assertions.as_slice() else {
        panic!("two original assumptions");
    };
    assert_eq!(
        result.assume_terms,
        [*positive, *positive, *negative, *positive]
    );
}

#[test]
fn complete_work_and_byte_totals_have_exact_and_one_short_boundaries() {
    for bundle in [contradiction(true), datatype(), skolem()] {
        let (work, bytes) = totals(&trace(&bundle));
        assert!(work > 0 && bytes > 0);
        assert!(bounded(&bundle, (work, bytes)).is_ok());
        for cap in [(work - 1, bytes), (work, bytes - 1), (0, bytes), (work, 0)] {
            assert_resource(bounded(&bundle, cap));
        }
        assert!(bounded(&bundle, (work, bytes)).is_ok());
    }
}

#[test]
fn repeated_replay_uses_the_callers_cumulative_allowance_without_resetting_it() {
    let bundle = skolem();
    let single = totals(&trace(&bundle));
    let twice = (
        single.0.checked_mul(2).unwrap(),
        single.1.checked_mul(2).unwrap(),
    );
    let mut used = (0, 0);
    let mut progress = |work, bytes| within(&mut used, twice, (work, bytes));
    assert!(re_check_bundle_strict_with_resource_control(&bundle, &mut progress).is_ok());
    assert!(re_check_bundle_strict_with_resource_control(&bundle, &mut progress).is_ok());
    assert_resource(re_check_bundle_strict_with_resource_control(
        &bundle,
        &mut progress,
    ));
    assert_eq!(used, twice);
}

#[test]
fn unused_large_snapshot_payload_is_paid_before_copying_not_hidden_by_proof_roots() {
    let small = contradiction(false);
    let small_cost = totals(&trace(&small));
    let mut large = small.clone();
    large.term_entries.push((
        TermData::Const(Constant::String("unused-payload".repeat(8192))),
        Sort::String,
    ));
    assert!(re_check_bundle_strict(&large).is_ok());
    let large_cost = totals(&trace(&large));
    assert!(large_cost.1 > small_cost.1 + 8192 * "unused-payload".len());
    assert_resource(bounded(&large, (usize::MAX, small_cost.1)));
    assert!(bounded(&large, large_cost).is_ok());
    assert!(bounded(&small, small_cost).is_ok());
}
