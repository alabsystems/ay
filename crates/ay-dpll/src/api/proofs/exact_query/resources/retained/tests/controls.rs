// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn retained_export_has_exact_one_short_and_nonrenewed_attempt_boundaries() {
    let (solver, binding) = solved(BOOLEAN);
    let (work, bytes) = totals(&trace(&solver, &binding));
    for (wc, bc, accepted) in [
        (work, bytes, true),
        (work - 1, bytes, false),
        (work, bytes - 1, false),
    ] {
        let (mut w, mut b) = (0, 0);
        let result = solver
            .export_last_unsat_retained_bundle_for_exact_query_with_resource_control(
                &binding,
                deadline(),
                &mut |dw, db| {
                    w += dw;
                    b += db;
                    w <= wc && b <= bc
                },
            );
        if accepted {
            assert!(result.unwrap().is_some());
        } else {
            assert!(matches!(result, Err(ProofCheckError::ResourceLimit)));
        }
    }
    let (mut w, mut b) = (0, 0);
    let mut shared = |dw, db| {
        w += dw;
        b += db;
        w <= work && b <= bytes
    };
    assert!(solver
        .export_last_unsat_retained_bundle_for_exact_query_with_resource_control(
            &binding,
            deadline(),
            &mut shared,
        )
        .unwrap()
        .is_some());
    assert!(matches!(
        solver.export_last_unsat_retained_bundle_for_exact_query_with_resource_control(
            &binding,
            deadline(),
            &mut shared,
        ),
        Err(ProofCheckError::ResourceLimit)
    ));
}

#[test]
#[ntest::timeout(60000)]
fn every_retained_export_callback_stop_is_terminal_without_a_raw_fallback() {
    let (solver, binding) = solved(BOOLEAN);
    let expected = trace(&solver, &binding);
    for stop in 1..=expected.len() {
        let mut actual = Vec::new();
        let result = solver
            .export_last_unsat_retained_bundle_for_exact_query_with_resource_control(
                &binding,
                deadline(),
                &mut |w, b| {
                    actual.push((w, b));
                    actual.len() != stop
                },
            );
        assert!(
            matches!(result, Err(ProofCheckError::ResourceLimit)),
            "checkpoint {stop}"
        );
        assert_eq!(actual, expected[..stop]);
    }
    assert_eq!(trace(&solver, &binding), expected);
}

#[test]
fn expired_original_deadline_refuses_before_source_walk_or_user_callback() {
    let (solver, binding) = solved(BOOLEAN);
    let mut calls = 0;
    let result = solver.export_last_unsat_retained_bundle_for_exact_query_with_resource_control(
        &binding,
        Instant::now(),
        &mut |_, _| {
            calls += 1;
            true
        },
    );
    assert!(matches!(result, Err(ProofCheckError::ResourceLimit)));
    assert_eq!(calls, 0);
}

#[test]
fn export_encoding_and_consumer_replay_share_one_exact_or_one_short_ledger() {
    let (solver, binding) = solved(BOOLEAN);
    let original_deadline = deadline();
    let mut expected = Vec::new();
    let mut counting = |work, bytes| {
        expected.push((work, bytes));
        true
    };
    let artifact = solver
        .export_last_unsat_retained_bundle_for_exact_query_with_resource_control(
            &binding,
            original_deadline,
            &mut counting,
        )
        .unwrap()
        .unwrap();
    let encoded = artifact
        .encode_with_resource_control(limits(), original_deadline, &mut counting)
        .unwrap();
    assert!(artifact
        .replay_exact_with_resource_control(original_deadline, &mut counting)
        .unwrap()
        .quality
        .is_complete());
    let (work, bytes) = totals(&expected);
    let export_cost = totals(&trace(&solver, &binding));
    assert!(work > export_cost.0 && bytes > export_cost.1);
    for (wc, bc, accepted) in [
        (work, bytes, true),
        (work - 1, bytes, false),
        (work, bytes - 1, false),
    ] {
        let (mut w, mut b) = (0, 0);
        let mut shared = |dw, db| {
            w += dw;
            b += db;
            w <= wc && b <= bc
        };
        let artifact = solver
            .export_last_unsat_retained_bundle_for_exact_query_with_resource_control(
                &binding,
                original_deadline,
                &mut shared,
            )
            .unwrap()
            .unwrap();
        assert_eq!(
            artifact
                .encode_with_resource_control(limits(), original_deadline, &mut shared)
                .unwrap(),
            encoded
        );
        let replay = artifact.replay_exact_with_resource_control(original_deadline, &mut shared);
        if accepted {
            assert!(replay.unwrap().quality.is_complete());
        } else {
            assert!(matches!(replay, Err(ProofCheckError::ResourceLimit)));
        }
    }
}
