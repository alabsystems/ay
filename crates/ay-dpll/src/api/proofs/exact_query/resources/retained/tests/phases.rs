// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

/// Reproduce only the source-authenticated construction/capture prefix. This
/// makes the next binding checkpoint observable without a production test hook
/// or an extra legacy strict check in the retained exporter.
fn capture_prefix(solver: &Solver, binding: &ExactSmtlibQueryBinding) -> Vec<(usize, usize)> {
    let mut charges = Vec::new();
    {
        let mut counting = |w, b| {
            charges.push((w, b));
            true
        };
        let capture = {
            let mut control = Control::new(&mut counting);
            control.charge(0, 0).unwrap();
            let roots = resolve_roots(solver, binding, &mut control)
                .unwrap()
                .unwrap();
            let source = solver
                .executor
                .exact_plain_query_proof_source_with_resource_control(
                    &roots,
                    &binding.source_context,
                    &mut |w, b| control.charge(w, b).is_ok(),
                )
                .unwrap()
                .unwrap();
            let allowed = source
                .source_closure_with_resource_control(&mut |w, b| control.charge(w, b).is_ok())
                .unwrap();
            assert_ne!(allowed, [] as [ay_core::TermId; 0]);
            let snapshot = construction::bundle(
                solver,
                source.proof(),
                |progress| source.complete_problem_with_resource_control(progress),
                &mut |w, b| control.charge(w, b).is_ok(),
            )
            .unwrap()
            .unwrap();
            capture_strict_retained_bundle_with_resource_control(
                snapshot,
                deadline(),
                &mut |w, b| control.charge(w, b).is_ok(),
            )
            .unwrap()
        };
        assert!(capture.first_check().quality.is_complete());
        drop(capture);
    }
    charges
}

#[test]
fn expiry_between_capture_and_live_binding_cannot_start_second_replay() {
    let (solver, binding) = solved(BOOLEAN);
    let prefix = capture_prefix(&solver, &binding);
    let expected = trace(&solver, &binding);
    assert_eq!(prefix, expected[..prefix.len()]);
    assert_eq!(expected[prefix.len()], (0, 0));
    let original_deadline = Instant::now() + Duration::from_secs(1);
    let mut actual = Vec::new();
    let result = solver.export_last_unsat_retained_bundle_for_exact_query_with_resource_control(
        &binding,
        original_deadline,
        &mut |work, bytes| {
            actual.push((work, bytes));
            if actual.len() == prefix.len() + 1 {
                while Instant::now() < original_deadline {
                    std::thread::sleep(Duration::from_millis(1));
                }
            }
            true
        },
    );
    assert!(matches!(result, Err(ProofCheckError::ResourceLimit)));
    assert_eq!(actual, expected[..=prefix.len()]);
}

#[test]
fn later_encode_or_replay_deadline_cannot_reopen_expired_producer_episode() {
    let (solver, binding) = solved(BOOLEAN);
    let original_deadline = Instant::now() + Duration::from_secs(1);
    let mut ledger = |_, _| true;
    let artifact = solver
        .export_last_unsat_retained_bundle_for_exact_query_with_resource_control(
            &binding,
            original_deadline,
            &mut ledger,
        )
        .unwrap()
        .unwrap();
    while Instant::now() < original_deadline {
        std::thread::sleep(Duration::from_millis(1));
    }
    let mut calls = 0;
    let mut observed = |_, _| {
        calls += 1;
        true
    };
    assert!(matches!(
        artifact.encode_with_resource_control(limits(), deadline(), &mut observed),
        Err(ProofCheckError::Cancelled)
    ));
    assert!(matches!(
        artifact.replay_exact_with_resource_control(deadline(), &mut observed),
        Err(ProofCheckError::Cancelled)
    ));
    assert_eq!(calls, 0);
}
