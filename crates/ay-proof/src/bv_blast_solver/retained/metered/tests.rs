// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::cell::Cell;

fn limits() -> (BvExprProofLimits, BvBlastValidateLimits, wire::WireLimits) {
    let end = Instant::now() + Duration::from_secs(60);
    let proof = BvExprProofLimits::conservative_external(end, 100);
    let gates = BvBlastValidateLimits {
        deadline: Some(end),
        max_vars: 4096,
        max_bit_lemmas: 4096,
        max_clauses: 16000,
        max_clause_literals: 64,
        max_original_literals: 64000,
        max_resolution_steps: 100,
        max_derived_literals: 10000,
        max_work: 1_000_000,
    };
    let wire = wire::WireLimits {
        max_json_bytes: 1_000_000,
        max_rows: 100,
        max_literals: 10000,
        max_hints: 10000,
        max_work: 1_000_000,
        max_storage_bytes: 8 * 1024 * 1024,
        deadline: end,
    };
    (proof, gates, wire)
}

fn allowance(limit: u64) -> WorkAllowance {
    WorkAllowance::new(limit, Instant::now() + Duration::from_secs(60))
}

fn total(work: work::WorkUsage) -> u64 {
    work.producer_validation + work.retained_prefix + work.gates + work.dag + work.wire
}

fn capture_identity(limit: u64) -> Result<Metered<Vec<u8>>, MeteredError> {
    let (proof, gates, wire) = limits();
    let a = BvExpr::leaf("a", 1);
    capture(&a, &a, &proof, &gates, &wire, allowance(limit), &mut || {
        true
    })
}

fn replay_identity(bytes: &[u8], limit: u64) -> Result<Metered<()>, MeteredError> {
    let (mut proof, gates, wire) = limits();
    proof.resolution.max_conflicts = Some(0);
    proof.resolution.max_decisions = Some(0);
    proof.resolution.max_backward_reconstruction_bytes = 0;
    proof.resolution.max_pending_deletions = 0;
    let a = BvExpr::leaf("a", 1);
    replay(
        &a,
        &a,
        bytes,
        &proof,
        &gates,
        &wire,
        allowance(limit),
        &mut || true,
    )
}

#[test]
fn unreported_sweep_validation_cannot_mint_metered_producer_credit() {
    let (mut proof, gates, wire) = limits();
    proof.sweep = true;
    proof.resolution.max_codec_bytes = 0;
    let a = BvExpr::leaf("a", 1);
    let result = capture(
        &a,
        &a,
        &proof,
        &gates,
        &wire,
        allowance(1_000_000),
        &mut || true,
    );
    assert!(matches!(result,
        Err(MeteredError::Proof(BvExprExportError::Malformed(message)))
            if message == "missing producer validation work"));
}

#[test]
fn capture_and_offline_replay_obey_exact_combined_work_and_one_short() {
    let produced = capture_identity(1_000_000).unwrap();
    let cap = total(produced.work);
    assert!(produced.work.producer_validation > 0);
    assert_eq!(produced.work.producer_validation, produced.work.dag);
    assert!(produced.work.retained_prefix > 0 && produced.work.gates > 0 && produced.work.wire > 0);
    let exact = capture_identity(cap).unwrap();
    assert_eq!(exact.value, produced.value);
    assert_eq!(exact.work, produced.work);
    assert!(capture_identity(cap - 1).is_err());
    let replayed = replay_identity(&produced.value, 1_000_000).unwrap();
    assert_eq!(replayed.work.producer_validation, 0);
    assert_eq!(replayed.work.dag, produced.work.dag);
    let cap = total(replayed.work);
    assert_eq!(
        replay_identity(&produced.value, cap).unwrap().work,
        replayed.work
    );
    assert!(replay_identity(&produced.value, cap - 1).is_err());
    assert!(capture_identity(0).is_err());
    assert!(replay_identity(&produced.value, 0).is_err());
}

#[test]
fn individually_fitting_phases_cannot_multiply_one_allowance() {
    let produced = capture_identity(1_000_000).unwrap();
    let w = produced.work;
    let largest = [
        w.producer_validation,
        w.retained_prefix,
        w.gates,
        w.dag,
        w.wire,
    ]
    .into_iter()
    .max()
    .unwrap();
    assert!(largest < total(w));
    assert!(capture_identity(largest).is_err());
    let replayed = replay_identity(&produced.value, 1_000_000).unwrap();
    let w = replayed.work;
    let largest = [w.retained_prefix, w.gates, w.dag, w.wire]
        .into_iter()
        .max()
        .unwrap();
    assert!(largest < total(w));
    assert!(replay_identity(&produced.value, largest).is_err());
}

#[test]
fn abundant_total_does_not_override_existing_phase_caps() {
    let produced = capture_identity(1_000_000).unwrap();
    let a = BvExpr::leaf("a", 1);
    for cap in 0..3 {
        let (mut proof, mut gates, mut wire) = limits();
        match cap {
            0 => gates.max_work = 0,
            1 => proof.resolution.validation.max_work = 0,
            2 => wire.max_work = 0,
            _ => unreachable!(),
        }
        assert!(capture(
            &a,
            &a,
            &proof,
            &gates,
            &wire,
            allowance(u64::MAX),
            &mut || true
        )
        .is_err());
        assert!(replay(
            &a,
            &a,
            &produced.value,
            &proof,
            &gates,
            &wire,
            allowance(u64::MAX),
            &mut || true
        )
        .is_err());
    }
}

#[test]
fn wire_and_prefix_are_debited_once_against_independent_existing_operations() {
    let produced = capture_identity(1_000_000).unwrap();
    let (proof, gates, wire) = limits();
    let decoded = wire::decode(&produced.value, &wire, &proof, &gates, &mut || true);
    let decode_work = decoded.usage.charged_work;
    let payload = decoded.result.unwrap();
    let encoded = wire::encode(&payload, &wire, &proof, &gates, &mut || true);
    assert_eq!(encoded.result.unwrap(), produced.value);
    assert_eq!(u128::from(produced.work.wire), encoded.usage.charged_work);
    let replayed = replay_identity(&produced.value, 1_000_000).unwrap();
    assert_eq!(u128::from(replayed.work.wire), decode_work);
    let a = BvExpr::leaf("a", 1);
    let graph = cnf::build_bv_expr_cnf(&a, &a, &proof, &mut || true)
        .unwrap()
        .into_graph();
    let mut control = Control::new(&proof);
    control.charge(1, &mut || true).unwrap();
    let shape = control.payload(&payload, &mut || true).unwrap();
    let payload_bytes = control.bytes;
    let graph_bytes = control.graph(&graph, &mut || true).unwrap();
    let dag = codec::decode(&payload, shape, &graph, &mut control, &mut || true).unwrap();
    let reduced = control
        .replay_limits(&graph, graph_bytes, payload_bytes, &mut || true)
        .unwrap();
    assert_eq!(replayed.work.retained_prefix, control.work);
    assert_eq!(
        replayed.work.dag,
        dag.validate_with_limits_and_cancellation_work(&reduced.resolution.validation, &mut || {
            true
        })
        .unwrap()
    );
    assert_eq!(
        replayed.work.gates,
        graph
            .validate_cnf_with_limits_and_cancellation_work(&gates, &mut || true)
            .unwrap()
    );
}

#[test]
fn malformed_wire_changed_source_and_missing_deadline_never_publish_usage() {
    let produced = capture_identity(1_000_000).unwrap();
    let (mut proof, gates, wire) = limits();
    let a = BvExpr::leaf("a", 1);
    let b = BvExpr::leaf("b", 1);
    assert!(replay(
        &a,
        &b,
        &produced.value,
        &proof,
        &gates,
        &wire,
        allowance(1_000_000),
        &mut || true
    )
    .is_err());
    assert!(replay_identity(b"null", 1_000_000).is_err());
    proof.resolution.deadline = None;
    assert!(capture(
        &a,
        &a,
        &proof,
        &gates,
        &wire,
        allowance(1_000_000),
        &mut || true
    )
    .is_err());
    assert!(replay(
        &a,
        &a,
        &produced.value,
        &proof,
        &gates,
        &wire,
        allowance(1_000_000),
        &mut || true
    )
    .is_err());
}

#[test]
fn every_capture_and_replay_poll_including_final_cleanup_is_terminal() {
    let produced = capture_identity(1_000_000).unwrap();
    let a = BvExpr::leaf("a", 1);
    for capturing in [true, false] {
        let invoke = |poll: &mut dyn FnMut() -> bool| {
            let (proof, gates, wire) = limits();
            if capturing {
                capture(&a, &a, &proof, &gates, &wire, allowance(1_000_000), poll).map(|_| ())
            } else {
                replay(
                    &a,
                    &a,
                    &produced.value,
                    &proof,
                    &gates,
                    &wire,
                    allowance(1_000_000),
                    poll,
                )
                .map(|_| ())
            }
        };
        let count = Cell::new(0);
        invoke(&mut || {
            count.set(count.get() + 1);
            true
        })
        .unwrap();
        assert!(count.get() > 10);
        for stop in 1..=count.get() {
            let calls = Cell::new(0);
            assert!(
                invoke(&mut || {
                    calls.set(calls.get() + 1);
                    calls.get() != stop
                })
                .is_err(),
                "capture={capturing}, poll={stop}"
            );
            assert_eq!(
                calls.get(),
                stop,
                "no callback revival after transient stop"
            );
        }
    }
}

#[test]
fn every_participating_deadline_is_intersected_before_any_work() {
    let produced = capture_identity(1_000_000).unwrap();
    let a = BvExpr::leaf("a", 1);
    let past = Instant::now() - Duration::from_secs(1);
    for expired in 0..5 {
        let (mut proof, mut gates, mut wire) = limits();
        let mut end = wire.deadline;
        match expired {
            0 => end = past,
            1 => wire.deadline = past,
            2 => gates.deadline = Some(past),
            3 => proof.resolution.deadline = Some(past),
            4 => proof.resolution.validation.deadline = Some(past),
            _ => unreachable!(),
        }
        let mut poll = || panic!("expired deadline cannot enter caller work");
        assert!(capture(
            &a,
            &a,
            &proof,
            &gates,
            &wire,
            WorkAllowance::new(1_000_000, end),
            &mut poll
        )
        .is_err());
        assert!(replay(
            &a,
            &a,
            &produced.value,
            &proof,
            &gates,
            &wire,
            WorkAllowance::new(1_000_000, end),
            &mut poll
        )
        .is_err());
    }
}

#[test]
fn failure_only_cleanup_polls_cannot_revive_cancellation() {
    let produced = capture_identity(1_000_000).unwrap();
    let a = BvExpr::leaf("a", 1);
    for malformed in [true, false] {
        let invoke = |poll: &mut dyn FnMut() -> bool| {
            let (proof, mut gates, wire) = limits();
            if !malformed {
                gates.max_work = 0;
            }
            let bytes = if malformed {
                b"null".as_slice()
            } else {
                &produced.value
            };
            replay(
                &a,
                &a,
                bytes,
                &proof,
                &gates,
                &wire,
                allowance(1_000_000),
                poll,
            )
        };
        let count = Cell::new(0);
        assert!(invoke(&mut || {
            count.set(count.get() + 1);
            true
        })
        .is_err());
        assert!(count.get() > 1);
        for stop in 1..=count.get() {
            let calls = Cell::new(0);
            assert!(invoke(&mut || {
                calls.set(calls.get() + 1);
                calls.get() != stop
            })
            .is_err());
            assert_eq!(calls.get(), stop);
        }
    }
}
