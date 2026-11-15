// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::cell::Cell;
use std::panic::{catch_unwind, AssertUnwindSafe};

mod controls;
mod resources;

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

fn source(index: usize) -> (BvExpr, BvExpr) {
    let a = BvExpr::leaf("chain_a", 1);
    match index {
        0 => (a.clone(), a),
        1 => (BvExpr::xor(a.clone(), a), BvExpr::const_val(0, 1)),
        2 => (
            BvExpr::and(a.clone(), BvExpr::not(a)),
            BvExpr::const_val(0, 1),
        ),
        _ => unreachable!(),
    }
}

fn no_search(proof: &mut BvExprProofLimits) {
    proof.resolution.max_conflicts = Some(0);
    proof.resolution.max_decisions = Some(0);
    proof.resolution.max_backward_reconstruction_bytes = 0;
    proof.resolution.max_pending_deletions = 0;
}

fn capture_many<const N: usize>(grant: u64) -> Result<Metered<[Vec<u8>; N]>, MeteredError> {
    let (proof, gates, wire) = limits();
    run(
        &proof,
        &gates,
        &wire,
        allowance(grant),
        &mut || true,
        |chain| {
            let mut frames: [Vec<u8>; N] = std::array::from_fn(|_| Vec::new());
            for (index, frame) in frames.iter_mut().enumerate() {
                let (lhs, rhs) = source(index);
                *frame = chain.capture_one(&lhs, &rhs, &proof, &gates)?;
            }
            Ok(frames)
        },
    )
}

fn replay_many(frames: &[Vec<u8>], grant: u64) -> Result<Metered<()>, MeteredError> {
    let (mut proof, gates, wire) = limits();
    no_search(&mut proof);
    run(
        &proof,
        &gates,
        &wire,
        allowance(grant),
        &mut || true,
        |chain| {
            for (index, frame) in frames.iter().enumerate() {
                let (lhs, rhs) = source(index);
                chain.replay_one(&lhs, &rhs, frame, &proof, &gates)?;
            }
            Ok(())
        },
    )
}

fn total(w: work::WorkUsage) -> u64 {
    w.producer_validation + w.retained_prefix + w.gates + w.dag + w.wire
}

#[test]
fn two_and_three_real_proofs_replay_after_producer_drop_without_producer_calls() {
    let before = producer_test_counter::count();
    let two = capture_many::<2>(1_000_000).unwrap();
    let three = capture_many::<3>(1_000_000).unwrap();
    assert_eq!(producer_test_counter::count(), before + 5);
    assert!(three.value.iter().all(|frame| !frame.is_empty()));
    assert!(three.work.producer_validation > two.work.producer_validation);
    let calls = producer_test_counter::count();
    for frames in [two.value.as_slice(), three.value.as_slice()] {
        let replay = replay_many(frames, 1_000_000).unwrap();
        assert_eq!(replay.work.producer_validation, 0);
        assert!(replay.work.gates > 0 && replay.work.dag > 0 && replay.work.wire > 0);
    }
    assert_eq!(producer_test_counter::count(), calls);
}

#[test]
fn multi_proof_work_is_additive_exact_one_short_and_zero() {
    let produced = capture_many::<3>(1_000_000).unwrap();
    let exact = total(produced.work);
    assert_eq!(capture_many::<3>(exact).unwrap().work, produced.work);
    assert!(capture_many::<3>(exact - 1).is_err());
    assert!(capture_many::<3>(0).is_err());
    let replayed = replay_many(&produced.value, 1_000_000).unwrap();
    let exact = total(replayed.work);
    assert_eq!(
        replay_many(&produced.value, exact).unwrap().work,
        replayed.work
    );
    assert!(replay_many(&produced.value, exact - 1).is_err());
    assert!(replay_many(&produced.value, 0).is_err());
    // Independent one-proof calls measure the very same phase bodies. In
    // particular final DAG replay is not charged its prefix a second time.
    let (mut proof, gates, wire) = limits();
    let mut captured = work::WorkUsage::default();
    let mut replay_sum = work::WorkUsage::default();
    for (index, bytes) in produced.value.iter().enumerate() {
        let (lhs, rhs) = source(index);
        let one = capture(
            &lhs,
            &rhs,
            &proof,
            &gates,
            &wire,
            allowance(1_000_000),
            &mut || true,
        )
        .unwrap();
        add_work(&mut captured, one.work);
        no_search(&mut proof);
        let one = replay(
            &lhs,
            &rhs,
            bytes,
            &proof,
            &gates,
            &wire,
            allowance(1_000_000),
            &mut || true,
        )
        .unwrap();
        add_work(&mut replay_sum, one.work);
        proof = limits().0;
    }
    assert_eq!(captured, produced.work);
    assert_eq!(replay_sum, replayed.work);
}

fn add_work(a: &mut work::WorkUsage, b: work::WorkUsage) {
    a.producer_validation += b.producer_validation;
    a.retained_prefix += b.retained_prefix;
    a.gates += b.gates;
    a.dag += b.dag;
    a.wire += b.wire;
}

#[test]
fn false_final_changed_source_and_corrupt_frames_refuse_without_replay_search() {
    let frames = capture_many::<3>(1_000_000).unwrap().value;
    let (mut proof, gates, wire) = limits();
    let a = BvExpr::leaf("chain_a", 1);
    let b = BvExpr::leaf("chain_b", 1);
    assert!(run(
        &proof,
        &gates,
        &wire,
        allowance(1_000_000),
        &mut || true,
        |chain| {
            let _first = chain.capture_one(&a, &a, &proof, &gates)?;
            chain.capture_one(&a, &b, &proof, &gates)
        }
    )
    .is_err());
    no_search(&mut proof);
    let calls = producer_test_counter::count();
    assert!(run(
        &proof,
        &gates,
        &wire,
        allowance(1_000_000),
        &mut || true,
        |chain| {
            chain.replay_one(&a, &a, &frames[0], &proof, &gates)?;
            chain.replay_one(&a, &b, &frames[1], &proof, &gates)
        }
    )
    .is_err());
    for corrupt in 0..2 {
        let mut altered = frames.clone();
        let mut payload: RetainedBvRefutation = serde_json::from_slice(&altered[2]).unwrap();
        if corrupt == 0 {
            payload.empty_clause_id = u64::MAX;
        } else {
            payload.rows.last_mut().unwrap().hints = vec![u64::MAX];
        }
        altered[2] = serde_json::to_vec(&payload).unwrap();
        assert!(replay_many(&altered, 1_000_000).is_err());
    }
    assert_eq!(producer_test_counter::count(), calls);
}
