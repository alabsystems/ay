// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::bv_blast_solver::retained::{metered, producer_test_counter, work::WorkAllowance};
use std::time::Duration;

fn fixture() -> (
    BvExpr,
    BvExpr,
    BvExprProofLimits,
    BvBlastValidateLimits,
    wire::WireLimits,
    Vec<u8>,
) {
    let lhs = BvExpr::leaf("priced_source", 9);
    let rhs = BvExpr::add(lhs.clone(), BvExpr::const_val(0, 9));
    let end = Instant::now() + Duration::from_secs(60);
    let proof = BvExprProofLimits::conservative_external(end, 10_000);
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
        max_json_bytes: proof.resolution.max_codec_bytes,
        max_rows: proof.resolution.max_derived_steps,
        max_literals: proof.resolution.max_derived_literals,
        max_hints: proof.resolution.max_hints,
        max_work: proof.resolution.validation.max_work,
        max_storage_bytes: proof.resolution.validation.max_bytes,
        deadline: end,
    };
    let bytes = metered::capture(
        &lhs,
        &rhs,
        &proof,
        &gates,
        &wire,
        WorkAllowance::new(proof.resolution.validation.max_work, end),
        &mut || true,
    )
    .unwrap()
    .value;
    (lhs, rhs, proof, gates, wire, bytes)
}

#[test]
fn ordinary_price_covers_actual_meter_and_narrow_storage_replays_without_search() {
    let (lhs, rhs, mut proof, mut gates, mut wire, bytes) = fixture();
    let before = producer_test_counter::count();
    let price = price(
        &lhs,
        &rhs,
        &bytes,
        bytes.capacity(),
        &proof,
        &gates,
        &wire,
        &mut || true,
    )
    .unwrap();
    assert!(price.work < proof.resolution.validation.max_work as usize);
    assert!(price.bytes < 768 * 1024 * 1024);
    let original_end = proof.resolution.deadline;
    price.tighten(&mut proof, &mut wire);
    assert_eq!(proof.resolution.deadline, original_end);
    let replay = metered::replay(
        &lhs,
        &rhs,
        &bytes,
        &proof,
        &gates,
        &wire,
        WorkAllowance::new(price.work as u64, wire.deadline),
        &mut || true,
    )
    .unwrap();
    let work = replay.work;
    assert!(price.work as u64 >= work.retained_prefix + work.gates + work.dag + work.wire);
    assert_eq!(work.producer_validation, 0);
    assert_eq!(producer_test_counter::count(), before);
}

#[test]
fn unchanged_wire_width_and_negative_source_controls_remain_mandatory() {
    let (lhs, rhs, proof, gates, wire, bytes) = fixture();
    let wrong = BvExpr::add(lhs.clone(), BvExpr::const_val(1, 9));
    let price = price(
        &lhs,
        &wrong,
        &bytes,
        bytes.capacity(),
        &proof,
        &gates,
        &wire,
        &mut || true,
    )
    .unwrap();
    // A priced false source is NOT a validated proof, and cannot be accepted
    // even when its topology and untrusted payload fit every cheap dimension.
    let before = producer_test_counter::count();
    assert!(metered::replay(
        &lhs,
        &wrong,
        &bytes,
        &proof,
        &gates,
        &wire,
        WorkAllowance::new(price.work as u64, wire.deadline),
        &mut || true
    )
    .is_err());
    for malformed in [b"null".as_slice(), b"{}".as_slice(), b"[".as_slice()] {
        assert!(super::price(
            &lhs,
            &rhs,
            malformed,
            malformed.len(),
            &proof,
            &gates,
            &wire,
            &mut || true
        )
        .is_err());
    }
    let mut short = wire;
    short.max_json_bytes = bytes.len() - 1;
    assert!(super::price(
        &lhs,
        &rhs,
        &bytes,
        bytes.capacity(),
        &proof,
        &gates,
        &short,
        &mut || true
    )
    .is_err());
    assert_eq!(producer_test_counter::count(), before);
}

#[test]
fn backing_capacity_is_held_and_checked_arithmetic_never_wraps_or_mints_an_allowance() {
    let (lhs, rhs, proof, gates, wire, bytes) = fixture();
    let first = price(
        &lhs,
        &rhs,
        &bytes,
        bytes.len(),
        &proof,
        &gates,
        &wire,
        &mut || true,
    )
    .unwrap();
    let second = price(
        &lhs,
        &rhs,
        &bytes,
        bytes.len() + 4096,
        &proof,
        &gates,
        &wire,
        &mut || true,
    )
    .unwrap();
    assert_eq!(second.bytes - first.bytes, 4096);
    assert_eq!(second.work, first.work);
    assert!(matches!(wire_bounds(usize::MAX), Err(PriceError::Overflow)));
    assert!(matches!(
        price(
            &lhs,
            &rhs,
            &bytes,
            usize::MAX,
            &proof,
            &gates,
            &wire,
            &mut || true
        ),
        Err(PriceError::Overflow)
    ));
}

#[test]
fn every_planner_callback_stop_including_final_blocks_price_publication() {
    let (lhs, rhs, proof, gates, wire, bytes) = fixture();
    let mut total = 0;
    price(
        &lhs,
        &rhs,
        &bytes,
        bytes.capacity(),
        &proof,
        &gates,
        &wire,
        &mut || {
            total += 1;
            true
        },
    )
    .unwrap();
    for stop_at in 1..=total {
        let mut calls = 0;
        assert!(price(
            &lhs,
            &rhs,
            &bytes,
            bytes.capacity(),
            &proof,
            &gates,
            &wire,
            &mut || {
                calls += 1;
                calls != stop_at
            }
        )
        .is_err());
        assert!(calls <= stop_at + 1); // Final cleanup may observe a non-wire refusal.
    }
}

#[test]
fn original_expired_deadline_and_zero_storage_refuse_without_a_producer_retry() {
    let (lhs, rhs, mut proof, gates, mut wire, bytes) = fixture();
    let before = producer_test_counter::count();
    wire.max_storage_bytes = 0;
    assert!(price(
        &lhs,
        &rhs,
        &bytes,
        bytes.capacity(),
        &proof,
        &gates,
        &wire,
        &mut || true
    )
    .is_err());
    wire.max_storage_bytes = 128 * 1024 * 1024;
    proof.resolution.deadline = Some(Instant::now());
    assert!(price(
        &lhs,
        &rhs,
        &bytes,
        bytes.capacity(),
        &proof,
        &gates,
        &wire,
        &mut || true
    )
    .is_err());
    assert_eq!(producer_test_counter::count(), before);
}

#[test]
fn shared_expression_source_bounds_include_every_repeated_output_copy_and_real_cnf() {
    let end = Instant::now() + Duration::from_secs(60);
    let proof = BvExprProofLimits::conservative_external(end, 10_000);
    for width in [1, 9, 64, 128] {
        let mut shared = BvExpr::leaf("shared_output_copy", width);
        for _ in 0..5 {
            shared = BvExpr::add(shared.clone(), shared);
        }
        let lhs = BvExpr::eq(shared.clone(), shared);
        let rhs = BvExpr::const_val(1, 1);
        let preflight = preflight_bv_equality(&lhs, &rhs, &proof, &mut || true).unwrap();
        let bound = source_bound(&lhs, &rhs, &proof, &mut || true).unwrap();
        assert!(
            bound.construction_work
                >= preflight.occurrences * (1 + 2 * proof.max_internal_width as usize)
        );
        let graph = cnf::build_bv_expr_cnf(&lhs, &rhs, &proof, &mut || true).unwrap();
        assert!(graph.vars.len() <= bound.gates);
        assert!(graph.bit_lemmas.len() <= bound.gates);
        assert!(graph.clauses.len() <= bound.clauses);
        assert!(
            graph
                .clauses
                .iter()
                .map(|row| row.lits.len())
                .sum::<usize>()
                <= bound.literals
        );
    }
}
