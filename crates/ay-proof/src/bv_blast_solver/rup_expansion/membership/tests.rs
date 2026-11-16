// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::bv_blast_solver::{rup_expansion::resolve_pair, RupExpansionLimits};
use ay_core::time::Instant;
use std::time::Duration;

fn caps() -> RupExpansionLimits {
    RupExpansionLimits {
        max_steps: 0,
        max_literals: 4096,
        max_work: 4096,
        max_bytes: 1024 * 1024,
        deadline: Instant::now() + Duration::from_secs(10),
    }
}

#[test]
fn long_resolution_matches_reference_order_and_rejects_tautologies() {
    for width in [8, 16, 32, 128] {
        let a: Vec<_> = (0..width).map(Lit::pos).collect();
        let mut b: Vec<_> = (1..width).rev().map(Lit::pos).collect();
        b.extend([Lit::neg(0), Lit::pos(width)]);
        for change in 0..4 {
            let mut right = b.clone();
            match change {
                1 => right.push(Lit::neg(width - 1)),
                2 => right.retain(|lit| lit.var != 0),
                3 => right.push(Lit::pos(0)),
                _ => (),
            }
            let expected = resolve_pair(
                &a,
                &right,
                0,
                &mut RupExpansionState::<'_>::new(0, None, &mut || true),
            )
            .unwrap();
            let actual = resolve_pair(
                &a,
                &right,
                0,
                &mut RupExpansionState::<'_>::new(0, Some(caps()), &mut || true),
            )
            .unwrap();
            assert_eq!(actual, expected, "width {width}, mutation {change}");
        }
    }
}

#[test]
fn indexed_equality_preserves_duplicate_and_polarity_semantics() {
    let a: Vec<_> = (0..128).map(Lit::pos).collect();
    let mut b = a.iter().rev().copied().collect::<Vec<_>>();
    b.extend_from_slice(&a);
    assert!(equal(
        &a,
        &b,
        &mut RupExpansionState::<'_>::new(0, Some(caps()), &mut || true)
    )
    .unwrap());
    b.push(Lit::neg(1));
    assert!(!equal(
        &a,
        &b,
        &mut RupExpansionState::<'_>::new(0, Some(caps()), &mut || true)
    )
    .unwrap());
    assert!(!equal(
        &a,
        &a[1..],
        &mut RupExpansionState::<'_>::new(0, Some(caps()), &mut || true)
    )
    .unwrap());
}

#[test]
fn indexed_membership_respects_allocation_and_every_cancellation_boundary() {
    let a: Vec<_> = (0..32).map(Lit::pos).collect();
    let b = vec![Lit::neg(0)];
    let mut limits = caps();
    limits.max_bytes = 0;
    assert!(matches!(
        resolve_pair(
            &a,
            &b,
            0,
            &mut RupExpansionState::<'_>::new(0, Some(limits), &mut || true)
        ),
        Err(BvSolvedExportError::ResourceLimit {
            resource: "RUP expansion bytes",
            ..
        })
    ));
    let mut polls = 0;
    resolve_pair(
        &a,
        &b,
        0,
        &mut RupExpansionState::<'_>::new(0, Some(caps()), &mut || {
            polls += 1;
            true
        }),
    )
    .unwrap();
    for stop in 1..=polls {
        let mut calls = 0;
        let result = resolve_pair(
            &a,
            &b,
            0,
            &mut RupExpansionState::<'_>::new(0, Some(caps()), &mut || {
                calls += 1;
                calls != stop
            }),
        );
        assert_eq!(result, Err(BvSolvedExportError::Cancelled));
        assert_eq!(calls, stop);
    }
}

#[test]
fn indexed_subset_respects_duplicate_and_polarity_semantics() {
    let b: Vec<_> = (0..128).map(Lit::pos).collect();
    let mut a: Vec<_> = b[..64].iter().rev().copied().collect();
    a.extend_from_slice(&b[..8]);
    assert!(subset(
        &a,
        &b,
        &mut RupExpansionState::<'_>::new(0, Some(caps()), &mut || true)
    )
    .unwrap());
    a.push(Lit::neg(1));
    assert!(!subset(
        &a,
        &b,
        &mut RupExpansionState::<'_>::new(0, Some(caps()), &mut || true)
    )
    .unwrap());
    assert!(!subset(
        &b,
        &b[1..],
        &mut RupExpansionState::<'_>::new(0, Some(caps()), &mut || true)
    )
    .unwrap());
}
