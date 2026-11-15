// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::ArrayValue;
use ay_core::original_query::{FiniteAdmissionGrant, OriginalAdmission};
use ay_core::time::Instant;
use std::sync::Arc;
use std::time::Duration;

mod resources;

fn bv(n: u64, w: u32) -> ModelValue {
    ModelValue::bitvec(n.into(), w)
}
fn literal(n: u64) -> Constant {
    Constant::BitVec {
        value: n.into(),
        width: 8,
    }
}
fn base(default: u64, rows: &[(u64, u64)]) -> Arc<ArraySnapshot> {
    ArraySnapshot::finite(
        ArrayValue {
            default: bv(default, 8),
            store: rows.iter().map(|&(k, v)| (bv(k, 64), bv(v, 8))).collect(),
        },
        &ay_core::Sort::array(ay_core::Sort::bitvec(64), ay_core::Sort::bitvec(8)),
        &mut 1_000_000,
    )
    .expect("complete fixture")
}
fn range(dst: Arc<ArraySnapshot>, value: u64, lo: u64, hi: u64) -> Arc<ArraySnapshot> {
    ArraySnapshot::range_copy(
        dst,
        base(value, &[]),
        &bv(lo, 64),
        &bv(hi, 64),
        &bv(0, 64),
        &mut 1_000_000,
    )
    .expect("existing complete range fixture")
}
fn owner(end: Instant, work: u64, bytes: usize) -> OriginalAdmission {
    OriginalAdmission::new(
        FiniteAdmissionGrant::new(work, bytes),
        end,
        Arc::new(|| false),
    )
}
fn confirm(
    owner: &OriginalAdmission,
    target: &ArraySnapshot,
    dst: &ArraySnapshot,
    lo: u64,
    hi: u64,
    literal: &Constant,
) -> bool {
    owner
        .with_work(|work| {
            target
                .confirms_range_fill_with_progress(dst, lo, hi, literal, &mut |w, b| {
                    work.admit(w, b).is_ok()
                })
                .map_err(|_| work.refuse_exhaustion())
        })
        .expect("same owner")
}

#[test]
fn partial_huge_and_max_exclusive_fill_check_the_complete_frame() {
    let end = Instant::now() + Duration::from_secs(20);
    let owner = owner(end, 1_000_000, 128 * 1024 * 1024);
    let dst = base(0, &[(0, 7), (u64::MAX, 11)]);
    for hi in [3, u64::MAX] {
        let target = range(dst.clone(), 9, 1, hi);
        assert!(confirm(&owner, &target, &dst, 1, hi, &literal(9)));
        let wrong = ArraySnapshot::store(target, &bv(u64::MAX, 64), &bv(9, 8), &mut 1_000_000)
            .expect("wrong frame");
        assert!(!confirm(&owner, &wrong, &dst, 1, hi, &literal(9)));
    }
    assert!(Instant::now() < end);
}

#[test]
fn finite_and_nested_store_range_shapes_have_identical_whole_fill_truth() {
    let end = Instant::now() + Duration::from_secs(20);
    let owner = owner(end, 1_000_000, 128 * 1024 * 1024);
    let dst = base(0, &[(0, 7), (2, 8), (u64::MAX, 3)]);
    let target = base(0, &[(0, 7), (1, 9), (2, 9), (u64::MAX, 3)]);
    assert!(confirm(&owner, &target, &dst, 1, 3, &literal(9)));
    let nested = ArraySnapshot::store(
        range(dst.clone(), 9, 1, 3),
        &bv(2, 64),
        &bv(9, 8),
        &mut 1_000_000,
    )
    .expect("last write");
    assert!(confirm(&owner, &nested, &dst, 1, 3, &literal(9)));
    let wrong = base(1, &[(0, 7), (1, 9), (2, 9), (u64::MAX, 3)]);
    assert!(!confirm(&owner, &wrong, &dst, 1, 3, &literal(9)));
    assert!(Instant::now() < end);
}

#[test]
fn empty_reversed_fill_still_validates_destination_and_literal_domains() {
    let end = Instant::now() + Duration::from_secs(20);
    let owner = owner(end, 1_000_000, 128 * 1024 * 1024);
    let dst = base(7, &[(u64::MAX, 3)]);
    assert!(confirm(&owner, &dst, &dst, 3, 1, &literal(9)));
    assert!(!confirm(&owner, &base(8, &[]), &dst, 3, 1, &literal(9)));
    let invalid = Constant::BitVec {
        value: (-1).into(),
        width: 8,
    };
    assert!(dst
        .confirms_range_fill_with_progress(&dst, 3, 1, &invalid, &mut |_, _| Instant::now() < end)
        .is_err());
    assert!(Instant::now() < end);
}

#[test]
fn bool_and_bv128_literals_are_borrowed_without_numeric_reconstruction() {
    let end = Instant::now() + Duration::from_secs(20);
    let owner = owner(end, 1_000_000, 128 * 1024 * 1024);
    for (cell, datum, literal) in [
        (
            ay_core::Sort::Bool,
            ModelValue::Bool(true),
            Constant::Bool(true),
        ),
        (
            ay_core::Sort::bitvec(128),
            ModelValue::bitvec((num_bigint::BigInt::from(1u8) << 127) + 123, 128),
            Constant::BitVec {
                value: (num_bigint::BigInt::from(1u8) << 127) + 123,
                width: 128,
            },
        ),
    ] {
        let sort = ay_core::Sort::array(ay_core::Sort::bitvec(64), cell);
        let snapshot = ArraySnapshot::finite(
            ArrayValue {
                default: datum,
                store: Vec::new(),
            },
            &sort,
            &mut 1000,
        )
        .expect("complete");
        assert!(confirm(&owner, &snapshot, &snapshot, 1, u64::MAX, &literal));
    }
    assert!(Instant::now() < end);
}
