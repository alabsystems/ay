// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::ArrayValue;
use ay_core::original_query::{FiniteAdmissionGrant, OriginalAdmission, QueryError};
use ay_core::time::Instant;
use ay_core::Sort;
use std::sync::Arc;
use std::time::Duration;

mod resources;

fn bv(value: u64, width: u32) -> ModelValue {
    ModelValue::bitvec(value.into(), width)
}

fn base(default: u64, cells: &[(u64, u64)]) -> Arc<ArraySnapshot> {
    ArraySnapshot::finite(
        ArrayValue {
            default: bv(default, 8),
            store: cells.iter().map(|&(k, v)| (bv(k, 64), bv(v, 8))).collect(),
        },
        &Sort::array(Sort::bitvec(64), Sort::bitvec(8)),
        &mut 1_000_000,
    )
    .expect("complete typed fixture")
}

fn range(
    dst: Arc<ArraySnapshot>,
    src: Arc<ArraySnapshot>,
    lo: u64,
    hi: u64,
    start: u64,
) -> Arc<ArraySnapshot> {
    ArraySnapshot::range_copy(
        dst,
        src,
        &bv(lo, 64),
        &bv(hi, 64),
        &bv(start, 64),
        &mut 1_000_000,
    )
    .expect("whole old captures")
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
    src: &ArraySnapshot,
    lo: u64,
    hi: u64,
    start: u64,
) -> bool {
    owner
        .with_work(|work| {
            target
                .confirms_range_copy_with_progress(dst, src, lo, hi, start, &mut |w, b| {
                    work.admit(w, b).is_ok()
                })
                .map_err(|_| work.refuse_exhaustion())
        })
        .expect("same complete original owner")
}

#[test]
fn bool_and_full_bv128_cells_use_complete_borrowed_values() {
    let end = Instant::now() + Duration::from_secs(20);
    let owner = owner(end, 1_000_000, 128 * 1024 * 1024);
    for (sort, a, b) in [
        (Sort::Bool, ModelValue::Bool(false), ModelValue::Bool(true)),
        (
            Sort::bitvec(128),
            ModelValue::bitvec(0.into(), 128),
            ModelValue::bitvec((BigInt::from(1u8) << 127) + 123, 128),
        ),
    ] {
        let sort = Sort::array(Sort::bitvec(64), sort);
        let dst = ArraySnapshot::finite(
            ArrayValue {
                default: a,
                store: Vec::new(),
            },
            &sort,
            &mut 1000,
        )
        .expect("dst");
        let src = ArraySnapshot::finite(
            ArrayValue {
                default: b,
                store: Vec::new(),
            },
            &sort,
            &mut 1000,
        )
        .expect("src");
        let target = range(dst.clone(), src.clone(), 1, u64::MAX, 0);
        assert!(confirm(&owner, &target, &dst, &src, 1, u64::MAX, 0));
    }
    assert!(Instant::now() < end);
}

#[test]
fn differently_shaped_finite_and_range_models_confirm_whole_copy() {
    let end = Instant::now() + Duration::from_secs(20);
    let owner = owner(end, 1_000_000, 128 * 1024 * 1024);
    let dst = base(0, &[(0, 7), (0, 7)]);
    let src = base(0, &[(0, 9), (u64::MAX, 0), (0, 9)]);
    let target = base(0, &[(0, 7), (1, 9)]);
    assert!(confirm(&owner, &target, &dst, &src, 1, 3, 0));
    let structured = range(dst.clone(), src.clone(), 1, 3, 0);
    assert!(confirm(&owner, &structured, &dst, &src, 1, 3, 0));
    assert!(owner.check().is_ok());
    assert!(Instant::now() < end);
}

#[test]
fn modular_preimages_max_singletons_and_prewrite_aliases_are_complete() {
    let end = Instant::now() + Duration::from_secs(20);
    let owner = owner(end, 1_000_000, 128 * 1024 * 1024);
    let old = base(7, &[(0, 9), (u64::MAX, 11)]);
    let target = base(7, &[(0, 9), (1, 11), (2, 9), (u64::MAX, 11)]);
    assert!(confirm(&owner, &target, &old, &old, 1, 3, u64::MAX));
    assert!(confirm(&owner, &old, &old, &old, u64::MAX, 0, 42));
    assert_eq!(preimage(N, 1, u64::MAX), 2);
    assert_eq!(u128::from(u64::MAX) + 1, N);
    assert!(Instant::now() < end);
}

#[test]
fn huge_nested_ranges_refine_without_enumerating_the_carrier() {
    let end = Instant::now() + Duration::from_secs(20);
    let owner = owner(end, 1_000_000, 128 * 1024 * 1024);
    let dst = base(7, &[(u64::MAX, 1)]);
    let src = range(base(9, &[]), base(11, &[(0, 13)]), 2, 4, 0);
    let target = range(dst.clone(), src.clone(), 1, 1 << 63, u64::MAX);
    assert!(confirm(&owner, &target, &dst, &src, 1, 1 << 63, u64::MAX));
    assert!(owner.check().is_ok());
    assert!(Instant::now() < end);
}

#[test]
fn a_far_wrong_cell_or_uncovered_default_never_becomes_confirmation() {
    let end = Instant::now() + Duration::from_secs(20);
    let owner = owner(end, 1_000_000, 128 * 1024 * 1024);
    let dst = base(7, &[]);
    let src = base(9, &[]);
    let expected = range(dst.clone(), src.clone(), 1, 1 << 63, 0);
    let wrong = ArraySnapshot::store(expected, &bv(1 << 62, 64), &bv(10, 8), &mut 1_000_000)
        .expect("actual wrong whole assignment");
    assert!(!confirm(&owner, &wrong, &dst, &src, 1, 1 << 63, 0));
    assert!(!confirm(&owner, &base(8, &[(0, 7)]), &dst, &src, 3, 1, 0));
    assert!(Instant::now() < end);
}

#[test]
fn small_complete_literal_oracle_covers_every_copy_cell_and_default_region() {
    let end = Instant::now() + Duration::from_secs(20);
    let owner = owner(end, 1_000_000, 128 * 1024 * 1024);
    for (lo, hi, start) in [(1, 3, 0), (2, 5, u64::MAX), (5, 1, 0)] {
        let dst = base(0, &[(0, 7), (2, 8), (u64::MAX, 3)]);
        let src = base(0, &[(0, 9), (1, 10), (u64::MAX, 11)]);
        let expected = range(dst.clone(), src.clone(), lo, hi, start);
        let mut rows = Vec::new();
        for i in (0..8).chain(std::iter::once(u64::MAX)) {
            let ModelValue::BitVec { value, width: 8 } =
                expected.read(&bv(i, 64), &mut 1000).expect("oracle")
            else {
                panic!("byte");
            };
            rows.push((i, value.to_u64().expect("canonical byte")));
        }
        let flat = base(0, &rows);
        assert!(confirm(&owner, &flat, &dst, &src, lo, hi, start));
    }
    assert!(Instant::now() < end);
}
