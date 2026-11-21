// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use num_traits::ToPrimitive;

fn bv(value: u64, width: u32) -> ModelValue {
    ModelValue::bitvec(value.into(), width)
}

fn base(default: u64, cells: &[(u64, u64)]) -> Arc<ArraySnapshot> {
    ArraySnapshot::finite(
        ArrayValue {
            default: bv(default, 8),
            store: cells.iter().map(|&(i, v)| (bv(i, 64), bv(v, 8))).collect(),
        },
        &Sort::array(Sort::bitvec(64), Sort::bitvec(8)),
        &mut 10_000,
    )
    .expect("typed complete base")
}

fn read(snapshot: &ArraySnapshot, index: u64) -> u64 {
    let ModelValue::BitVec { value, width: 8 } = snapshot
        .read(&bv(index, 64), &mut 1000)
        .expect("complete read")
    else {
        panic!("typed cell")
    };
    value.to_u64().expect("byte")
}

#[test]
fn enormous_range_is_one_full_function_and_prints_closed_captures() {
    let dst = base(7, &[]);
    let src = base(9, &[]);
    let mut work = 1000;
    let value = ArraySnapshot::range_copy(
        dst.clone(),
        src.clone(),
        &bv(1, 64),
        &bv(1 << 60, 64),
        &bv(0, 64),
        &mut work,
    )
    .expect("huge range");
    assert_eq!(work, 999, "no work proportional to interval cardinality");
    assert_eq!(read(&value, 0), 7);
    assert_eq!(read(&value, 1), 9);
    assert_eq!(read(&value, (1 << 60) - 1), 9);
    assert_eq!(read(&value, 1 << 60), 7);
    let same = ArraySnapshot::range_copy(
        dst,
        src,
        &bv(1, 64),
        &bv(1 << 60, 64),
        &bv(0, 64),
        &mut work,
    )
    .expect("independent full program");
    assert!(value
        .same_function(&same, &mut work)
        .expect("whole function comparison"));
    let output = value.to_smtlib(&mut 10_000).expect("closed model");
    assert!(output.contains("lambda"));
    assert!(output.contains("bv1152921504606846976 64"));
    assert!(output.contains("bv9 8"));
    assert!(output.contains("bv7 8"));
    assert!(output.len() < 1000);
}

#[test]
fn aliased_old_source_survives_new_writes() {
    let old = base(0, &[(0, 7), (1, 9)]);
    let written = ArraySnapshot::range_copy(
        old.clone(),
        old.clone(),
        &bv(1, 64),
        &bv(3, 64),
        &bv(0, 64),
        &mut 1000,
    )
    .expect("old captures");
    let later = ArraySnapshot::store(written.clone(), &bv(0, 64), &bv(42, 8), &mut 1000)
        .expect("later store");
    assert_eq!(read(&old, 0), 7);
    assert_eq!(read(&written, 1), 7);
    assert_eq!(read(&written, 2), 9);
    assert_eq!(read(&later, 1), 7);
    assert_eq!(read(&later, 0), 42);
}

#[test]
fn empty_and_reversed_unsigned_intervals_preserve_every_read() {
    let dst = base(7, &[(2, 42)]);
    let src = base(9, &[]);
    for (lo, hi) in [(2, 2), (3, 1), (u64::MAX, 0)] {
        let value = ArraySnapshot::range_copy(
            dst.clone(),
            src.clone(),
            &bv(lo, 64),
            &bv(hi, 64),
            &bv(0, 64),
            &mut 1000,
        )
        .expect("empty range");
        for index in [0, 1, 2, 3, u64::MAX] {
            assert_eq!(read(&value, index), read(&dst, index));
        }
    }
}

#[test]
fn source_offset_is_exact_modular_bv64() {
    let value = ArraySnapshot::range_copy(
        base(7, &[]),
        base(9, &[(u64::MAX, 11), (0, 12)]),
        &bv(1, 64),
        &bv(3, 64),
        &bv(u64::MAX, 64),
        &mut 1000,
    )
    .expect("modular range");
    assert_eq!(read(&value, 1), 11);
    assert_eq!(read(&value, 2), 12);
    assert_eq!(read(&value, 3), 7);
}

#[test]
fn program_mismatch_is_never_disequality_evidence() {
    let a = ArraySnapshot::range_copy(
        base(7, &[]),
        base(7, &[]),
        &bv(1, 64),
        &bv(3, 64),
        &bv(0, 64),
        &mut 1000,
    )
    .expect("program");
    assert!(!a
        .same_function(&base(7, &[]), &mut 1000)
        .expect("no structural proof"));
    assert_eq!(
        a.equality_with_stop(&base(7, &[]), &mut 1000, &mut || false)
            .expect("comparison"),
        None
    );
    assert_eq!(
        read(&a, 2),
        7,
        "these different programs actually denote equal arrays"
    );
}

#[test]
fn wrong_sorts_work_exhaustion_and_output_allocation_decline() {
    assert!(ArraySnapshot::range_copy(
        base(0, &[]),
        base(1, &[]),
        &bv(1, 32),
        &bv(3, 64),
        &bv(0, 64),
        &mut 1000
    )
    .is_err());
    assert!(ArraySnapshot::range_copy(
        base(0, &[]),
        base(1, &[]),
        &bv(1, 64),
        &bv(3, 64),
        &bv(0, 64),
        &mut 0
    )
    .is_err());
    assert!(base(7, &[]).to_smtlib(&mut 1).is_err());
    let many = ArrayValue {
        default: bv(0, 8),
        store: (0..256).map(|i| (bv(i, 64), bv(1, 8))).collect(),
    };
    assert!(ArraySnapshot::finite(
        many,
        &Sort::array(Sort::bitvec(64), Sort::bitvec(8)),
        &mut 64
    )
    .is_err());
}

#[test]
fn nested_snapshots_have_a_hard_depth_limit() {
    let mut value = base(0, &[]);
    let source = base(1, &[]);
    for _ in 1..64 {
        value = ArraySnapshot::range_copy(
            value,
            source.clone(),
            &bv(1, 64),
            &bv(3, 64),
            &bv(0, 64),
            &mut 1000,
        )
        .expect("bounded depth");
    }
    assert!(ArraySnapshot::range_copy(
        value,
        source,
        &bv(1, 64),
        &bv(3, 64),
        &bv(0, 64),
        &mut 1000
    )
    .is_err());
}

#[test]
fn original_stop_callback_is_polled_during_read_equality_and_printing() {
    let destination = base(7, &[(0, 8), (1, 9)]);
    let source = base(3, &[(0, 4)]);
    let snapshot = ArraySnapshot::range_copy(
        Arc::clone(&destination),
        source,
        &bv(1, 64),
        &bv(1 << 60, 64),
        &bv(0, 64),
        &mut 10_000,
    )
    .expect("compact full function");
    let mut calls = 0;
    assert!(snapshot
        .read_with_stop(&bv(1, 64), &mut 10_000, &mut || {
            calls += 1;
            calls >= 2
        })
        .is_err());
    let mut calls = 0;
    assert!(snapshot
        .same_function_with_stop(&snapshot, &mut 10_000, &mut || {
            calls += 1;
            calls >= 2
        })
        .is_err());
    let mut calls = 0;
    assert!(snapshot
        .to_smtlib_with_stop(&mut 10_000, &mut || {
            calls += 1;
            calls >= 2
        })
        .is_err());
}
