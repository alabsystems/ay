// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::super::{Admission, TermStore};
use super::*;
use crate::original_query::{QueryError, StopReason, WorkBudget};
use std::ops::ControlFlow;

mod resources;
mod tables;

fn bound(buckets: usize, group: usize, len: usize) -> Result<usize> {
    checked_work(33 * buckets + group, len, 32, 8)
}

#[test]
fn complete_allocated_domain_and_fixed_header_have_exact_prices() {
    for (group, expected) in [(4, 8192), (8, 6144), (16, 5120)] {
        assert_eq!(bound(128, group, 112), Ok(expected));
    }
}

#[test]
fn empty_singleton_has_full_header_and_one_static_group() {
    assert_eq!(checked_work(0, 0, 32, 8), Ok(640));
    assert_eq!(checked_work(0, 1, 32, 8), Err(limit()));
}

#[test]
fn small_padded_shapes_pay_both_mirror_candidates_and_correction() {
    for group in [8, 16] {
        for len in 0..=3 {
            assert_eq!(bound(4, group, len), Ok(768 + 64 * len));
        }
    }
    assert_eq!(bound(4, 4, 3), Ok(736));
}

#[test]
fn low_live_count_never_shortens_the_tombstone_probe_partition() {
    for group in [4, 8, 16] {
        let groups = 128 / group;
        for len in 0..=112 {
            assert_eq!(bound(128, group, len), Ok(512 + 128 * groups + 32 * len));
        }
    }
    assert_eq!(bound(128, 8, 32), Ok(3584));
}

#[test]
fn foreign_layout_or_abi_refuses_instead_of_guessing_probe_shape() {
    for allocation in [1, 33, 34, 33 * 3 + 8, 33 * 12 + 8, 33 * 128 + 7] {
        assert_eq!(checked_work(allocation, 0, 32, 8), Err(limit()));
    }
    assert_eq!(checked_work(33 * 128 + 8, 0, 24, 8), Err(limit()));
    assert_eq!(checked_work(33 * 128 + 8, 0, 32, 16), Err(limit()));
}

#[test]
fn impossible_live_counts_and_fee_overflow_are_typed_refusals() {
    assert_eq!(bound(4, 8, 4), Err(limit()));
    assert_eq!(bound(8, 8, 8), Err(limit()));
    assert_eq!(bound(128, 8, 113), Err(limit()));
    assert_eq!(checked_work(usize::MAX, 0, 32, 8), Err(limit()));
    let buckets = 1usize << (usize::BITS - 6);
    assert_eq!(checked_work(33 * buckets + 4, 0, 32, 8), Err(limit()));
}

#[test]
fn triangular_groups_partition_every_allocated_bucket_exactly_once() {
    for group in [4, 8, 16] {
        for buckets in [16, 32, 64, 128, 256, 512] {
            for start in 0..buckets {
                let mut visits = vec![0usize; buckets];
                let (mut pos, mut stride) = (start, 0);
                for _ in 0..buckets / group {
                    for lane in 0..group {
                        visits[(pos + lane) & (buckets - 1)] += 1;
                    }
                    stride += group;
                    pos = (pos + stride) & (buckets - 1);
                }
                assert!(visits.iter().all(|&count| count == 1));
            }
        }
    }
}
