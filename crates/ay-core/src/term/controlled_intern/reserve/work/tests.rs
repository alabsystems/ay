// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::original_query::{QueryError, WorkBudget};
use std::ops::ControlFlow;

mod tables;

fn bound(buckets: usize, group: usize, len: usize) -> Result<usize> {
    checked_scans(33 * buckets + group, len, 32, 8)
}

#[test]
fn confirmed_128_bucket_growth_keeps_128_units_and_original_million_limit() {
    for (group, expected) in [(4, 935_936), (8, 735_232), (16, 634_880)] {
        let work = product(bound(128, group, 112).expect("valid primary layout"), 128)
            .expect("bounded work");
        assert_eq!(work, expected);
        assert!(work < 1_048_576);
    }
}

#[test]
fn closed_form_counts_every_group_through_all_collision_occupancies() {
    for group in [4, 8, 16] {
        for len in 0..=512 {
            let reference: usize = (0..len).map(|j| j / group + 1).sum();
            assert_eq!(group_probes(len, group), Ok(reference));
        }
    }
}

#[test]
fn small_tables_pay_an_additional_correction_group_for_each_item() {
    for group in [8, 16] {
        for len in 0..=3 {
            assert_eq!(bound(4, group, len), Ok(12 + 96 + 4 * len + 32 * len));
        }
    }
    assert_eq!(bound(4, 4, 3), Ok(12 + 96 + 6 + 96));
}

#[test]
fn empty_singleton_prices_the_fallible_first_allocation() {
    assert_eq!(checked_scans(0, 0, 32, 8), Ok(100));
    assert_eq!(checked_scans(0, 1, 32, 8), Err(limit()));
}

#[test]
fn malformed_or_foreign_layouts_refuse_instead_of_guessing_group_width() {
    for allocation in [1, 33, 34, 33 * 3 + 8, 33 * 12 + 8, 33 * 128 + 7] {
        assert_eq!(checked_scans(allocation, 0, 32, 8), Err(limit()));
    }
    assert_eq!(checked_scans(33 * 128 + 8, 112, 24, 8), Err(limit()));
    assert_eq!(checked_scans(33 * 128 + 8, 112, 32, 16), Err(limit()));
}

#[test]
fn impossible_live_counts_and_layout_overflow_are_typed_refusals() {
    assert_eq!(bound(4, 8, 4), Err(limit()));
    assert_eq!(bound(8, 8, 8), Err(limit()));
    assert_eq!(bound(128, 8, 113), Err(limit()));
    assert_eq!(checked_scans(usize::MAX, 0, 32, 8), Err(limit()));
    assert_eq!(group_probes(usize::MAX, 4), Err(limit()));
    assert_eq!(group_probes(1, 0), Err(limit()));
}

#[test]
fn tombstone_inplace_and_resize_keep_bulk_scan_hash_and_move_costs() {
    for group in [4, 8, 16] {
        for len in [0, 1, 55, 56, 112] {
            let expected =
                3 * 128 + 96 + 2 * (0..len).map(|j| j / group + 1).sum::<usize>() + 32 * len;
            assert_eq!(bound(128, group, len), Ok(expected));
        }
    }
}

#[test]
fn worst_collision_work_remains_quadratic_not_average_case() {
    for group in [4, 8, 16] {
        let a = group_probes(256, group).expect("finite");
        let b = group_probes(512, group).expect("finite");
        assert!(b > 3 * a);
    }
}

#[test]
fn original_work_one_short_refuses_and_same_owner_cannot_retry() {
    let work = product(bound(128, 8, 112).expect("primary layout"), 128).expect("finite charge");
    let mut checkpoint = || ControlFlow::Continue(());
    let grant = u64::try_from(work - 1).expect("fixture grant fits");
    let mut budget = WorkBudget::new(grant, &mut checkpoint);
    assert_eq!(budget.admit(work, 716_800), Err(QueryError::Exhausted));
    assert_eq!(budget.charge(0), Err(QueryError::Exhausted));
    assert_eq!(budget.admit(work, 716_800), Err(QueryError::Exhausted));
}

#[test]
fn exact_original_work_consumes_only_the_preexisting_grant() {
    let work = product(bound(128, 8, 112).expect("primary layout"), 128).expect("finite charge");
    let mut checkpoint = || ControlFlow::Continue(());
    let mut budget = WorkBudget::new(u64::try_from(work).expect("fixture grant"), &mut checkpoint);
    assert_eq!(budget.admit(work, 716_800), Ok(()));
    assert_eq!(budget.charge(0), Ok(()));
    assert_eq!(budget.charge(1), Err(QueryError::Exhausted));
}
