// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;
use crate::counted_storage::test_owner;

fn ordinary(s: &mut VSIDS, vars: &[usize], stage: ActivityStage) {
    let vals = vec![0; s.activities.len() * 2];
    match stage {
        ActivityStage::Chb => {
            s.chb_bump_batch(vars);
            s.chb_on_conflict();
        }
        ActivityStage::Evsids => s.batch_bump(vars, &vals, true),
        ActivityStage::DormantEvsids => {
            s.bump_evsids_score_dormant_batch(vars);
            for &var in vars {
                s.bump_vmtf_order_only(Variable(var as u32), &vals);
            }
        }
        ActivityStage::Vmtf => {
            let sorted: Vec<_> = vars.iter().map(|&v| (s.bump_order[v], v)).collect();
            s.batch_bump_queue_sorted(&sorted, &vals);
        }
    }
}

fn counted(
    s: &mut VSIDS,
    vars: &[usize],
    stage: ActivityStage,
    owner: &CountedAdmission,
) -> Result<()> {
    let vals = vec![0; s.activities.len() * 2];
    let sorted: Vec<_> = vars.iter().map(|&v| (s.bump_order[v], v)).collect();
    s.analysis_activity_counted(vars, &vals, &sorted, stage, owner)
}

fn exact(s: &VSIDS, expected: &VSIDS) {
    assert_eq!(format!("{s:?}"), format!("{expected:?}"));
    assert_eq!(
        s.heap_repair_scratch.capacity(),
        expected.heap_repair_scratch.capacity()
    );
    assert_eq!(
        s.heap_repair_order.capacity(),
        expected.heap_repair_order.capacity()
    );
    assert_eq!(
        s.heap_repair_stamp.capacity(),
        expected.heap_repair_stamp.capacity()
    );
    assert_eq!(
        s.chb_scores.as_ref().map(Vec::capacity),
        expected.chb_scores.as_ref().map(Vec::capacity)
    );
    assert_eq!(
        s.chb_last_conflict.as_ref().map(Vec::capacity),
        expected.chb_last_conflict.as_ref().map(Vec::capacity)
    );
}

#[test]
fn sparse_single_dense_and_duplicate_batches_preserve_entire_heap_and_capacity() {
    for vars in [vec![63], vec![62, 63], vec![63, 63, 62], (0..64).collect()] {
        let mut actual = VSIDS::new(64);
        let mut expected = actual.clone();
        ordinary(&mut expected, &vars, ActivityStage::Evsids);
        let owner = test_owner(10_000_000, 10_000_000);
        counted(&mut actual, &vars, ActivityStage::Evsids, &owner).unwrap();
        exact(&actual, &expected);
        assert!(owner.usage().unwrap().work_admitted > 0);
    }
}

#[test]
fn sparse_epoch_wrap_and_warm_capacity_are_identical() {
    let mut actual = VSIDS::new(128);
    let mut expected = VSIDS::new(128);
    ordinary(&mut actual, &[126, 127], ActivityStage::Evsids);
    ordinary(&mut expected, &[126, 127], ActivityStage::Evsids);
    actual.heap_repair_epoch = u32::MAX;
    expected.heap_repair_epoch = u32::MAX;
    ordinary(&mut expected, &[122, 125], ActivityStage::Evsids);
    counted(
        &mut actual,
        &[122, 125],
        ActivityStage::Evsids,
        &test_owner(10_000_000, 10_000_000),
    )
    .unwrap();
    exact(&actual, &expected);
    assert_eq!(actual.heap_repair_epoch, 1);
}

#[test]
fn real_rescale_heap_repair_and_deferred_queue_are_identical() {
    let mut actual = VSIDS::new(64);
    actual.increment = 2e100;
    let mut expected = actual.clone();
    ordinary(&mut expected, &[60, 63], ActivityStage::Evsids);
    counted(
        &mut actual,
        &[60, 63],
        ActivityStage::Evsids,
        &test_owner(10_000_000, 10_000_000),
    )
    .unwrap();
    exact(&actual, &expected);
    assert!(actual.increment < 10.0);
    assert!(actual.vmtf_deferred);
}

#[test]
fn loaded_dormant_and_lazy_chb_keep_exact_scores_counters_and_allocations() {
    for loaded in [false, true] {
        let mut actual = VSIDS::new(16);
        if loaded {
            actual.swap_chb_scores();
        }
        let mut expected = actual.clone();
        for stage in [
            ActivityStage::Chb,
            if loaded {
                ActivityStage::DormantEvsids
            } else {
                ActivityStage::Evsids
            },
        ] {
            ordinary(&mut expected, &[13, 15], stage);
            counted(
                &mut actual,
                &[13, 15],
                stage,
                &test_owner(10_000_000, 10_000_000),
            )
            .unwrap();
            exact(&actual, &expected);
        }
        assert_eq!(actual.chb_conflicts, 1);
    }
}

#[test]
fn queue_freeze_and_vmtf_relinks_keep_exact_state() {
    for freeze in [false, true] {
        for stage in [ActivityStage::Vmtf, ActivityStage::Evsids] {
            let mut actual = VSIDS::new(16);
            actual.queue_freeze = freeze;
            let mut expected = actual.clone();
            ordinary(&mut expected, &[13, 1, 15], stage);
            counted(
                &mut actual,
                &[13, 1, 15],
                stage,
                &test_owner(10_000_000, 10_000_000),
            )
            .unwrap();
            exact(&actual, &expected);
        }
    }
}

#[test]
fn every_work_cut_in_real_sparse_repair_is_terminal_without_fresh_grant() {
    let owner = test_owner(1_000_000, 1_000_000);
    counted(
        &mut VSIDS::new(32),
        &[30, 31],
        ActivityStage::Evsids,
        &owner,
    )
    .unwrap();
    let total = owner.usage().unwrap().work_admitted;
    for budget in 0..total {
        let owner = test_owner(budget, 1_000_000);
        let mut s = VSIDS::new(32);
        assert_eq!(
            counted(&mut s, &[30, 31], ActivityStage::Evsids, &owner),
            Err(CountedAdmissionError::WorkExhausted)
        );
        assert_eq!(
            owner.clone().check(),
            Err(CountedAdmissionError::WorkExhausted)
        );
        assert_eq!(
            counted(&mut s, &[30, 31], ActivityStage::Evsids, &owner),
            Err(CountedAdmissionError::WorkExhausted)
        );
    }
}

#[test]
fn every_storage_cut_in_sparse_growth_and_lazy_chb_is_terminal() {
    for stage in [ActivityStage::Evsids, ActivityStage::Chb] {
        let owner = test_owner(1_000_000, 1_000_000);
        counted(&mut VSIDS::new(32), &[30, 31], stage, &owner).unwrap();
        let total = owner.usage().unwrap().storage_admitted;
        assert!(total > 0);
        for storage in 0..total {
            let owner = test_owner(1_000_000, storage);
            assert_eq!(
                counted(&mut VSIDS::new(32), &[30, 31], stage, &owner),
                Err(CountedAdmissionError::StorageExhausted)
            );
            assert_eq!(owner.check(), Err(CountedAdmissionError::StorageExhausted));
        }
    }
}

#[test]
fn counter_overflow_refuses_before_scores_or_queue_change() {
    for stage in [
        ActivityStage::Chb,
        ActivityStage::Evsids,
        ActivityStage::Vmtf,
    ] {
        let mut s = VSIDS::new(4);
        if stage == ActivityStage::Chb {
            s.chb_conflicts = u64::MAX;
        } else {
            s.bump_counter = u64::MAX;
        }
        let before = format!("{s:?}");
        let owner = test_owner(1_000_000, 1_000_000);
        assert!(counted(&mut s, &[1], stage, &owner).is_err());
        assert_eq!(format!("{s:?}"), before);
        assert!(owner.check().is_err());
    }
}
