// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::counted_storage::test_owner;
use ay_core::debug_channel::misc_cli_flags_with;

fn construct(owner: &CountedAdmission) -> Result<InprocessingEngines> {
    owner.with_work(|_| Ok(InprocessingEngines::try_new_counted(7, owner)))?
}

#[test]
fn exact_and_one_short_budgets_cover_nested_engine_construction() {
    let flags = misc_cli_flags_with(|flags| flags.sat_mem_probe = false);
    let _flags = ay_core::misc_test_override::set(flags);
    let baseline = test_owner(100_000, 100_000);
    drop(construct(&baseline).unwrap());
    let receipt = baseline.usage().unwrap();
    for (work, storage, error) in [
        (receipt.work_admitted, receipt.storage_admitted, None),
        (
            receipt.work_admitted - 1,
            receipt.storage_admitted,
            Some(CountedAdmissionError::WorkExhausted),
        ),
        (
            receipt.work_admitted,
            receipt.storage_admitted - 1,
            Some(CountedAdmissionError::StorageExhausted),
        ),
    ] {
        let owner = test_owner(work, storage);
        assert_eq!(construct(&owner).err(), error);
        if let Some(error) = error {
            assert_eq!(construct(&owner).err(), Some(error));
            assert_eq!(owner.check(), Err(error));
        } else {
            assert_eq!(owner.usage().unwrap().work_remaining, 0);
            assert_eq!(owner.usage().unwrap().storage_remaining, 0);
        }
    }
}

#[test]
fn stopped_partial_engine_construction_cannot_revive() {
    use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
    use std::sync::Arc;
    let flags = misc_cli_flags_with(|flags| flags.sat_mem_probe = false);
    let _flags = ay_core::misc_test_override::set(flags);
    let enabled = Arc::new(AtomicBool::new(true));
    let observer_enabled = Arc::clone(&enabled);
    let calls = Arc::new(AtomicUsize::new(0));
    let observed_calls = Arc::clone(&calls);
    let owner = CountedAdmission::new(
        ay_core::original_query::FiniteAdmissionGrant::new(100_000, 100_000),
        None,
        Arc::new(move || {
            let count = observed_calls.fetch_add(1, Ordering::SeqCst);
            observer_enabled.load(Ordering::SeqCst) && count >= 30
        }),
    )
    .unwrap();
    let error = construct(&owner).err().unwrap();
    assert!(owner.usage().unwrap().work_admitted > 0);
    enabled.store(false, Ordering::SeqCst);
    assert_eq!(construct(&owner).err(), Some(error));
    assert_eq!(owner.check(), Err(error));
}

#[test]
fn memory_probe_requires_its_own_diagnostic_coverage() {
    let flags = misc_cli_flags_with(|flags| flags.sat_mem_probe = true);
    let _flags = ay_core::misc_test_override::set(flags);
    let owner = test_owner(100_000, 100_000);
    let error = construct(&owner).err().unwrap();
    assert!(matches!(error, CountedAdmissionError::Original(_)));
    assert_eq!(owner.usage().unwrap().work_admitted, 1);
    assert_eq!(
        owner.usage().unwrap().storage_admitted,
        std::mem::size_of::<InprocessingEngines>()
    );
    assert_eq!(owner.check(), Err(error));
}
