// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::residual::witness::MAX_WITNESS_VALUE_WORK;

#[test]
fn acquisition_and_retention_debit_the_same_remaining_allowance() {
    let key = ModelValue::Str("nested-key".repeat(20));
    let index = ModelValue::Bool(false);
    let value = ModelValue::Bool(true);
    let slot = Slot::Access(vec![AccessStep::Index(key.clone())]);
    let mut acquired = 0;
    assert!(account_path_index(&mut acquired, &key));
    let mut full = acquired;
    assert!(account_entry_values(&mut full, &index, &value, &slot));
    assert_eq!(full, 2 * acquired + 2);
    for deficit in [0, 1] {
        let mut remaining = MAX_WITNESS_VALUE_WORK - full + deficit;
        assert!(account_path_index(&mut remaining, &key));
        let before_entry = remaining;
        assert_eq!(
            account_entry_values(&mut remaining, &index, &value, &slot),
            deficit == 0
        );
        assert_eq!(
            remaining,
            if deficit == 0 {
                MAX_WITNESS_VALUE_WORK
            } else {
                before_entry
            }
        );
    }
}

#[test]
fn oversized_inner_payload_refuses_transactionally_and_fresh_retry_works() {
    let key = ModelValue::Str("x".repeat(MAX_WITNESS_VALUE_WORK));
    let mut spent = 7;
    assert!(!account_path_index(&mut spent, &key));
    assert_eq!(spent, 7);
    let slot = Slot::Access(vec![AccessStep::Index(key)]);
    assert!(!account_entry_values(
        &mut spent,
        &ModelValue::Bool(false),
        &ModelValue::Bool(true),
        &slot,
    ));
    assert_eq!(spent, 7);
    assert!(account_path_index(&mut spent, &ModelValue::Bool(true)));
    assert_eq!(spent, 8);
}

#[test]
fn malformed_overdepth_access_is_not_retained_as_a_small_entry() {
    let slot = Slot::Access(vec![
        AccessStep::Index(ModelValue::Bool(false));
        crate::residual::MAX_CLASSIFY_DEPTH + 1
    ]);
    let mut spent = 0;
    assert!(!account_entry_values(
        &mut spent,
        &ModelValue::Bool(false),
        &ModelValue::Bool(true),
        &slot,
    ));
    assert_eq!(spent, 0);
}
