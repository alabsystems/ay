// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! One cumulative value-work allowance for acquisition and retained entries.

use super::{AccessStep, ModelValue, Slot, WitnessBudget};

/// Charge the complete entry before retaining it, including every inner key.
/// Refusal is transactional, like the existing outer-index/value accounting.
pub(in crate::residual) fn account_entry_values(
    value_work: &mut usize,
    index: &ModelValue,
    value: &ModelValue,
    slot: &Slot,
) -> bool {
    let mut candidate = WitnessBudget {
        value_work: *value_work,
        ..WitnessBudget::default()
    };
    if !candidate.account_value(index) || !candidate.account_value(value) {
        return false;
    }
    if let Slot::Access(path) = slot {
        if path.len() > crate::residual::MAX_CLASSIFY_DEPTH {
            return false;
        }
        for step in path {
            if let AccessStep::Index(key) = step {
                if !candidate.account_value(key) {
                    return false;
                }
            }
        }
    }
    *value_work = candidate.value_work;
    true
}

/// Debit a parser-acquired inner key before retaining its owned value.
/// Entry admission separately charges its persistent batch. Neither phase
/// resets the allowance; the evaluator callback retains its existing bounds.
pub(in crate::residual) fn account_path_index(value_work: &mut usize, index: &ModelValue) -> bool {
    let mut candidate = WitnessBudget {
        value_work: *value_work,
        ..WitnessBudget::default()
    };
    if !candidate.account_value(index) {
        return false;
    }
    *value_work = candidate.value_work;
    true
}

#[cfg(test)]
mod tests;
