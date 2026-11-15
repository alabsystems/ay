// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Owned input/solver state stays OUTSIDE operation and entry-poll unwinding.

use super::*;
use ay_core::original_query::OriginalAdmissionError;
use std::any::Any;
use std::panic::{catch_unwind, AssertUnwindSafe};

pub(super) fn caught<T>(
    owner: &CountedAdmission,
    operation: impl FnOnce() -> Result<T>,
) -> Result<T> {
    match catch_unwind(AssertUnwindSafe(operation)) {
        Ok(result) => result,
        Err(payload) => {
            let first = owner.refuse(CountedAdmissionError::Original(
                OriginalAdmissionError::OperationPanicked,
            ));
            dispose_payload(payload);
            Err(first)
        }
    }
}

fn dispose_payload(mut payload: Box<dyn Any + Send>) {
    // A destructor may itself panic. Drain finite replacement chains only
    // outside active unwinding. Arbitrary nonterminating user code is not a
    // bounded solver operation, just as for the original owner callback.
    loop {
        match catch_unwind(AssertUnwindSafe(|| drop(payload))) {
            Ok(()) => return,
            Err(next) => payload = next,
        }
    }
}

/// Release the final local owner outside unwinding as well. If this really is
/// its last handle, even a hostile observer-capture Drop cannot escape. A live
/// returned solver retains that same ledger, so this cannot destroy its owner.
pub(super) fn release<T>(owner: CountedAdmission, result: Result<T>) -> Result<T> {
    let first = owner.usage().ok().and_then(|usage| usage.refusal);
    match catch_unwind(AssertUnwindSafe(|| drop(owner))) {
        Ok(()) => result,
        Err(payload) => {
            dispose_payload(payload);
            match result {
                Err(error) => Err(error),
                Ok(_) => Err(first.unwrap_or(CountedAdmissionError::Original(
                    OriginalAdmissionError::OperationPanicked,
                ))),
            }
        }
    }
}
