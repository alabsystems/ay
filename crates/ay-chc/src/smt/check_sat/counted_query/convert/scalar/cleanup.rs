// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Retain owned circuit state outside operation unwinding, like BV cleanup.

use super::*;
use ay_core::original_query::{CountedAdmissionError, OriginalAdmissionError};
use std::any::Any;
use std::panic::{catch_unwind, AssertUnwindSafe};

pub(super) fn invoke<T>(
    owner: &CountedAdmission,
    operation: impl FnOnce() -> Result<T>,
) -> Result<T> {
    let result = catch_unwind(AssertUnwindSafe(|| owner.with_work(|_| Ok(operation()))));
    match result {
        Ok(result) => result.map_err(Error::from)?,
        Err(payload) => {
            let first = owner.refuse(CountedAdmissionError::Original(
                OriginalAdmissionError::OperationPanicked,
            ));
            dispose_payload(payload);
            Err(Error::Stopped(first))
        }
    }
}

fn dispose_payload(mut payload: Box<dyn Any + Send>) {
    // A custom panic payload may itself panic on drop. Drain replacement
    // payloads outside active unwinding without leaking the original state.
    // Arbitrary nonterminating callback/destructor code cannot be bounded.
    loop {
        match catch_unwind(AssertUnwindSafe(|| drop(payload))) {
            Ok(()) => return,
            Err(next) => payload = next,
        }
    }
}
