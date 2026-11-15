// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Keep owned callback destruction outside any active operation unwind.

use super::*;
use ay_core::original_query::OriginalAdmissionError;
use std::any::Any;
use std::panic::{catch_unwind, AssertUnwindSafe};

pub(super) fn check(encoder: &CountedBvEncoder<'_>) -> Result<()> {
    // The encoder is only borrowed: even an entry-poll panic cannot destroy
    // its last callback while the operation itself is unwinding.
    caught(&encoder.owner, || encoder.check())
}

pub(super) fn finish(encoder: CountedBvEncoder<'_>) -> Result<()> {
    let owner = encoder.owner.clone();
    let guard = encoder.solver.encoding_guard();
    let mut pending = Some(encoder);
    // Neither closure owns the encoder or its final guard. with_work can
    // refuse before entering its own catch boundary, leaving pending intact.
    let operation = caught(&owner, || {
        owner.with_work(|_| {
            Ok((|| {
                owner.admit(1, 0)?;
                poll(&owner, &guard)?;
                drop(pending.take());
                poll(&owner, &guard)
            })())
        })?
    });
    // Cleanup was prepaid during construction. It still runs after refusal,
    // without a fresh admission, and never during an operation's unwind.
    let discarded = caught(&owner, || {
        drop(pending.take());
        Ok(())
    });
    let retained = caught(&owner, || poll(&owner, &guard));
    let released = caught(&owner, || {
        drop(guard);
        Ok(())
    });
    let final_owner = caught(&owner, || {
        owner.check()?;
        Ok(())
    });
    // All disposal has finished. Prefer the original owner's FIRST cause,
    // including an earlier work/storage refusal over a later destructor panic.
    final_owner?;
    operation?;
    discarded?;
    retained?;
    released
}

fn poll(owner: &CountedAdmission, guard: &BvEncodingGuard) -> Result<()> {
    if !guard.open() {
        return Err(CountedBvError::Stopped(owner.refuse(
            CountedAdmissionError::Original(OriginalAdmissionError::ObserverStopped),
        )));
    }
    owner.check()?;
    Ok(())
}

// Callers keep owned callback-bearing state outside this boundary, borrowing
// it for operations and disposing of it through finish after any refusal.
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
            Err(CountedBvError::Stopped(first))
        }
    }
}

fn dispose_payload(mut payload: Box<dyn Any + Send>) {
    // A custom panic payload can itself panic on drop. Drain each replacement
    // outside active unwinding; do not leak it or double-panic a callback.
    // As with callbacks, arbitrary nonterminating destructors cannot be bounded.
    loop {
        match catch_unwind(AssertUnwindSafe(|| drop(payload))) {
            Ok(()) => return,
            Err(next) => payload = next,
        }
    }
}
