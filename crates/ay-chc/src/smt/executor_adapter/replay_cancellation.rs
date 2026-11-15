// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Owned, attempt-local observation of caller cancellation, never authority.

use crate::CancellationToken;
use std::sync::{
    atomic::{AtomicBool, Ordering},
    Arc,
};

/// Retains the complete linked-token snapshot, including inherited parents.
/// Every clone shares one sticky observation for this replay attempt. Later
/// caller resets cannot resume an attempt that has already observed refusal.
/// Links added to the caller token after construction are not retroactive,
/// matching `CancellationToken::clone`; link parents before starting replay.
#[derive(Clone)]
pub(crate) struct ReplayCancellation {
    token: CancellationToken,
    observed: Arc<AtomicBool>,
}

impl ReplayCancellation {
    pub(crate) fn new(token: &CancellationToken) -> Self {
        let token = token.clone();
        let observed = Arc::new(AtomicBool::new(token.is_cancelled()));
        Self { token, observed }
    }

    pub(crate) fn is_cancelled(&self) -> bool {
        // This flag records only refusal, not synchronization of other data.
        // It is never cleared and does not modify the caller or any parent.
        if self.observed.load(Ordering::Relaxed) || self.token.is_cancelled() {
            self.observed.store(true, Ordering::Relaxed);
            true
        } else {
            false
        }
    }
}

#[cfg(test)]
mod tests;
