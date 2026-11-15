// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::time::Duration;

mod concurrent;
mod counted;
mod limits;
mod observer;

fn end() -> Instant {
    Instant::now() + Duration::from_secs(20)
}

fn healthy(work: u64, bytes: usize) -> OriginalAdmission {
    OriginalAdmission::new(
        FiniteAdmissionGrant::new(work, bytes),
        end(),
        Arc::new(|| false),
    )
}

fn stopped_flag(work: u64, bytes: usize) -> (OriginalAdmission, Arc<AtomicBool>) {
    let flag = Arc::new(AtomicBool::new(false));
    let observed = Arc::clone(&flag);
    let owner = OriginalAdmission::new(
        FiniteAdmissionGrant::new(work, bytes),
        end(),
        Arc::new(move || observed.load(Ordering::SeqCst)),
    );
    (owner, flag)
}

fn balances(owner: &OriginalAdmission) -> (u64, usize) {
    owner.inner.test_balances()
}
