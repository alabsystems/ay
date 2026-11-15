// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The strict byte replay (walk 4) returns its transient checker bytes.

use super::*;

#[test]
fn declared_validation_returns_its_checker_bytes_and_a_bare_one_keeps_them() {
    for declared in [true, false] {
        let mut callback = || true;
        let mut progress =
            RetainedReplayProgress::new(ReplayLimit::Until(deadline()), &mut callback).unwrap();
        if declared {
            progress.begin_obligation().unwrap();
        }
        let (row, payload) = sealed(&mut progress);
        let (work, bytes, ..) = progress.ledger();
        payload
            .validate_retained_with_resources(&row, &mut progress)
            .unwrap();
        let after = progress.ledger();
        assert!(after.0 > work, "work is never returned");
        if declared {
            assert_eq!(after.1, bytes, "walk-4 bytes return when its owners drop");
        } else {
            assert!(
                after.1 > bytes,
                "a request without obligations stays cumulative"
            );
        }
    }
}
