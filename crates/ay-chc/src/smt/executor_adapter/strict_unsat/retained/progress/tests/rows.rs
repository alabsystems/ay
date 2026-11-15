// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

const UNSAT: &str = "(declare-const x Int) (assert (> x 5)) (assert (< x 3)) (check-sat)";

fn discharged_rows(owner: &mut RetainedReplayProgress<'_>) -> Result<(), String> {
    for _ in 0..2 {
        let cap =
            super::super::super::check_plain_unsat_retained_native_with_progress(UNSAT, owner)?;
        let bytes = cap.encode(owner)?;
        bytes.admit(owner)?;
        drop(bytes);
        owner.check()?;
    }
    owner.check()
}

#[test]
fn two_rows_third_replay_encoding_and_restricted_subsetup_share_exact_or_one_short_allowance() {
    let mut callback = || true;
    let mut measured =
        RetainedReplayProgress::new(ReplayLimit::Until(deadline()), &mut callback).unwrap();
    discharged_rows(&mut measured).unwrap();
    let total = (measured.work, measured.bytes);
    for (short_work, short_bytes) in [(false, false), (true, false), (false, true)] {
        let mut callback = || true;
        let mut owner =
            RetainedReplayProgress::new(ReplayLimit::Until(deadline()), &mut callback).unwrap();
        owner.max_work = total.0 - usize::from(short_work);
        owner.max_bytes = total.1 - usize::from(short_bytes);
        assert_eq!(
            discharged_rows(&mut owner).is_ok(),
            !(short_work || short_bytes)
        );
        if short_work || short_bytes {
            assert!(owner.check().is_err());
        }
    }
}
