// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::sync::{
    atomic::{AtomicBool, Ordering},
    Arc,
};

#[test]
fn exact_original_work_offer_covers_one_complete_lookup_without_renewal() {
    let (store, _, _) = tables::collision_store();
    let fee = tables::paid(&store);
    let mut checkpoint = || ControlFlow::Continue(());
    let mut owner = WorkBudget::new(u64::try_from(fee).expect("fixture"), &mut checkpoint);
    let mut sink = |work, bytes| owner.admit(work, bytes).is_ok();
    let mut admission = Admission {
        progress: &mut sink,
        refused: false,
    };
    assert_eq!(store.controlled_probe_fee(&mut admission), Ok(()));
    drop(admission);
    drop(sink);
    assert_eq!(owner.charge(0), Ok(()));
    assert_eq!(owner.charge(1), Err(QueryError::Exhausted));
}

#[test]
fn one_short_and_zero_original_owners_refuse_before_lookup_and_stay_refused() {
    let (store, keys, _) = tables::collision_store();
    let fee = tables::paid(&store);
    for grant in [0, fee - 1] {
        let mut checkpoint = || ControlFlow::Continue(());
        let mut owner = WorkBudget::new(u64::try_from(grant).expect("fixture"), &mut checkpoint);
        let mut sink = |work, bytes| owner.admit(work, bytes).is_ok();
        let mut admission = Admission {
            progress: &mut sink,
            refused: false,
        };
        for _ in 0..2 {
            assert_eq!(store.controlled_probe_fee(&mut admission), Err(limit()));
        }
        drop(admission);
        drop(sink);
        assert_eq!(owner.charge(0), Err(QueryError::Exhausted));
    }
    assert_eq!(store.hash_cons.len(), keys.len());
}

#[test]
fn original_late_stop_is_sticky_after_flag_reset_without_lookup_or_new_owner() {
    let (store, _, _) = tables::collision_store();
    let raw = Arc::new(AtomicBool::new(false));
    let captured = Arc::clone(&raw);
    let mut checkpoint = || {
        if captured.load(Ordering::Acquire) {
            ControlFlow::Break(StopReason::Cancelled)
        } else {
            ControlFlow::Continue(())
        }
    };
    let mut owner = WorkBudget::new(1_048_576, &mut checkpoint);
    assert_eq!(owner.charge(0), Ok(()));
    raw.store(true, Ordering::Release);
    let mut sink = |work, bytes| owner.admit(work, bytes).is_ok();
    let mut admission = Admission {
        progress: &mut sink,
        refused: false,
    };
    assert_eq!(store.controlled_probe_fee(&mut admission), Err(limit()));
    raw.store(false, Ordering::Release);
    assert_eq!(store.controlled_probe_fee(&mut admission), Err(limit()));
    drop(admission);
    drop(sink);
    assert_eq!(
        owner.charge(0),
        Err(QueryError::Interrupted(StopReason::Cancelled))
    );
}
