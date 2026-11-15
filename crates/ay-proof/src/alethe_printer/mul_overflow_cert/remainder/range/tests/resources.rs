// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::super::super::super::EmissionProgress;
use super::*;
use std::cell::Cell;

fn stage_projection(progress: EmissionProgress<'_>) -> Option<()> {
    let mut p = Proof::new_with_progress("r.".into(), "@r".into(), progress);
    let (x, y) = (free_bits(&mut p, "x", 3), free_bits(&mut p, "y", 3));
    super::super::specification::remainder_stages(&mut p, &x, &y)?;
    p.observe()
}

#[test]
fn every_projected_stage_cut_uses_the_same_sticky_original_owner() {
    let calls = Cell::new(0);
    let mut accept = || {
        calls.set(calls.get() + 1);
        true
    };
    stage_projection(EmissionProgress::with_caller(&mut accept)).unwrap();
    assert_eq!(
        calls.get(),
        6,
        "entry, each original bit, final, caller fence"
    );
    for cut in 1..=calls.get() {
        let seen = Cell::new(0);
        let mut stop = || {
            seen.set(seen.get() + 1);
            seen.get() != cut
        };
        let owner = EmissionProgress::with_caller(&mut stop);
        assert!(stage_projection(owner.clone()).is_none());
        assert!(owner.refused());
        assert_eq!(seen.get(), cut);
        assert!(stage_projection(owner).is_none());
        assert_eq!(seen.get(), cut);
    }
}

#[test]
fn range_proof_first_middle_and_final_refusals_never_publish_a_stage() {
    let calls = Cell::new(0);
    let mut accept = || {
        calls.set(calls.get() + 1);
        true
    };
    let owner = EmissionProgress::with_caller(&mut accept);
    let mut p = Proof::new_with_progress("r.".into(), "@r".into(), owner);
    RangeStage::new(&mut p, 1, "@s").unwrap();
    let total = calls.get();
    assert!(total > 10);
    for cut in [1, 2, total / 2, total - 1, total] {
        let seen = Cell::new(0);
        let mut stop = || {
            seen.set(seen.get() + 1);
            seen.get() != cut
        };
        let owner = EmissionProgress::with_caller(&mut stop);
        let mut p = Proof::new_with_progress("r.".into(), "@r".into(), owner.clone());
        assert!(RangeStage::new(&mut p, 1, "@s").is_none());
        assert!(owner.refused());
        assert_eq!(seen.get(), cut);
        let budget = p.budget;
        assert!(RangeStage::new(&mut p, 1, "@s").is_none());
        assert_eq!(p.budget, budget);
        assert_eq!(seen.get(), cut);
    }
}

#[test]
fn a_panicking_stage_observer_retires_the_same_owner_without_a_result() {
    let calls = Cell::new(0);
    let mut observer = || {
        calls.set(calls.get() + 1);
        assert_ne!(calls.get(), 4, "hostile observer inside stage construction");
        true
    };
    let owner = EmissionProgress::with_caller(&mut observer);
    let mut p = Proof::new_with_progress("r.".into(), "@r".into(), owner.clone());
    let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        RangeStage::new(&mut p, 3, "@s")
    }));
    assert!(outcome.is_err());
    assert!(owner.refused());
    assert!(RangeStage::new(&mut p, 3, "@s").is_none());
    assert_eq!(calls.get(), 4);
}
