// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use std::cell::Cell;

fn solve(progress: &mut SosProgress<'_>) -> Option<Vec<BigRational>> {
    lp_phase1_feasible_with_progress(
        vec![vec![rational(2, 1), one()], vec![one(), rational(3, 1)]],
        vec![one(), one()],
        2,
        progress,
    )
}

#[test]
fn phase1_cancellation_is_sticky_at_entry_pivots_and_final_poll(
) -> Result<(), Box<dyn std::error::Error>> {
    let calls = Cell::new(0usize);
    let mut count = |_, _| {
        calls.set(calls.get().saturating_add(1));
        true
    };
    assert_eq!(
        solve(&mut SosProgress::new(&mut count)),
        Some(vec![rational(2, 5), rational(1, 5)])
    );
    let last = calls.get().checked_sub(1).ok_or("no progress calls")?;
    for permitted in [0, 2, calls.get() / 2, last] {
        let refusing_call = permitted.checked_add(1).ok_or("call count overflows")?;
        let seen = Cell::new(0usize);
        let mut callback = |_, _| {
            seen.set(seen.get().saturating_add(1));
            seen.get() != refusing_call
        };
        let mut progress = SosProgress::new(&mut callback);
        assert!(solve(&mut progress).is_none());
        assert!(progress.refused());
        assert!(solve(&mut progress).is_none());
        assert_eq!(seen.get(), refusing_call);
    }
    Ok(())
}

#[test]
fn phase1_refuses_allocation_for_tableau_and_zero_row_solution() {
    for rows in [0, 1] {
        let mut callback = |_, bytes| bytes == 0;
        let mut progress = SosProgress::new(&mut callback);
        assert!(lp_phase1_feasible_with_progress(
            vec![vec![one()]; rows],
            vec![one(); rows],
            1,
            &mut progress,
        )
        .is_none());
        assert!(progress.refused());
    }
}

#[test]
fn exact_lp_updates_charge_scratch_before_arithmetic() {
    let rejected_bytes = Cell::new(0usize);
    let mut callback = |_, bytes| {
        rejected_bytes.set(bytes);
        bytes == 0
    };
    let mut progress = SosProgress::new(&mut callback);
    let mut budget = SosLpBudget::with_progress(&mut progress);
    assert!(lp_mul(&rational(2, 3), &rational(9, 4), &mut budget).is_none());
    assert!(rejected_bytes.get() > 0);
}
