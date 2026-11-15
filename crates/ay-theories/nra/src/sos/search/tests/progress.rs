// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use std::cell::Cell;

#[test]
fn shared_search_control_cannot_recover_after_cancelled_fallback_or_replay(
) -> Result<(), Box<dyn std::error::Error>> {
    let source = shifted_quartic(Rel::Lt);
    let variables = [TermId(1)];
    let calls = Cell::new(0usize);
    let bytes = Cell::new(0usize);
    let mut count = |_: usize, allocated: usize| {
        calls.set(calls.get().saturating_add(1));
        bytes.set(bytes.get().saturating_add(allocated));
        true
    };
    let certificate = search_with_progress(&source, &variables, &mut SosProgress::new(&mut count))
        .expect("shared allowance admits the shifted-quartic fallback");
    assert!(calls.get() > 20);
    assert!(bytes.get() > 0);
    let last = calls.get().checked_sub(1).ok_or("no progress calls")?;
    for permitted in [0, 1, calls.get() / 4, calls.get() / 2, last] {
        let refusing_call = permitted.checked_add(1).ok_or("call count overflows")?;
        let seen = Cell::new(0usize);
        let mut once_false = |_, _| {
            seen.set(seen.get().saturating_add(1));
            seen.get() != refusing_call
        };
        let mut progress = SosProgress::new(&mut once_false);
        assert!(search_with_progress(&source, &variables, &mut progress).is_none());
        assert!(progress.refused());
        assert_eq!(seen.get(), refusing_call);
        assert_eq!(
            certificate.verify_with_progress(&source, &mut progress),
            Err(SosError::ResourceLimit)
        );
        assert_eq!(
            seen.get(),
            refusing_call,
            "refusal cannot be reset by a new phase"
        );
    }
    Ok(())
}

#[test]
fn exact_replay_cancellation_dominates_entry_middle_and_final_poll(
) -> Result<(), Box<dyn std::error::Error>> {
    let source = shifted_quartic(Rel::Lt);
    let certificate = search(&source, &[TermId(1)]).expect("small source witness");
    let calls = Cell::new(0usize);
    let mut count = |_, _| {
        calls.set(calls.get().saturating_add(1));
        true
    };
    certificate
        .verify_with_progress(&source, &mut SosProgress::new(&mut count))
        .unwrap();
    let last = calls.get().checked_sub(1).ok_or("no progress calls")?;
    for permitted in [0, calls.get() / 2, last] {
        let seen = Cell::new(0usize);
        let mut callback = |_, _| {
            seen.set(seen.get().saturating_add(1));
            seen.get() <= permitted
        };
        let mut progress = SosProgress::new(&mut callback);
        assert_eq!(
            certificate.verify_with_progress(&source, &mut progress),
            Err(SosError::ResourceLimit)
        );
        assert!(progress.refused());
    }
    Ok(())
}

#[test]
fn search_and_replay_share_a_cumulative_byte_allowance() {
    let source = shifted_quartic(Rel::Lt);
    let variables = [TermId(1)];
    let bytes = Cell::new(0usize);
    let mut count = |_, allocated| {
        bytes.set(bytes.get().saturating_add(allocated));
        true
    };
    let certificate =
        search_with_progress(&source, &variables, &mut SosProgress::new(&mut count)).unwrap();
    let search_bytes = bytes.get();
    let spent = Cell::new(0usize);
    let mut callback = |_, allocated| {
        spent.set(spent.get().saturating_add(allocated));
        spent.get() <= search_bytes
    };
    let mut progress = SosProgress::new(&mut callback);
    assert!(search_with_progress(&source, &variables, &mut progress).is_some());
    assert_eq!(spent.get(), search_bytes);
    assert_eq!(
        certificate.verify_with_progress(&source, &mut progress),
        Err(SosError::ResourceLimit)
    );
    assert!(progress.refused());
}
