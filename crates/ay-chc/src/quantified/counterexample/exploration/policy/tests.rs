// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![allow(clippy::unwrap_used)]

use std::cell::{Cell, RefCell};

use super::*;

mod refusal;

fn times() -> (Instant, Instant) {
    let start = Instant::now();
    (start, start + Duration::from_secs(30))
}

#[test]
fn more_than_sixty_four_unsat_decoys_do_not_hide_later_sat() {
    let (start, deadline) = times();
    let clock = Cell::new(start);
    let token = CancellationToken::new();
    let control = SourceControl::new(deadline, &token);
    let discovered = Cell::new(0usize);
    let attempted = RefCell::new(Vec::new());
    let result = explore(
        deadline,
        &control,
        || clock.get(),
        || {
            let id = discovered.get();
            discovered.set(id + 1);
            Some(if id <= 130 {
                Discovery::Candidate(id)
            } else {
                Discovery::Exhausted
            })
        },
        |id, _| {
            attempted.borrow_mut().push(*id);
            clock.set(clock.get() + Duration::from_micros(1));
            if *id == 130 {
                Probe::Sat
            } else {
                Probe::Unsat
            }
        },
    );
    assert_eq!(result, Some(130));
    assert_eq!(*attempted.borrow(), (0..=130).collect::<Vec<_>>());
}

#[test]
fn early_inconclusive_candidate_cannot_starve_later_discovery() {
    let (start, deadline) = times();
    let clock = Cell::new(start);
    let token = CancellationToken::new();
    let control = SourceControl::new(deadline, &token);
    let discovered = Cell::new(0usize);
    let hard_attempts = Cell::new(0usize);
    let result = explore(
        deadline,
        &control,
        || clock.get(),
        || {
            let id = discovered.get();
            discovered.set(id + 1);
            Some(if id <= 130 {
                Discovery::Candidate(id)
            } else {
                Discovery::Exhausted
            })
        },
        |id, child| match *id {
            0 => {
                hard_attempts.set(hard_attempts.get() + 1);
                clock.set(child);
                Probe::Inconclusive
            }
            130 => Probe::Sat,
            _ => Probe::Unsat,
        },
    );
    assert_eq!(result, Some(130));
    assert_eq!(hard_attempts.get(), 8);
    assert!(clock.get() < start + Duration::from_secs(10));
}

#[test]
fn sole_remaining_candidate_receives_the_remaining_parent_budget() {
    let (start, deadline) = times();
    let clock = Cell::new(start);
    let token = CancellationToken::new();
    let control = SourceControl::new(deadline, &token);
    let first = Cell::new(true);
    let slices = RefCell::new(Vec::new());
    let result = explore(
        deadline,
        &control,
        || clock.get(),
        || {
            Some(if first.replace(false) {
                Discovery::Candidate(7)
            } else {
                Discovery::Exhausted
            })
        },
        |_, child| {
            let slice = child - clock.get();
            slices.borrow_mut().push(slice);
            if slice < Duration::from_millis(500) {
                clock.set(child);
                Probe::Inconclusive
            } else {
                clock.set(clock.get() + Duration::from_millis(500));
                Probe::Sat
            }
        },
    );
    assert_eq!(result, Some(7));
    assert_eq!(
        *slices.borrow(),
        vec![INITIAL_SLICE, deadline - start - INITIAL_SLICE]
    );
}

#[test]
fn pending_generator_transitions_yield_to_retained_retries() {
    let (start, deadline) = times();
    let clock = Cell::new(start);
    let token = CancellationToken::new();
    let control = SourceControl::new(deadline, &token);
    let steps = Cell::new(0usize);
    let attempts = Cell::new(0usize);
    let result = explore(
        deadline,
        &control,
        || clock.get(),
        || {
            let n = steps.get();
            steps.set(n + 1);
            Some(if n == 0 {
                Discovery::Candidate(9)
            } else {
                Discovery::Pending
            })
        },
        |_, child| {
            let count = attempts.get();
            attempts.set(count + 1);
            assert!(steps.get() <= 1 + (count + 1) * MAX_DISCOVERY_MICROSTEPS);
            if count == 5 {
                Probe::Sat
            } else {
                clock.set(child);
                Probe::Inconclusive
            }
        },
    );
    assert_eq!(result, Some(9));
    assert_eq!(attempts.get(), 6);
    assert_eq!(steps.get(), 1 + 64 + 128 + 256 * 3);
}

#[test]
fn retry_snapshot_keeps_fifo_order_and_retires_only_definitive_unsat() {
    let (start, deadline) = times();
    let clock = Cell::new(start);
    let token = CancellationToken::new();
    let control = SourceControl::new(deadline, &token);
    let mut discovery = [0, 1, 2].into_iter();
    let attempted = RefCell::new(Vec::new());
    let result = explore(
        deadline,
        &control,
        || clock.get(),
        || {
            Some(
                discovery
                    .next()
                    .map_or(Discovery::Exhausted, Discovery::Candidate),
            )
        },
        |id, child| {
            attempted.borrow_mut().push(*id);
            match *id {
                0 => Probe::Unsat,
                1 if attempted.borrow().iter().filter(|&&n| n == 1).count() == 1 => {
                    clock.set(child);
                    Probe::Inconclusive
                }
                1 => Probe::Sat,
                _ => Probe::Unsat,
            }
        },
    );
    assert_eq!(result, Some(1));
    assert_eq!(*attempted.borrow(), vec![0, 1, 2, 1]);
}
