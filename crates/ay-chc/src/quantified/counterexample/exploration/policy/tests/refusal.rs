// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use std::rc::Rc;

use super::*;

#[test]
fn locally_late_sat_retries_but_parent_late_sat_never_commits() {
    let (start, deadline) = times();
    let clock = Cell::new(start);
    let token = CancellationToken::new();
    let control = SourceControl::new(deadline, &token);
    let first = Cell::new(true);
    let attempts = Cell::new(0usize);
    let result = explore(
        deadline,
        &control,
        || clock.get(),
        || {
            Some(if first.replace(false) {
                Discovery::Candidate(1)
            } else {
                Discovery::Exhausted
            })
        },
        |_, child| {
            attempts.set(attempts.get() + 1);
            clock.set(child);
            Probe::Sat
        },
    );
    assert!(result.is_none());
    assert_eq!(attempts.get(), 2);
    assert_eq!(clock.get(), deadline);
    assert!(
        control.poll().is_some(),
        "mock local time must not poison the real parent"
    );
}

#[test]
fn terminal_refusal_and_cancel_reset_do_not_admit_sat() {
    for terminal in [false, true] {
        let (start, deadline) = times();
        let token = CancellationToken::new();
        let control = SourceControl::new(deadline, &token);
        let calls = Cell::new(0usize);
        let result = explore(
            deadline,
            &control,
            || start,
            || Some(Discovery::Candidate(1)),
            |_, _| {
                calls.set(calls.get() + 1);
                if terminal {
                    Probe::Terminal
                } else {
                    token.cancel();
                    assert!(control.poll().is_none());
                    token.reset();
                    Probe::Sat
                }
            },
        );
        assert!(result.is_none());
        assert_eq!(calls.get(), 1);
        let fresh = SourceControl::new(deadline, &token);
        assert_eq!(
            explore(
                deadline,
                &fresh,
                || start,
                || Some(Discovery::Candidate(2)),
                |_, _| Probe::Sat
            ),
            Some(2)
        );
    }
}

#[test]
fn exhausted_or_pre_refused_search_never_calls_the_native_probe() {
    let (start, deadline) = times();
    let token = CancellationToken::new();
    for exhausted_budget in [false, true] {
        let control = SourceControl::new(deadline, &token);
        if exhausted_budget {
            assert!(control.bytes(64 * 1024 * 1024 + 1).is_none());
        }
        let calls = Cell::new(0usize);
        let result = explore::<usize>(
            deadline,
            &control,
            || start,
            || {
                calls.set(calls.get() + 1);
                Some(Discovery::Exhausted)
            },
            |_, _| panic!("no candidate may reach the probe"),
        );
        assert!(result.is_none());
        assert_eq!(calls.get(), usize::from(!exhausted_budget));
    }
}

#[test]
fn queue_and_probe_work_are_charged_before_the_probe_runs() {
    let (start, deadline) = times();
    let token = CancellationToken::new();
    let required = 2 * 64 + 2 * std::mem::size_of::<Pending<usize>>();
    for shortfall in [0usize, 1] {
        let control = SourceControl::new(deadline, &token);
        control
            .bytes(64 * 1024 * 1024 - required + shortfall)
            .unwrap();
        let calls = Cell::new(0usize);
        let result = explore(
            deadline,
            &control,
            || start,
            || Some(Discovery::Candidate(7usize)),
            |_, _| {
                calls.set(calls.get() + 1);
                Probe::Sat
            },
        );
        assert_eq!(result, (shortfall == 0).then_some(7));
        assert_eq!(calls.get(), usize::from(shortfall == 0));
    }
}

struct DropClock {
    id: usize,
    clock: Rc<Cell<Instant>>,
    deadline: Instant,
    poison: bool,
}

impl Drop for DropClock {
    fn drop(&mut self) {
        if self.poison {
            self.clock.set(self.deadline);
        }
    }
}

#[test]
fn pending_payload_cleanup_precedes_final_sat_admission() {
    let (start, deadline) = times();
    let clock = Rc::new(Cell::new(start));
    let token = CancellationToken::new();
    let control = SourceControl::new(deadline, &token);
    let discovered = Cell::new(0usize);
    let attempts = Cell::new(0usize);
    let result = explore(
        deadline,
        &control,
        || clock.get(),
        || {
            let id = discovered.get();
            discovered.set(id + 1);
            Some(if id < 2 {
                Discovery::Candidate(DropClock {
                    id,
                    clock: Rc::clone(&clock),
                    deadline,
                    poison: id == 1,
                })
            } else {
                Discovery::Exhausted
            })
        },
        |candidate, child| {
            assert_eq!(candidate.id, 0);
            let n = attempts.get();
            attempts.set(n + 1);
            if n == 0 {
                clock.set(child);
                Probe::Inconclusive
            } else {
                Probe::Sat
            }
        },
    );
    assert!(result.is_none());
    assert_eq!(attempts.get(), 2);
    assert_eq!(clock.get(), deadline);
}
