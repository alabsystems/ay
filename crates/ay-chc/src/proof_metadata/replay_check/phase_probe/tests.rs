// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::time::Duration;

const TEST_ROW: Row = Row {
    row: 7,
    clause: 11,
    kind: 3,
    bytes: 91,
};

#[test]
fn disabled_probe_does_not_observe_clock_context_sink_or_result() {
    let deadline = Instant::now() + Duration::from_secs(60);
    let returned = observe(
        false,
        Phase::Solve,
        ReplayLimit::Until(deadline),
        || panic!("disabled context"),
        &mut || panic!("disabled clock"),
        &mut |_| panic!("disabled sink"),
        || Some(42),
        |_| panic!("disabled classification"),
    );
    assert_eq!(returned, Some(42));
}

#[test]
fn phases_preserve_results_and_emit_one_pair_with_exact_numeric_identity() {
    let start = Instant::now();
    for value in [Some(Some(42)), Some(None), None] {
        let mut ticks = [start, start + Duration::from_millis(3)].into_iter();
        let mut events = Vec::new();
        let actual = observe(
            true,
            Phase::ExactExport,
            ReplayLimit::Until(start + Duration::from_millis(9)),
            || TEST_ROW,
            &mut || ticks.next().expect("exactly two diagnostic clock reads"),
            &mut |event| events.push(event),
            || value,
            |value| {
                if value.is_some() {
                    Outcome::Present
                } else {
                    Outcome::Absent
                }
            },
        );
        assert_eq!(actual, value);
        assert_eq!(
            events,
            vec![
                Event {
                    phase: Phase::ExactExport,
                    row: TEST_ROW,
                    outcome: Outcome::Entered,
                    elapsed_us: 0,
                    remaining_us: Some(9000),
                    rows: 0
                },
                Event {
                    phase: Phase::ExactExport,
                    row: TEST_ROW,
                    outcome: if value.is_some() {
                        Outcome::Present
                    } else {
                        Outcome::Absent
                    },
                    elapsed_us: 3000,
                    remaining_us: Some(6000),
                    rows: 0
                }
            ]
        );
        assert!(ticks.next().is_none());
    }
}

#[test]
fn probe_preserves_operation_polls_drop_and_post_refusal_order() {
    for enabled in [false, true] {
        let history = std::cell::RefCell::new(Vec::new());
        struct Local<'a>(&'a std::cell::RefCell<Vec<&'static str>>);
        impl Drop for Local<'_> {
            fn drop(&mut self) {
                self.0.borrow_mut().push("drop");
            }
        }
        let start = Instant::now();
        let result = observe(
            enabled,
            Phase::Executor,
            ReplayLimit::Until(start),
            || TEST_ROW,
            &mut || start,
            &mut |_| {},
            || {
                history.borrow_mut().push("pre");
                let proposed = {
                    let _local = Local(&history);
                    history.borrow_mut().push("operation");
                    Some(7)
                };
                history.borrow_mut().push("post");
                proposed.filter(|_| false)
            },
            |value| {
                if value.is_some() {
                    Outcome::Present
                } else {
                    Outcome::Absent
                }
            },
        );
        assert_eq!(result, None);
        assert_eq!(*history.borrow(), ["pre", "operation", "drop", "post"]);
    }
}

#[test]
fn unwind_emits_one_pair_and_restores_nested_row_context() {
    let old = ROW.with(Cell::get);
    let mut events = Vec::new();
    let start = Instant::now();
    let outer = row_scope_enabled(true, TEST_ROW);
    let inner = Row { row: 9, ..TEST_ROW };
    let caught = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _inner = row_scope_enabled(true, inner);
        observe(
            true,
            Phase::ParseShape,
            ReplayLimit::Until(start + Duration::from_secs(60)),
            || ROW.with(Cell::get),
            &mut || start,
            &mut |event| events.push(event),
            || panic!("opaque phase"),
            |()| Outcome::Ok,
        );
    }));
    assert!(caught.is_err());
    assert_eq!(events.len(), 2);
    assert_eq!(events[0].row, inner);
    assert_eq!(events[0].outcome, Outcome::Entered);
    assert_eq!(events[1].row, inner);
    assert_eq!(events[1].outcome, Outcome::Unwind);
    assert_eq!(ROW.with(Cell::get), TEST_ROW);
    {
        let _disabled = row_scope_enabled(false, inner);
        assert_eq!(ROW.with(Cell::get), TEST_ROW);
    }
    drop(outer);
    assert_eq!(ROW.with(Cell::get), old);
}

#[test]
fn expired_snapshot_is_only_metadata_and_never_polls_cancellation() {
    use crate::smt::executor_adapter::ReplayCancellation;
    let token = crate::CancellationToken::new();
    let cancellation = ReplayCancellation::new(&token);
    token.cancel();
    let start = Instant::now();
    let mut events = Vec::new();
    let actual: Result<usize, usize> = observe(
        true,
        Phase::Recheck,
        ReplayLimit::Cancellable {
            deadline: start,
            cancellation: &cancellation,
        },
        || TEST_ROW,
        &mut || start + Duration::from_millis(1),
        &mut |event| events.push(event),
        || Err(17),
        |value| {
            if value.is_ok() {
                Outcome::Ok
            } else {
                Outcome::Error
            }
        },
    );
    assert_eq!(actual, Err(17));
    assert_eq!(events.len(), 2);
    assert_eq!(events[1].remaining_us, Some(0));
    assert_eq!(events[1].outcome, Outcome::Error);
    token.reset();
    assert!(
        !cancellation.is_cancelled(),
        "diagnostics must not make cancellation sticky"
    );
}

#[test]
fn opaque_results_never_enter_diagnostic_events() {
    let start = Instant::now();
    let secret = "(assert confidential_source_formula)";
    for value in [Ok(secret), Err(secret)] {
        let mut events = Vec::new();
        let actual = observe(
            true,
            Phase::ExactExport,
            ReplayLimit::Until(start + Duration::from_secs(60)),
            || TEST_ROW,
            &mut || start,
            &mut |event| events.push(event),
            || value,
            |value| {
                if value.is_ok() {
                    Outcome::Ok
                } else {
                    Outcome::Error
                }
            },
        );
        assert_eq!(actual, value);
        assert_eq!(events.len(), 2);
        assert_eq!(
            events[1].outcome,
            if value.is_ok() {
                Outcome::Ok
            } else {
                Outcome::Error
            }
        );
        assert!(events.iter().all(|event| event.row == TEST_ROW));
        assert!(!format!("{events:?}").contains(secret));
    }
}

#[test]
fn cleanup_guards_bracket_existing_owner_drop_on_return_and_unwind() {
    for enabled in [false, true] {
        for unwind in [false, true] {
            let drops = Cell::new(0);
            struct Owner<'a> {
                cleanup: &'a SolverCleanup,
                drops: &'a Cell<usize>,
                enabled: bool,
            }
            impl Drop for Owner<'_> {
                fn drop(&mut self) {
                    assert_eq!(self.cleanup.start.get().is_some(), self.enabled);
                    self.drops.set(self.drops.get() + 1);
                }
            }
            let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                let cleanup = SolverCleanup {
                    context: enabled.then_some((TEST_ROW, None)),
                    start: Cell::new(None),
                };
                let _owner = Owner {
                    cleanup: &cleanup,
                    drops: &drops,
                    enabled,
                };
                let _start = cleanup.start_on_drop();
                assert!(cleanup.start.get().is_none());
                assert!(!unwind, "opaque owner operation");
                37
            }));
            assert_eq!(result.is_err(), unwind);
            if !unwind {
                assert_eq!(result.ok(), Some(37));
            }
            assert_eq!(drops.get(), 1);
        }
    }
}
