// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Opt-in attribution only: no control polls, source text, or renewed grants.
//! Entered/end pairs are nested wall intervals, not additive CPU measurements.
//! Outcomes describe the outer return shape, never proof authority or a guessed
//! refusal cause. Enabling diagnostics consumes time under the unchanged wall.

use crate::smt::executor_adapter::ReplayLimit;
use ay_core::time::Instant;
use std::cell::Cell;
use std::marker::PhantomData;
use std::rc::Rc;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Phase {
    Render,
    RenderComplete,
    ParseShape,
    ParseBound,
    Setup,
    Solve,
    ExactExport,
    Recheck,
    AssumeBinding,
    Executor,
    SolverCleanup,
}

impl Phase {
    fn label(self) -> &'static str {
        match self {
            Self::Render => "render",
            Self::RenderComplete => "render-complete",
            Self::ParseShape => "parse-shape",
            Self::ParseBound => "parse-bound",
            Self::Setup => "setup",
            Self::Solve => "solve",
            Self::ExactExport => "exact-export",
            Self::Recheck => "recheck",
            Self::AssumeBinding => "assume-binding",
            Self::Executor => "executor",
            Self::SolverCleanup => "solver-cleanup",
        }
    }
}

/// Zero-based row/clause; MAX means no row. Kind: 0 none, 1 initiation,
/// 2 consecution, 3 safety, 4 trace validity. No source-owned strings enter here.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct Row {
    pub(crate) row: usize,
    pub(crate) clause: usize,
    pub(crate) kind: u8,
    pub(crate) bytes: usize,
}

const NO_ROW: Row = Row {
    row: usize::MAX,
    clause: usize::MAX,
    kind: 0,
    bytes: 0,
};
thread_local! { static ROW: Cell<Row> = const { Cell::new(NO_ROW) }; }

pub(crate) fn row_scope(row: Row) -> RowScope {
    row_scope_enabled(ay_core::misc_cli_flags().probe_strict_check, row)
}

fn row_scope_enabled(enabled: bool, row: Row) -> RowScope {
    RowScope {
        previous: enabled.then(|| ROW.with(|slot| slot.replace(row))),
        thread_bound: PhantomData,
    }
}

pub(crate) struct RowScope {
    previous: Option<Row>,
    // Restoring thread-local state on another thread would corrupt its context.
    thread_bound: PhantomData<Rc<()>>,
}

impl Drop for RowScope {
    fn drop(&mut self) {
        if let Some(previous) = self.previous {
            ROW.with(|slot| slot.set(previous));
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Outcome {
    Entered,
    Present,
    Absent,
    Ok,
    Error,
    Unwind,
    Returned,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Event {
    phase: Phase,
    row: Row,
    outcome: Outcome,
    elapsed_us: u128,
    remaining_us: Option<u128>,
    rows: usize,
}

fn deadline(limit: ReplayLimit<'_>) -> Option<Instant> {
    match limit {
        ReplayLimit::Until(deadline) | ReplayLimit::Cancellable { deadline, .. } => Some(deadline),
    }
}

fn event(
    phase: Phase,
    row: Row,
    outcome: Outcome,
    start: Instant,
    end: Instant,
    deadline: Option<Instant>,
) -> Event {
    Event {
        phase,
        row,
        outcome,
        elapsed_us: end.saturating_duration_since(start).as_micros(),
        remaining_us: deadline.map(|deadline| deadline.saturating_duration_since(end).as_micros()),
        rows: 0,
    }
}

fn emit(event: Event) {
    ay_core::safe_eprintln!(
        "--probe-strict-check: chc-replay phase={} row={} clause={} kind={} bytes={} outcome={:?} elapsed_us={} bounded={} remaining_us={} rows={}",
        event.phase.label(), event.row.row, event.row.clause, event.row.kind, event.row.bytes,
        event.outcome, event.elapsed_us, u8::from(event.remaining_us.is_some()), event.remaining_us.unwrap_or(0), event.rows,
    );
}

struct Span<'a> {
    phase: Phase,
    row: Row,
    deadline: Option<Instant>,
    start: Instant,
    outcome: Outcome,
    now: &'a mut dyn FnMut() -> Instant,
    sink: &'a mut dyn FnMut(Event),
}

impl Drop for Span<'_> {
    fn drop(&mut self) {
        let end = (self.now)();
        (self.sink)(event(
            self.phase,
            self.row,
            self.outcome,
            self.start,
            end,
            self.deadline,
        ));
    }
}

fn observe<T>(
    enabled: bool,
    phase: Phase,
    limit: ReplayLimit<'_>,
    context: impl FnOnce() -> Row,
    now: &mut dyn FnMut() -> Instant,
    sink: &mut dyn FnMut(Event),
    operation: impl FnOnce() -> T,
    classify: impl FnOnce(&T) -> Outcome,
) -> T {
    if !enabled {
        return operation();
    }
    let mut span = Span {
        phase,
        row: context(),
        deadline: deadline(limit),
        start: now(),
        outcome: Outcome::Unwind,
        now,
        sink,
    };
    (span.sink)(event(
        phase,
        span.row,
        Outcome::Entered,
        span.start,
        span.start,
        span.deadline,
    ));
    let result = operation();
    span.outcome = classify(&result);
    result
}

pub(crate) fn option<T>(
    phase: Phase,
    limit: ReplayLimit<'_>,
    operation: impl FnOnce() -> Option<T>,
) -> Option<T> {
    observe(
        ay_core::misc_cli_flags().probe_strict_check,
        phase,
        limit,
        || ROW.with(Cell::get),
        &mut Instant::now,
        &mut emit,
        operation,
        |value| {
            if value.is_some() {
                Outcome::Present
            } else {
                Outcome::Absent
            }
        },
    )
}

pub(crate) fn result<T, E>(
    phase: Phase,
    limit: ReplayLimit<'_>,
    operation: impl FnOnce() -> Result<T, E>,
) -> Result<T, E> {
    observe(
        ay_core::misc_cli_flags().probe_strict_check,
        phase,
        limit,
        || ROW.with(Cell::get),
        &mut Instant::now,
        &mut emit,
        operation,
        |value| {
            if value.is_ok() {
                Outcome::Ok
            } else {
                Outcome::Error
            }
        },
    )
}

pub(crate) fn rendered_rows(rows: usize, limit: ReplayLimit<'_>) {
    if !ay_core::misc_cli_flags().probe_strict_check {
        return;
    }
    let now = Instant::now();
    let mut summary = event(
        Phase::RenderComplete,
        NO_ROW,
        Outcome::Returned,
        now,
        now,
        deadline(limit),
    );
    summary.rows = rows;
    emit(summary);
}

/// Declare BEFORE the solver, and its start guard immediately AFTER the solver.
/// Reverse local destruction then measures only the solver's existing cleanup;
/// neither guard owns/moves the solver or changes its destruction boundary.
pub(crate) struct SolverCleanup {
    context: Option<(Row, Option<Instant>)>,
    start: Cell<Option<Instant>>,
}

impl SolverCleanup {
    pub(crate) fn new(limit: ReplayLimit<'_>) -> Self {
        Self {
            context: ay_core::misc_cli_flags()
                .probe_strict_check
                .then(|| (ROW.with(Cell::get), deadline(limit))),
            start: Cell::new(None),
        }
    }

    pub(crate) fn start_on_drop(&self) -> CleanupStart<'_> {
        CleanupStart(self)
    }
}

pub(crate) struct CleanupStart<'a>(&'a SolverCleanup);

impl Drop for CleanupStart<'_> {
    fn drop(&mut self) {
        if let Some((row, deadline)) = self.0.context {
            let start = Instant::now();
            self.0.start.set(Some(start));
            emit(event(
                Phase::SolverCleanup,
                row,
                Outcome::Entered,
                start,
                start,
                deadline,
            ));
        }
    }
}

impl Drop for SolverCleanup {
    fn drop(&mut self) {
        if let (Some((row, deadline)), Some(start)) = (self.context, self.start.get()) {
            let outcome = if std::thread::panicking() {
                Outcome::Unwind
            } else {
                Outcome::Returned
            };
            emit(event(
                Phase::SolverCleanup,
                row,
                outcome,
                start,
                Instant::now(),
                deadline,
            ));
        }
    }
}

#[cfg(test)]
mod tests;
