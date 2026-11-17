// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
//! A bounded main-tree prefix of the existing row-propagation arithmetic.
use super::{ColKind, Model, NoDeps, Row, SearchMode};
use std::sync::atomic::Ordering::Relaxed;
use std::time::{Duration, Instant};

pub(super) const MAX_CALLS: usize = 64;
pub(super) const MAX_VISITS: usize = 4096;
pub(super) const ROWS_PER_CALL: usize = 64;
pub(super) const MAX_COLUMNS: usize = 4096;
// One preallocated usize queue, one bool queued vector, 64 stack terms and
// small counters. A conservative nominal simultaneous allowance, not RSS.
pub(super) const SCRATCH_BYTES: usize = 80 * 1024;

#[derive(Clone, Copy)]
pub(super) enum Activation {
    Legacy,
    MarkedMargin,
}

#[derive(Debug, Clone, Default)]
pub(super) struct Report {
    pub(super) eligible: bool,
    pub(super) attempts: usize,
    pub(super) completed: usize,
    pub(super) visits: usize,
    pub(super) terms: usize,
    pub(super) skipped_wide: usize,
    pub(super) invalid_rows: usize,
    pub(super) tightenings: usize,
    pub(super) binary_fixings: usize,
    pub(super) conflicts: usize,
    pub(super) accepted_prunes: usize,
    pub(super) row_limits: usize,
    pub(super) queue_limits: usize,
    pub(super) deadline_limits: usize,
    pub(super) memory_declines: usize,
    pub(super) elapsed: Duration,
    pub(super) stop: &'static str,
    #[cfg(test)]
    pub(super) visited_rows: Vec<u32>,
    #[cfg(test)]
    pub(super) first_node: Option<usize>,
    #[cfg(test)]
    pub(super) last_node: Option<usize>,
    #[cfg(test)]
    pub(super) first_conflict_node: Option<usize>,
}

pub(super) struct EarlyPropagation {
    source: usize,
    pub(super) report: Report,
}
impl EarlyPropagation {
    pub(super) fn new(
        model: &Model,
        mode: SearchMode,
        enabled: bool,
        default_class: bool,
        activation: Activation,
    ) -> Self {
        let eligible = matches!(activation, Activation::MarkedMargin)
            && enabled
            && default_class
            && mode.depth == 0
            && !mode.projected
            && !mode.cheap
            && !mode.dfs
            && !model.has_inexact_coeffs()
            && model.num_cols() <= MAX_COLUMNS;
        Self {
            source: std::ptr::from_ref(model) as usize,
            report: Report {
                eligible,
                stop: if eligible { "ready" } else { "ineligible" },
                ..Report::default()
            },
        }
    }

    /// None declines optional work; Some(true) retains a sound partial box.
    /// Only a completed, still-live contradiction returns Some(false).
    pub(super) fn propagate(
        &mut self,
        model: &Model,
        node: usize,
        adjacency: &[Vec<u32>],
        seeds: &[usize],
        lower: &mut [f64],
        upper: &mut [f64],
        deadline: Option<Instant>,
        open_bytes: usize,
        memory: Option<usize>,
    ) -> Option<bool> {
        if !self.start(model, node, seeds, deadline) {
            return None;
        }
        let (rows, queue) = self.limits(model, adjacency, seeds, lower.len(), upper.len())?;
        if !self.scratch_fits(open_bytes, memory) {
            return None;
        }
        let began = Instant::now();
        let mut control = Control::Bounded {
            rows,
            queue,
            deadline,
            run: Report::default(),
        };
        let alive = super::propagate_branch_rows_many_t(
            model,
            adjacency,
            seeds,
            lower,
            upper,
            &mut NoDeps,
            &mut control,
        );
        let Control::Bounded { run, .. } = control else {
            return None;
        };
        let late = deadline.is_some_and(|d| Instant::now() >= d);
        let pruned = !alive && !late;
        self.report.accepted_prunes += usize::from(pruned);
        #[cfg(test)]
        if pruned {
            self.report.first_conflict_node.get_or_insert(node);
        }
        self.absorb(run, began.elapsed(), late);
        Some(!pruned)
    }

    fn start(
        &mut self,
        model: &Model,
        node: usize,
        seeds: &[usize],
        deadline: Option<Instant>,
    ) -> bool {
        if !self.report.eligible || seeds.is_empty() {
            return false;
        }
        if self.source != std::ptr::from_ref(model) as usize {
            self.report.stop = "foreign-source";
            return false;
        }
        if self.report.attempts >= MAX_CALLS || self.report.visits >= MAX_VISITS {
            self.report.stop = if self.report.visits >= MAX_VISITS {
                "visit-cap"
            } else {
                "call-cap"
            };
            return false;
        }
        self.report.attempts += 1;
        #[cfg(test)]
        {
            self.report.first_node.get_or_insert(node);
            self.report.last_node = Some(node);
        }
        #[cfg(not(test))]
        let _ = node;
        if deadline.is_some_and(|d| Instant::now() >= d) {
            self.report.deadline_limits += 1;
            self.report.stop = "deadline";
            return false;
        }
        true
    }

    fn limits(
        &mut self,
        model: &Model,
        adjacency: &[Vec<u32>],
        seeds: &[usize],
        lower_len: usize,
        upper_len: usize,
    ) -> Option<(usize, usize)> {
        let rows = super::PROP_MAX_SWEEPS_CFG
            .load(Relaxed)
            .min(ROWS_PER_CALL)
            .min(MAX_VISITS - self.report.visits);
        let queue = super::PROP_MAX_QUEUE_CFG.load(Relaxed).min(MAX_COLUMNS);
        if rows == 0
            || queue == 0
            || seeds.len() > queue
            || adjacency.len() != model.num_cols()
            || lower_len < model.num_cols()
            || upper_len < model.num_cols()
            || seeds.iter().any(|&j| j >= model.num_cols())
        {
            self.report.stop = "capacity";
            return None;
        }
        Some((rows, queue))
    }

    fn scratch_fits(&mut self, open_bytes: usize, memory: Option<usize>) -> bool {
        if memory.is_some_and(|m| open_bytes.checked_add(SCRATCH_BYTES).is_none_or(|n| n > m)) {
            self.report.memory_declines += 1;
            self.report.stop = "memory";
            return false;
        }
        true
    }

    fn absorb(&mut self, run: Report, elapsed: Duration, late: bool) {
        let r = &mut self.report;
        r.visits += run.visits;
        r.terms += run.terms;
        r.skipped_wide += run.skipped_wide;
        r.invalid_rows += run.invalid_rows;
        r.tightenings += run.tightenings;
        r.binary_fixings += run.binary_fixings;
        r.conflicts += run.conflicts;
        r.row_limits += run.row_limits;
        r.queue_limits += run.queue_limits;
        r.deadline_limits += usize::from(late || run.deadline_limits > 0);
        r.completed += usize::from(
            !late && run.deadline_limits == 0 && run.row_limits == 0 && run.queue_limits == 0,
        );
        r.elapsed += elapsed;
        r.stop = if late || run.deadline_limits > 0 {
            "deadline"
        } else if run.row_limits > 0 {
            "row-cap"
        } else if run.queue_limits > 0 {
            "queue-cap"
        } else {
            "completed"
        };
        #[cfg(test)]
        r.visited_rows.extend(run.visited_rows);
    }
}

/// Legacy callers keep their original caps, seed allocation and no clock read.
/// Bounded callers supply values; no global tuning atomics are mutated.
#[cfg_attr(
    test,
    expect(
        clippy::large_enum_variant,
        reason = "test-only report instrumentation enlarges this stack-local control; boxing would add an unbudgeted allocation to optional bounded propagation"
    )
)]
pub(super) enum Control {
    Legacy,
    Bounded {
        rows: usize,
        queue: usize,
        deadline: Option<Instant>,
        run: Report,
    },
}
impl Control {
    pub(super) fn rows(&self, legacy: usize) -> usize {
        match self {
            Self::Legacy => legacy,
            Self::Bounded { rows, .. } => *rows,
        }
    }
    pub(super) fn queue(&self, legacy: usize) -> usize {
        match self {
            Self::Legacy => legacy,
            Self::Bounded { queue, .. } => *queue,
        }
    }
    pub(super) fn queue_capacity(&self, seeds: usize, cap: usize) -> usize {
        match self {
            Self::Legacy => seeds,
            Self::Bounded { .. } => cap,
        }
    }
    pub(super) fn before_row(&mut self) -> bool {
        match self {
            Self::Bounded {
                deadline: Some(d),
                run,
                ..
            } if Instant::now() >= *d => {
                run.deadline_limits = 1;
                false
            }
            _ => true,
        }
    }
    pub(super) fn row_limit(&mut self) {
        if let Self::Bounded { run, .. } = self {
            run.row_limits += 1;
        }
    }
    pub(super) fn visit(&mut self, row: u32, terms: usize) {
        if let Self::Bounded { run, .. } = self {
            run.visits += 1;
            if terms > 64 {
                run.skipped_wide += 1;
            } else {
                run.terms += terms;
            }
            #[cfg(test)]
            run.visited_rows.push(row);
            #[cfg(not(test))]
            let _ = row;
        }
    }
    pub(super) fn invalid_row(&mut self) {
        if let Self::Bounded { run, .. } = self {
            run.invalid_rows += 1;
        }
    }
    pub(super) fn conflict(&mut self) {
        if let Self::Bounded { run, .. } = self {
            run.conflicts += 1;
        }
    }
    pub(super) fn tightened(&mut self, kind: ColKind, old: (f64, f64), new: (f64, f64)) {
        if let Self::Bounded { run, .. } = self {
            if old != new {
                run.tightenings += 1;
                run.binary_fixings +=
                    usize::from(matches!(kind, ColKind::Binary) && old.0 < old.1 && new.0 == new.1);
            }
        }
    }
    pub(super) fn queue_limit(&mut self) {
        if let Self::Bounded { run, .. } = self {
            run.queue_limits += 1;
        }
    }
}

/// Build adjacency once; every later node retains these row/column identities.
pub(super) fn column_rows(model: &Model) -> Vec<Vec<u32>> {
    let mut result = vec![Vec::new(); model.num_cols()];
    for row in 0..model.num_rows() {
        let (coefficients, _, _) = model.row(Row(row as u32));
        for &(column, _) in coefficients {
            result[column as usize].push(row as u32);
        }
    }
    result
}

#[cfg(test)]
thread_local! {
    static TEST_REPORTS: std::cell::RefCell<Vec<Report>> = const { std::cell::RefCell::new(Vec::new()) };
}
#[cfg(test)]
impl Drop for EarlyPropagation {
    fn drop(&mut self) {
        TEST_REPORTS.with(|slot| {
            let mut records = slot.borrow_mut();
            if records.len() < 64 {
                records.push(self.report.clone());
            }
        });
    }
}
#[cfg(test)]
pub(super) fn take_test_reports() -> Vec<Report> {
    TEST_REPORTS.with(|slot| std::mem::take(&mut *slot.borrow_mut()))
}
#[cfg(test)]
#[path = "early_propagation_certificate_tests.rs"]
mod certificate_tests;
#[cfg(test)]
#[path = "early_propagation_tests.rs"]
mod tests;
