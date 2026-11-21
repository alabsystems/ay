// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Primitive-only observation of an already-computed recovery outcome.

use super::{Checked, Refusal};
use crate::executor::Executor;
use ay_core::TermId;
use std::cell::Cell;

#[derive(Clone, Copy)]
struct Record {
    phase: &'static str,
    check: &'static str,
    term: Option<TermId>,
    peer: Option<TermId>,
    nodes: Option<usize>,
    apps: Option<usize>,
    completed_outputs: Option<usize>,
    captured: bool,
    closed: bool,
    changed: Option<bool>,
    committed: bool,
}

pub(super) struct Probe {
    enabled: bool,
    record: Cell<Record>,
}
impl Probe {
    pub(super) fn new(enabled: bool) -> Self {
        Self {
            enabled,
            record: Cell::new(Record {
                phase: "owner",
                check: "owner-capture",
                term: None,
                peer: None,
                nodes: None,
                apps: None,
                completed_outputs: None,
                captured: false,
                closed: false,
                changed: None,
                committed: false,
            }),
        }
    }
    pub(super) fn phase(&self, phase: &'static str) {
        if self.enabled {
            let mut record = self.record.get();
            record.phase = phase;
            self.record.set(record);
        }
    }
    pub(super) fn check(&self, check: &'static str, term: Option<TermId>, peer: Option<TermId>) {
        if self.enabled {
            let mut record = self.record.get();
            record.check = check;
            record.term = term;
            record.peer = peer;
            self.record.set(record);
        }
    }
    pub(super) fn captured(&self, nodes: usize, apps: usize, completed_outputs: usize) {
        if self.enabled {
            let mut record = self.record.get();
            record.nodes = Some(nodes);
            record.apps = Some(apps);
            record.completed_outputs = Some(completed_outputs);
            record.captured = true;
            self.record.set(record);
        }
    }
    pub(super) fn closed(&self) {
        if self.enabled {
            let mut record = self.record.get();
            record.closed = true;
            self.record.set(record);
        }
    }
    pub(super) fn changed(&self, changed: bool) {
        if self.enabled {
            let mut record = self.record.get();
            record.changed = Some(changed);
            self.record.set(record);
        }
    }
    pub(super) fn committed(&self) {
        if self.enabled {
            let mut record = self.record.get();
            record.committed = true;
            self.record.set(record);
        }
    }
    /// Whether the closure phase finished (test observation only).
    #[cfg(test)]
    pub(super) fn closure_complete(&self) -> bool {
        self.record.get().closed
    }
    pub(super) fn emit(&self, exec: &Executor, result: &Checked<()>) {
        if !self.enabled {
            return;
        }
        let Some((ticket, epoch)) = exec.reserve_model_recovery_trace() else {
            return;
        };
        let record = self.record.get();
        let (outcome, stop) = match result {
            Ok(()) => ("ok", None),
            Err(Refusal::Unsupported) => ("unsupported", None),
            Err(Refusal::Conflict) => ("conflict", None),
            Err(Refusal::Stopped(origin)) => ("stopped", Some(*origin)),
        };
        // All fields are already-held primitive metadata or finite enum/static
        // tags. Formatting is after BOTH the existing flag and shared cap.
        ay_core::safe_eprintln!(
            "[ay-uf-recovery] seq={} executor={:p} epoch=0x{:x} phase={} check={} term={:?} peer={:?} nodes={:?} apps={:?} completed_bool_outputs={:?} capture_complete={} closure_complete={} changed={:?} committed={} outcome={} stop={:?}",
            ticket, std::ptr::from_ref(exec), epoch, record.phase, record.check,
            record.term, record.peer, record.nodes, record.apps, record.completed_outputs, record.captured,
            record.closed, record.changed, record.committed, outcome, stop,
        );
    }
}
