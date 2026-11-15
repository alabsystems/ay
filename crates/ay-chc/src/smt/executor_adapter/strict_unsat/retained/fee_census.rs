// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

//! Test-only bounded attribution. Never a callback, budget, source authority,
//! proof producer, or acceptance path. Active observers consume time under the
//! test's unchanged wall. The public native snapshot is DIAGNOSTIC ONLY.

use super::super::Solver;
use ay_core::{AletheRule, ProofStep, TheoryLemmaKind};
use std::cell::RefCell;

mod capsule;
mod source;
mod tests;

const EVENTS: usize = 512;
const SOURCES: usize = 128;
const TERMS: usize = 4096;
const EDGES: usize = 32768;
const HEADS: usize = 8;

#[derive(Clone, Copy, Debug)]
struct Head {
    bytes: [u8; 32],
    len: usize,
    nodes: usize,
    clipped: bool,
}
const EMPTY_HEAD: Head = Head {
    bytes: [0; 32],
    len: 0,
    nodes: 0,
    clipped: false,
};

#[derive(Clone, Copy, Debug)]
struct Debit {
    row: usize,
    stage: &'static str,
    work: usize,
    bytes: usize,
    before_work: usize,
    before_bytes: usize,
    cap_fits: bool,
}
const EMPTY_DEBIT: Debit = Debit {
    row: 0,
    stage: "none",
    work: 0,
    bytes: 0,
    before_work: 0,
    before_bytes: 0,
    cap_fits: false,
};

#[derive(Clone, Copy, Debug)]
struct Source {
    row: usize,
    step: usize,
    family: &'static str,
    literals: usize,
    singleton_not: bool,
    array: bool,
    bool_bv_only: bool,
    small_array_keys: bool,
    max_array_bv_key: u32,
    max_bv_width: u32,
    max_arity: usize,
    ite_nodes: usize,
    indexed_apps: usize,
    unique_terms: usize,
    unique_roots: usize,
    raw_edges: usize,
    raw_var_name_bytes: usize,
    max_var_name_bytes: usize,
    narrow_typed_ops: bool,
    heads: [Head; HEADS],
    head_count: usize,
    complete: bool,
}
const EMPTY_SOURCE: Source = Source {
    row: 0,
    step: 0,
    family: "none",
    literals: 0,
    singleton_not: false,
    array: false,
    bool_bv_only: true,
    small_array_keys: true,
    max_array_bv_key: 0,
    max_bv_width: 0,
    max_arity: 0,
    ite_nodes: 0,
    indexed_apps: 0,
    unique_terms: 0,
    unique_roots: 0,
    raw_edges: 0,
    raw_var_name_bytes: 0,
    max_var_name_bytes: 0,
    narrow_typed_ops: true,
    heads: [EMPTY_HEAD; HEADS],
    head_count: 0,
    complete: false,
};

struct Census {
    case: &'static str,
    stage: &'static str,
    row: usize,
    owners: usize,
    owner_caps: (usize, usize),
    calls: usize,
    events: [Debit; EVENTS],
    event_count: usize,
    sources: [Source; SOURCES],
    source_count: usize,
    snapshots: usize,
    incomplete: bool,
    capsules: [capsule::Capsule; capsule::CAPSULES],
    capsule_count: usize,
    capsule_overflow: bool,
}
thread_local! {
    static CURRENT: RefCell<Option<Census>> = const { RefCell::new(None) };
}

struct Recording;
fn start(case: &'static str) -> Recording {
    CURRENT.with(|slot| {
        let previous = slot.replace(Some(Census {
            case,
            stage: "other-original-work",
            row: 0,
            owners: 0,
            owner_caps: (0, 0),
            calls: 0,
            events: [EMPTY_DEBIT; EVENTS],
            event_count: 0,
            sources: [EMPTY_SOURCE; SOURCES],
            source_count: 0,
            snapshots: 0,
            incomplete: false,
            capsules: [capsule::EMPTY; capsule::CAPSULES],
            capsule_count: 0,
            capsule_overflow: false,
        }));
        assert!(previous.is_none(), "fee census must not nest");
    });
    Recording
}
impl Drop for Recording {
    fn drop(&mut self) {
        CURRENT.with(|slot| {
            if let Some(census) = slot.take() {
                eprintln!(
                    "retained-fee-census case={} owners={} caps={:?} calls={} snapshots={} truncated={}",
                    census.case, census.owners, census.owner_caps,
                    census.calls, census.snapshots, census.incomplete,
                );
                for source in &census.sources[..census.source_count] {
                    eprintln!(
                        "retained-source-census case={} row={} step={} family={} literals={} singleton_not={} array={} bool_bv_only={} small_array_keys={} max_array_bv_key={} complete={}",
                        census.case, source.row, source.step, source.family, source.literals,
                        source.singleton_not, source.array, source.bool_bv_only,
                        source.small_array_keys, source.max_array_bv_key, source.complete,
                    );
                    eprintln!(
                        "retained-source-footprint case={} row={} step={} max_bv_width={} max_arity={} ite_nodes={} indexed_apps={} unique_terms={} roots={} unique_roots={} raw_edges={} raw_var_name_bytes={} max_var_name_bytes={} narrow_typed_ops={}",
                        census.case, source.row, source.step, source.max_bv_width,
                        source.max_arity, source.ite_nodes, source.indexed_apps,
                        source.unique_terms, source.literals, source.unique_roots,
                        source.raw_edges, source.raw_var_name_bytes,
                        source.max_var_name_bytes, source.narrow_typed_ops,
                    );
                    for head in &source.heads[..source.head_count] {
                        eprintln!(
                            "retained-source-disqualifier case={} row={} step={} head={} nodes={} clipped={}",
                            census.case, source.row, source.step,
                            std::str::from_utf8(&head.bytes[..head.len]).unwrap_or("<non-UTF8-prefix>"),
                            head.nodes, head.clipped,
                        );
                    }
                }
                for event in &census.events[..census.event_count] {
                    eprintln!(
                        "retained-fee-debit case={} row={} stage={} work={} bytes={} before_work={} before_bytes={} cap_fits={}",
                        census.case, event.row, event.stage, event.work, event.bytes,
                        event.before_work, event.before_bytes, event.cap_fits,
                    );
                }
                capsule::dump(&census);
            }
        });
    }
}

/// No identity, control poll, clock read, allocation, or owner debit.
pub(super) fn owner(work: usize, bytes: usize) {
    CURRENT.with(|slot| {
        if let Some(census) = slot.borrow_mut().as_mut() {
            census.owners += 1;
            if census.owners == 1 {
                census.owner_caps = (work, bytes);
            } else if census.owner_caps != (work, bytes) {
                census.incomplete = true;
            }
        }
    });
}

/// Records the existing request BEFORE its arithmetic/callback preflight.
/// cap_fits is arithmetic only: it is NOT acceptance or a callback verdict.
pub(super) fn debit(
    work: usize,
    bytes: usize,
    before_work: usize,
    before_bytes: usize,
    max_work: usize,
    max_bytes: usize,
) {
    CURRENT.with(|slot| {
        if let Some(census) = slot.borrow_mut().as_mut() {
            census.calls += 1;
            let cap_fits = before_work.checked_add(work).is_some_and(|n| n <= max_work)
                && before_bytes
                    .checked_add(bytes)
                    .is_some_and(|n| n <= max_bytes);
            if work < 1_000_000 && bytes < 1_000_000 && cap_fits {
                return;
            }
            if census.event_count == EVENTS {
                census.incomplete = true;
                return;
            }
            census.events[census.event_count] = Debit {
                row: census.row,
                stage: census.stage,
                work,
                bytes,
                before_work,
                before_bytes,
                cap_fits,
            };
            census.event_count += 1;
        }
    });
}

pub(crate) struct Stage(Option<&'static str>);
pub(super) fn stage(label: &'static str) -> Stage {
    Stage(CURRENT.with(|slot| {
        slot.borrow_mut().as_mut().map(|census| {
            let previous = census.stage;
            census.stage = label;
            previous
        })
    }))
}
impl Drop for Stage {
    fn drop(&mut self) {
        if let Some(previous) = self.0 {
            CURRENT.with(|slot| {
                if let Some(census) = slot.borrow_mut().as_mut() {
                    census.stage = previous;
                }
            });
        }
    }
}

/// Borrow fields of the SAME already-solved native proof's public snapshot.
/// The snapshot is immediately dropped; it is never replayed, serialized,
/// compared as source authority, or passed to the retained exporter.
pub(super) fn native(solver: &Solver) {
    if !CURRENT.with(|slot| slot.borrow().is_some()) {
        return;
    }
    let snapshot = solver.export_last_unsat_bundle();
    CURRENT.with(|slot| {
        let mut active = slot.borrow_mut();
        let Some(census) = active.as_mut() else {
            return;
        };
        census.row = census.snapshots;
        census.snapshots += 1;
        let Some(snapshot) = snapshot.as_ref() else {
            census.incomplete = true;
            return;
        };
        for (step, item) in snapshot.steps.iter().enumerate() {
            let (family, clause) = match item {
                ProofStep::TheoryLemma { kind, clause, .. } => (
                    match kind {
                        TheoryLemmaKind::BvBitBlast => "BvBitBlast",
                        TheoryLemmaKind::BvBitBlastGate { .. } => "BvBitBlastGate",
                        TheoryLemmaKind::BvLiaTautology => "BvLiaTautology",
                        TheoryLemmaKind::SeqExtensionalCompanionContradiction => {
                            "SeqExtensionalCompanionContradiction"
                        }
                        _ => "OtherTheoryLemma",
                    },
                    clause.as_slice(),
                ),
                ProofStep::Step {
                    rule: AletheRule::Evaluate,
                    clause,
                    ..
                } => ("Evaluate", clause.as_slice()),
                _ => continue,
            };
            if census.source_count == SOURCES {
                census.incomplete = true;
                break;
            }
            let mut source = source::shape(snapshot, clause);
            source.row = census.row;
            source.step = step;
            source.family = family;
            census.incomplete |= !source.complete;
            census.sources[census.source_count] = source;
            census.source_count += 1;
            capsule::record(census, snapshot, clause, step);
        }
    });
}

pub(super) fn begin_export(solver: &Solver) -> Stage {
    native(solver);
    stage("walks-1+2-live-exact-export")
}
