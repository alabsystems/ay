// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The count of UNSAT proof assembly, charged to the assembly's owner: one
//! unit per OBSERVATION of the owner's stop, and the allowance step (4a)'s
//! nested proof assembly runs on (#r30-4a-nested-assembly-count).
//!
//! # Why assembly needed a count
//!
//! `build_unsat_proof` charges no split-loop round trip and, on most shapes,
//! no conflict, so the counts step (4a) sizes its re-decision with
//! (`api/proofs/certification_effort/redecision.rs`) do not reach it. On
//! `finstore_7373_0110` (release, `fd4e00f75`) step (4a)'s question
//! re-solves `unsat` with no conflict and no round trip, and its proof
//! assembly then runs for about 3.9 s, against about 0.5 s for the first
//! solve's whole assembly; 3.0 s of it is the Farkas reconstruction pass
//! (7738 LRA solves against the first solve's 2010). Only a wall-clock slice
//! bounded it, so whether the question accepted or declined depended on the
//! host's speed.
//!
//! # The unit
//!
//! An OBSERVATION is one call of the stop the assembly's long loops poll
//! (`Executor::make_proof_assembly_should_stop`: every pass boundary, the
//! empty-clause ladder's rungs and its trace replay, the authored cascade,
//! the bridge candidates, the derivation lanes, and the printer's complete
//! bit-blast, which polls it as the emission owner's callback,
//! `with_emission_progress`), and one per reconstruction attempt of the
//! Farkas pass (`proof_farkas.rs`), which polls the search's own stop. These
//! are exactly the points at which a clock could end the assembly, so the
//! count ends it at the same kind of point, at an index the query fixes.
//! Strict proof walks are not charged here: each walk runs on its own
//! deterministic work envelope (`strict_check_progress.rs`).
//!
//! The count is per thread and monotone, like the split loops' round trips
//! (`ay_core::resource::thread_round_trips`). An assembly and every nested
//! solve it runs execute on the thread that called them, so the difference of
//! two readings is the assembly work that thread ran between them, nested
//! work included. Work another thread runs is neither charged nor stopped
//! here.
//!
//! # The allowance
//!
//! [`enter_allowance`] grants the work this thread runs a number of
//! observations until the returned scope is dropped. The observation after
//! the last granted one finds it spent; the owner's stop then reports a stop,
//! and the assembly discards its unfinished proof for the fail-closed poison
//! (`build_unsat_assembly/stop.rs`). Allowances nest, the tighter binding. A
//! spent allowance only ever ends work: it never creates or accepts a proof,
//! and the one caller that opens one (`Executor::reconfirm_unsat_within`, for
//! step (4a)) declines a re-decision whose allowance it spent. With no
//! allowance open, an observation is one thread-local add and never stops
//! anything.
//!
//! # Search work inside assembly
//!
//! [`thread_assembly_units`] is a second per-thread count, of search work
//! units (`ay_core::resource::thread_work_units`, split-loop round trips
//! plus CDCL conflicts). `Executor::build_unsat_proof` holds an
//! [`enter_assembly_units`] scope for its extent: the scope reads the units
//! when it is entered and, when it is dropped, adds their growth since then
//! to the count. Only a scope entered while no counting scope was open on
//! its thread counts, so an assembly a nested solve runs inside another is
//! counted once, as part of the outermost one. The count therefore grows
//! only when an outermost scope is dropped, and the difference of two
//! readings is the whole search work of the outermost assemblies that ended
//! between them; one still open at the later reading is not in it. Work
//! another thread runs is not counted here. The partition rescue reads the
//! count for its per-component statistics (`partition_rescue.rs`).

use std::cell::Cell;
use std::marker::PhantomData;

thread_local! {
    /// Assembly observations made on this thread; monotone.
    static OBSERVED: Cell<u64> = const { Cell::new(0) };
    /// The [`OBSERVED`] reading past which the tightest open allowance is
    /// spent; `None` while no allowance is open.
    static SPENT_PAST: Cell<Option<u64>> = const { Cell::new(None) };
    /// Search work units this thread spent inside its outermost proof
    /// assembly scopes that have ended (been dropped); monotone.
    static ASSEMBLY_UNITS: Cell<u64> = const { Cell::new(0) };
    /// Whether an [`AssemblyUnitsScope`] that counts is open on this thread:
    /// the depth guard that keeps a nested assembly from being counted twice.
    static ASSEMBLY_OPEN: Cell<bool> = const { Cell::new(false) };
}

/// Assembly observations made on this thread so far; monotone. The
/// difference of two readings is the assembly work run between them.
pub(in crate::executor) fn thread_observations() -> u64 {
    OBSERVED.try_with(Cell::get).unwrap_or(u64::MAX)
}

/// Can the current allowance cover this known lower bound on future observations?
/// This read-only admission check leaves the count available to the enclosing proof.
pub(in crate::executor) fn can_observe(additional: usize) -> bool {
    u64::try_from(additional)
        .ok()
        .and_then(|count| thread_observations().checked_add(count))
        .is_some_and(|projected| !spent_at(projected))
}

/// Charge one observation. `true` once an open allowance is spent: the
/// caller treats it as a stop, never as an answer.
pub(in crate::executor) fn observe() -> bool {
    let observed = OBSERVED
        .try_with(|count| {
            let next = count.get().saturating_add(1);
            count.set(next);
            next
        })
        .unwrap_or(u64::MAX);
    spent_at(observed)
}

/// Record the observations a check made on this thread since `started_at`
/// (its [`thread_observations`] reading when it began), its nested solves'
/// included, as the write-only statistic `proof_assembly.observations`: the
/// yardstick of step (4a)'s assembly allowance (`FirstSolveWork`).
pub(in crate::executor) fn record(
    statistics: &mut crate::executor_types::Statistics,
    started_at: u64,
) {
    statistics.set_int(
        "proof_assembly.observations",
        thread_observations().saturating_sub(started_at),
    );
}

/// Whether an open allowance is spent, without charging anything.
pub(in crate::executor) fn allowance_spent() -> bool {
    spent_at(thread_observations())
}

fn spent_at(observed: u64) -> bool {
    SPENT_PAST
        .try_with(Cell::get)
        .ok()
        .flatten()
        .is_some_and(|limit| observed > limit)
}

/// An open allowance, entered on this thread. Dropping it restores the
/// allowance around it (or none). Bound to the thread that entered it.
#[must_use = "the allowance ends when this scope is dropped"]
pub(in crate::executor) struct AllowanceScope {
    outer: Option<u64>,
    entered_at: u64,
    _not_send: PhantomData<*const ()>,
}

impl AllowanceScope {
    /// Observations charged since the scope was entered, nested work
    /// included: one past the allowance when it stopped the work.
    pub(in crate::executor) fn spent(&self) -> u64 {
        thread_observations().saturating_sub(self.entered_at)
    }
}

impl Drop for AllowanceScope {
    fn drop(&mut self) {
        let _ = SPENT_PAST.try_with(|limit| limit.set(self.outer));
    }
}

/// Grant the assembly work this thread runs `observations` observations
/// until the returned scope is dropped. An allowance entered inside another
/// is spent when either one is.
pub(in crate::executor) fn enter_allowance(observations: u64) -> AllowanceScope {
    let entered_at = thread_observations();
    let own = entered_at.saturating_add(observations);
    let outer = SPENT_PAST.try_with(Cell::get).ok().flatten();
    let tightest = outer.map_or(own, |outer| outer.min(own));
    let _ = SPENT_PAST.try_with(|limit| limit.set(Some(tightest)));
    AllowanceScope {
        outer,
        entered_at,
        _not_send: PhantomData,
    }
}

/// Search work units (`ay_core::resource::thread_work_units`) this thread
/// spent inside its outermost UNSAT proof assembly scopes that have ended;
/// monotone. It grows when an outermost [`enter_assembly_units`] scope is
/// dropped, by the units spent while that scope was open, so the difference
/// of two readings is the whole search work of the outermost assemblies that
/// ended between them, any spent before the earlier reading included; one
/// still open at the later reading is not counted.
pub(in crate::executor) fn thread_assembly_units() -> u64 {
    ASSEMBLY_UNITS.try_with(Cell::get).unwrap_or(u64::MAX)
}

/// One proof assembly's hold on [`thread_assembly_units`]: dropping it adds
/// the search work units this thread spent since it was entered, when it is
/// the scope that counts. Bound to the thread that entered it.
#[must_use = "the assembly's search work is counted when this scope is dropped"]
pub(in crate::executor) struct AssemblyUnitsScope {
    /// The `thread_work_units` reading at entry, for the scope that found no
    /// counting scope open on its thread; `None` for a nested one.
    entered_at: Option<u64>,
    _not_send: PhantomData<*const ()>,
}

impl Drop for AssemblyUnitsScope {
    fn drop(&mut self) {
        let Some(entered_at) = self.entered_at else {
            return;
        };
        let spent = ay_core::resource::thread_work_units().saturating_sub(entered_at);
        let _ = ASSEMBLY_UNITS.try_with(|units| units.set(units.get().saturating_add(spent)));
        let _ = ASSEMBLY_OPEN.try_with(|open| open.set(false));
    }
}

/// Open the count of one proof assembly's search work on this thread, for
/// [`thread_assembly_units`]. A scope entered while a counting one is open
/// counts nothing: the open one's reading already covers its work.
pub(in crate::executor) fn enter_assembly_units() -> AssemblyUnitsScope {
    let counts = ASSEMBLY_OPEN
        .try_with(|open| !open.replace(true))
        .unwrap_or(false);
    AssemblyUnitsScope {
        entered_at: counts.then(ay_core::resource::thread_work_units),
        _not_send: PhantomData,
    }
}

#[cfg(test)]
#[path = "assembly_observations_tests.rs"]
mod tests;
