// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::counted_storage::try_reserve;
use crate::vsids::BacktrackReservation;

pub(super) fn transaction(
    s: &mut Solver,
    target: u32,
    lane: Lane,
    owner: &CountedAdmission,
) -> AdmissionResult<()> {
    owner.admit(1, 0)?;
    phases(s, lane, owner)?;
    if target >= s.decision_level {
        return Ok(());
    }
    let start = lane.start(s, target);
    let mut growth = BacktrackReservation::default();
    let mut reason_required = s.reason_clause_marks.len();
    for index in start..s.trail.len() {
        // Pay the metadata scan before reading this candidate. The admitted
        // kernel visit covers compaction/phase/value/lambda bookkeeping and
        // constant-time VMTF/domain membership operations for this literal.
        owner.admit(2, 0)?;
        let var = s.trail[index].variable();
        if s.var_data[var.index()].level <= target {
            continue;
        }
        if matches!(lane, Lane::Standard { .. }) && s.chrono_enabled {
            if let Some(reference) = s.lambda[var.index()] {
                if s.arena.is_active(reference.index()) {
                    // The real chronological branch can inspect every lambda
                    // edge, even for a clause that ultimately cannot reimply.
                    // Earlier reimplied variables may lower assertion levels;
                    // preflight must not predict success from the old values.
                    owner.admit(s.arena.len_of(reference.index()), 0)?;
                    if !s.reason_marks_invalidated && is_clause_reason(reference.0) {
                        reason_required =
                            reason_required.max(reference.index().checked_add(1).ok_or_else(
                                || owner.refuse(CountedAdmissionError::StorageExhausted),
                            )?);
                    }
                }
            }
        }
        if s.var_lifecycle.is_removed(var.index()) {
            continue;
        }
        let bucket = s.bucket_queue_active
            && s.active_domain
                .as_ref()
                .is_some_and(|domain| domain.get(var.index()) == Some(&true));
        s.vsids
            .plan_backtrack_candidate(var, bucket, &mut growth, owner)?;
    }
    s.vsids.reserve_backtrack(growth, owner)?;
    let reason_growth = reason_required - s.reason_clause_marks.len();
    owner.admit(reason_growth, 0)?; // mark_reason_clause_cold's zero fill
    try_reserve(owner, &mut s.reason_clause_marks, reason_growth)?;
    if target == 0 && matches!(lane, Lane::Standard { .. }) {
        // Root cursor's partition_point plus its final predicate check.
        let len = s.cold.lrat_level0_unit_materialize_pinned.len();
        owner.admit((usize::BITS - len.leading_zeros()) as usize + 1, 0)?;
    }
    debug_postconditions(s, owner)
}

fn phases(s: &Solver, lane: Lane, owner: &CountedAdmission) -> AdmissionResult<()> {
    if !matches!(lane, Lane::Standard { save_phases: true }) {
        return Ok(());
    }
    let len = s.no_conflict_until;
    if s.stable_mode && len > s.target_trail_len {
        owner.admit(s.num_vars, 0)?;
    }
    if len > s.best_trail_len && (s.stable_mode || !s.cold.best_stable_kissat) {
        owner.admit(s.num_vars, 0)?;
    }
    Ok(())
}

fn debug_postconditions(s: &Solver, owner: &CountedAdmission) -> AdmissionResult<()> {
    #[cfg(debug_assertions)]
    {
        if s.num_conflicts & 0x3ff == 0 {
            owner.admit(s.num_vars, 0)?;
        }
        owner.admit(s.trail_lim.len(), 0)?;
        owner.admit(s.trail.len(), 0)?;
    }
    let _ = (s, owner);
    Ok(())
}
