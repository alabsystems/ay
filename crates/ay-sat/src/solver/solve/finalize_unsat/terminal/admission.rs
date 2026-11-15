// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::solver::clause_add::terminal::Policy as _;
use crate::solver::conflict_analysis_lrat_unit_chain::admitted::Policy as _;
use crate::solver::conflict_analysis_minimize_lrat::root::Policy as _;

pub(super) fn prepare(
    s: &mut Solver,
    owner: &CountedAdmission,
    progress: ProofProgress<'_>,
) -> AdmissionResult<()> {
    owner.admit(96, 0)?;
    if !s
        .cold
        .counted_admission
        .as_ref()
        .is_some_and(|attached| attached.shares_ledger_with(owner))
    {
        return Err(invalid(
            owner,
            "terminal owner is not the attached original ledger",
        ));
    }
    if progress.is_some()
        || s.decision_level != 0
        || !s.cold.scope_selectors.is_empty()
        || s.cold.unsat_certificate_enabled
        || s.cold.backward_proof_limits.is_some()
        || s.cold.backward_proof_failure.is_some()
        || s.cold.internal_lrat_enabled
        || s.consuming_trace_pending()
        || s.cold.tla_trace.is_some()
        || s.cold.diagnostic_trace.is_some()
        || s.cold.trace_ext_conflict
        || tracing::dispatcher::has_been_set()
        || s.deterministic_inproc()
    {
        return Err(invalid(
            owner,
            "selected terminal proof/progress/diagnostic continuation is not admitted",
        ));
    }
    #[cfg(ay_logging)]
    if s.cold.log_enabled {
        return Err(invalid(owner, "selected terminal logging is not admitted"));
    }
    if s.arena.has_oversized_clause()
        || s.cold.oversized_clause_poison
        || s.cold.finalize_sat_fail_count != 0
    {
        return Err(invalid(
            owner,
            "poisoned ordinary formula cannot publish counted UNSAT",
        ));
    }
    let p = root::Counted(owner);
    p.enter(s)?;
    p.empty(s)?;
    p.enter_chain(s, &[])?;
    if let Some(bitmap) = &s.cold.streaming_core {
        let n = usize::try_from(s.cold.streaming_core_num_originals)
            .map_err(|_| invalid(owner, "streaming support ID domain overflow"))?;
        if bitmap.len() < n {
            return Err(invalid(
                owner,
                "streaming support bitmap is shorter than its original ID domain",
            ));
        }
    }
    // No dirty flag may predate this exclusive scope. Every new mark prepays
    // retirement before registration; no global scan is needed in Drop.
    owner.admit(s.min.minimize_flags.len(), 0)?;
    if s.min.minimize_flags.iter().any(|flags| flags & LRAT_A != 0) {
        return Err(invalid(owner, "terminal proof scratch is not retired"));
    }
    owner.check()
}

pub(super) fn terminal(s: &Solver, owner: &CountedAdmission) -> AdmissionResult<()> {
    owner.admit(8, 0)?;
    let Some(trace) = s.live_clause_trace() else {
        return Err(invalid(
            owner,
            "counted terminal has no retained clause trace",
        ));
    };
    if !s.has_empty_clause || trace.is_truncated() || trace.proof_work_exhausted() {
        return Err(invalid(owner, "counted terminal trace is incomplete"));
    }
    let mut last = None;
    for row in trace.entries() {
        owner.admit(3, 0)?;
        last = Some((row.id, row.clause.is_empty()));
    }
    if !last.is_some_and(|(id, empty)| id != 0 && empty && s.cold.empty_clause_lrat_id == Some(id))
    {
        return Err(invalid(
            owner,
            "counted terminal has no actual terminal empty row",
        ));
    }
    owner.check()
}
