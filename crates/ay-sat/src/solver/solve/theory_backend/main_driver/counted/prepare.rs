// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

pub(super) fn entry(s: &Solver, owner: &CountedAdmission) -> Result<()> {
    // Includes guard retirement. Existing solver buffers remain owned by the
    // solver; no dense destruction or unmetered reconstruction occurs here.
    owner.admit(96, 0).map_err(counted_admission::reason)?;
    let Some(flags) = ay_core::captured_misc_cli_flags() else {
        return Err(refusal(
            owner,
            "MAIN driver requires captured process configuration",
        ));
    };
    if !s
        .cold
        .counted_admission
        .as_ref()
        .is_some_and(|a| a.shares_ledger_with(owner))
    {
        return Err(refusal(owner, "MAIN driver owner identity mismatch"));
    }
    if s.cold.ic3_mode
        || s.cold.tla_trace.is_some()
        || s.cold.diagnostic_trace.is_some()
        || s.cold.trace_ext_conflict
        || s.cold.observer.is_some()
        || s.cold.progress_enabled
        || s.cold.portfolio_clause_exporter.is_some()
        || !s.cold.scope_selectors.is_empty()
        || !s.has_live_clause_trace()
        || s.proof_manager.is_some()
        || s.cold.internal_lrat_enabled
        || s.watches_disconnected
        || flags.ab_triage_var.is_some()
        || s.trail.len() > s.num_vars
        || s.trail_lim.len() != s.decision_level as usize
    {
        return Err(refusal(
            owner,
            "selected MAIN driver state or output is not admitted",
        ));
    }
    #[cfg(ay_logging)]
    if s.log_enabled {
        return Err(refusal(owner, "MAIN driver logging is not admitted"));
    }
    owner.check().map_err(counted_admission::reason)
}

pub(super) fn iteration(s: &Solver, owner: &CountedAdmission) -> Result<()> {
    // Constant-time loop gates, scheduler predicates, shared memory polling,
    // lookahead take, counters and retirement. Actual variable/BCP walks are
    // charged by their own real engines below, not this fixed allowance.
    owner.admit(128, 0).map_err(counted_admission::reason)?;
    if let Some(lit) = s.cold.lookahead_decision {
        let index = lit.variable().index();
        if index >= s.num_vars {
            return Err(refusal(owner, "invalid stored lookahead decision"));
        }
        if !s.var_is_assigned(index) && s.stats.lookahead_decisions_used == u64::MAX {
            return Err(refusal(owner, "lookahead decision counter overflow"));
        }
    }
    Ok(())
}

pub(super) fn conflict(s: &Solver, owner: &CountedAdmission) -> Result<()> {
    owner.admit(96, 0).map_err(counted_admission::reason)?;
    if !s.cold.process_memory_interrupt
        && s.num_conflicts
            .saturating_add(1)
            .is_multiple_of(PROCESS_MEMORY_CHECK_INTERVAL)
    {
        memory_poll(owner)?;
    }
    if s.conflicts_since_restart.checked_add(1).is_none()
        || s.num_conflicts.checked_add(1).is_none()
        || s.stats
            .stable_conflicts
            .checked_add(u64::from(s.stable_mode))
            .is_none()
    {
        return Err(refusal(owner, "MAIN conflict counters overflow"));
    }
    if s.num_conflicts.saturating_add(1) >= s.cold.stable_lock_at {
        return Err(refusal(
            owner,
            "selected learned-shape mode locking is not admitted",
        ));
    }
    Ok(())
}

pub(super) fn memory_poll(owner: &CountedAdmission) -> Result<()> {
    if ay_sys::get_process_memory_limit() != 0 {
        // Shared Linux reader is now stack-bounded: at most 7*(BITS+1)+8
        // reads and bounded UTF-8/field scans. Other platforms use fixed
        // metadata structures. No dynamic proc-file content allocation.
        owner.admit(4096, 0).map_err(counted_admission::reason)?;
    }
    Ok(())
}
