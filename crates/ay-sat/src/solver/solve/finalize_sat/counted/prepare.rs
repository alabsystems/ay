// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;

pub(super) fn entry(s: &Solver, owner: &CountedAdmission) -> AdmissionResult<()> {
    // Includes constant-time error classification and exceptional retirement.
    owner.admit(64, 0)?;
    if !s
        .cold
        .counted_admission
        .as_ref()
        .is_some_and(|a| a.shares_ledger_with(owner))
    {
        return Err(invalid(
            owner,
            "SAT model owner is not the attached original ledger",
        ));
    }
    if ay_core::captured_misc_cli_flags().is_none()
        || s.cold.tla_trace.is_some()
        || s.cold.diagnostic_trace.is_some()
        || s.cold.trace_ext_conflict
        || tracing::dispatcher::has_been_set()
        || s.active_domain.is_some()
        || !s.cold.scope_selectors.is_empty()
    {
        return Err(invalid(
            owner,
            "selected SAT model scope/domain/diagnostic path is not admitted",
        ));
    }
    #[cfg(ay_logging)]
    if s.cold.log_enabled {
        return Err(invalid(owner, "selected SAT model logging is not admitted"));
    }
    if s.has_empty_clause
        || s.arena.has_oversized_clause()
        || s.cold.oversized_clause_poison
        || s.cold.finalize_sat_fail_count != 0
        || s.cold.i2e.len() < s.num_vars
        || s.num_vars.checked_mul(2).is_none_or(|n| n > s.vals.len())
    {
        return Err(model_invalid(owner));
    }
    // Original ordinary summaries are no-ops under these unchanged selections.
    // No output flag is changed, and the pending decision writer stays attached
    // on success, matching ordinary SAT completion.
    owner.check()
}
