// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

pub(super) fn entry(
    s: &Solver,
    reference: ClauseRef,
    owner: &CountedAdmission,
) -> Result<(), SatUnknownReason> {
    owner.admit(96, 0).map_err(counted_admission::reason)?;
    let Some(flags) = ay_core::captured_misc_cli_flags() else {
        return Err(refusal(
            owner,
            "dispatch requires captured process configuration",
        ));
    };
    if s.cold.ic3_mode
        || s.decision_level as usize > s.num_vars
        || s.trail_lim.len() != s.decision_level as usize
        || s.trail.len() > s.num_vars
        || s.num_vars > (u32::MAX / 4) as usize
        || s.fixed_count > i64::MAX - 2
        || s.stats.forced_backtracks == u64::MAX
        || !s.has_live_clause_trace()
        || s.proof_manager.is_some()
        || s.cold.internal_lrat_enabled
        || s.cold.proof_bookkeeping_budget.is_some()
        || s.cold.backward_proof_limits.is_some()
        || s.cold.backward_proof_failure.is_some()
        || s.veripb_hints_cached_active()
        || s.two_stage_clause_management
        || flags.ab_triage_var.is_some()
        || s.cold.trace_ext_conflict
        || s.cold.diagnostic_trace.is_some()
    {
        return Err(refusal(
            owner,
            "selected dispatch state or output is not admitted",
        ));
    }
    #[cfg(ay_logging)]
    if s.log_enabled {
        return Err(refusal(owner, "dispatch logging is not admitted"));
    }
    // Validate the exact internal BCP/theory reference before unchecked value
    // reads. Bounds checks do not pretend to authenticate arbitrary offsets.
    level::Policy::enter(&level::Counted(owner), s, reference)
        .map_err(counted_admission::reason)?;
    owner.check().map_err(counted_admission::reason)
}
