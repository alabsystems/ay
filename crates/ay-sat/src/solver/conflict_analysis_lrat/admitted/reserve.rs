// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

pub(super) fn entry(
    s: &Solver,
    lits: &[Literal],
    hints: &[u64],
    owner: &CountedAdmission,
) -> AdmissionResult<()> {
    owner.admit(32, 0)?;
    let Some(flags) = ay_core::captured_misc_cli_flags() else {
        return Err(invalid(
            owner,
            "learned insertion requires captured process configuration",
        ));
    };
    if flags.ab_triage_clause.is_some()
        || flags.ab_triage_var.is_some()
        || s.proof_manager.is_some()
        || s.cold.forward_checker.is_some()
        || !s.has_live_clause_trace()
        || s.cold.internal_lrat_enabled
        || s.cold.proof_vars_compacted
        || !s.veripb_hints_resolved_inactive()
        || s.cold.veripb_hints.derived.has_pending_emission()
        || !s.counted_learned_triage_inactive()
        || !s.counted_emission_triage_inactive()
        || s.should_record_fmla_learned_lrat_authority_fail_closed(hints)
        || s.cold.diagnostic_trace.is_some()
        || s.cold.proof_bookkeeping_budget.is_some()
        || lits.is_empty()
        || lits.len() > u16::MAX as usize
        || hints.is_empty()
    {
        return Err(invalid(
            owner,
            "selected learned proof or diagnostic operation is not admitted",
        ));
    }
    #[cfg(ay_logging)]
    if s.log_enabled {
        return Err(invalid(owner, "learned insertion logging is not admitted"));
    }
    for literal in lits {
        owner.admit(1, 0)?;
        if literal.variable().index() >= s.num_vars {
            return Err(invalid(
                owner,
                "learned literal outside original solver namespace",
            ));
        }
    }
    let pass = Solver::diagnostic_pass_code(DiagnosticPass::Learning) as usize;
    if s.cold.veripb_hints.adds_by_pass[pass] == u64::MAX
        || s.cold.veripb_hints.derived.red_by_pass[pass] == u64::MAX
    {
        return Err(invalid(owner, "learned proof statistics overflow"));
    }
    Ok(())
}

pub(super) fn sort(len: usize, owner: &CountedAdmission) -> AdmissionResult<()> {
    // Same standard unstable ordering; conservative introsort/heapsort envelope.
    let levels = (usize::BITS - len.leading_zeros()) as usize;
    let work = len
        .checked_mul(levels.saturating_add(1))
        .and_then(|n| n.checked_mul(64))
        .ok_or_else(|| owner.refuse(CountedAdmissionError::WorkExhausted))?;
    owner.admit(work, 0)
}

pub(super) fn watch_order(s: &Solver, len: usize, owner: &CountedAdmission) -> AdmissionResult<()> {
    // Highest-level watch selection plus the debug independent maximum scan.
    owner.admit(len.saturating_mul(2).saturating_add(4), 0)?;
    let tail_selected = ((6..=17).contains(&len) && s.cold.bcp_learned_617_tail_reorder)
        || (len == 18 && s.cold.bcp_learned_18_tail_reorder)
        || ((19..=63).contains(&len)
            && (s.cold.bcp_learned_1963_tail_reorder
                || s.cold.bcp_learned_1963_tail_reorder_swap_budget.is_some()));
    if tail_selected {
        // The existing insertion sort and optional inversion-count pass are
        // selected only for clauses of at most 63 literals.
        owner.admit(len.saturating_mul(len).saturating_mul(3), 0)?;
    }
    Ok(())
}

pub(super) fn tail(
    s: &mut Solver,
    lits: &[Literal],
    watches: Option<(Literal, Literal)>,
    owner: &CountedAdmission,
) -> AdmissionResult<()> {
    if let Some((first, second)) = watches {
        s.watches
            .reserve_counted_learned_pair(first, second, owner)?;
    }
    try_reserve(owner, &mut s.cold.learned_clause_trail, 1)?;
    if s.cold.learned_clause_trail.len() >= 1024 {
        owner.admit(s.cold.learned_clause_trail.len().saturating_add(1), 0)?;
    }
    // Subsumption dirty marking and fixed header/watch/counter effects.
    owner.admit(lits.len().saturating_add(32), 0)?;
    owner.check()
}
