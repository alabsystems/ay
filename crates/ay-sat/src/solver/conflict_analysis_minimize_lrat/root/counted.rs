// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::solver::conflict_analysis::triage_enabled;

pub(in crate::solver) struct Counted<'a>(pub(in crate::solver) &'a CountedAdmission);

impl Policy for Counted<'_> {
    type Error = CountedAdmissionError;
    fn owner(&self) -> Option<&CountedAdmission> {
        Some(self.0)
    }
    fn work(&self, n: usize) -> AdmissionResult<()> {
        self.0.admit(n, 0)
    }
    fn reserve<T>(&self, values: &mut Vec<T>, n: usize) -> AdmissionResult<()> {
        try_reserve(self.0, values, n)
    }
    fn enter(&self, s: &mut Solver) -> AdmissionResult<()> {
        self.work(64)?;
        if ay_core::captured_misc_cli_flags().is_none() {
            return Err(invalid(
                self.0,
                "counted root configuration was not captured",
            ));
        }
        if !s.cold.lrat_enabled
            || !s.has_live_clause_trace()
            || s.proof_manager.is_some()
            || s.cold.forward_checker.is_some()
            || s.cold.proof_vars_compacted
            || !s.veripb_hints_resolved_inactive()
            || s.cold.veripb_hints.derived.has_pending_emission()
            || s.cold.proof_bookkeeping_budget.is_some()
            || triage_enabled()
            || !s.counted_emission_triage_inactive()
        {
            return Err(invalid(
                self.0,
                "counted root materialization requires the trace-only emission route",
            ));
        }
        if s.num_vars != s.var_data.len()
            || s.trail.len() > s.num_vars
            || s.vals.len() < s.num_vars.saturating_mul(2)
            || s.unit_proof_sign.len() < s.unit_proof_id.len()
            || s.cold.level0_proof_sign.len() < s.cold.level0_proof_id.len()
        {
            return Err(invalid(
                self.0,
                "counted root materialization state is out of bounds",
            ));
        }
        let end = s.trail_lim.first().copied().unwrap_or(s.trail.len());
        if end > s.trail.len() {
            return Err(invalid(
                self.0,
                "counted root trail prefix is out of bounds",
            ));
        }
        let pins = &s.cold.lrat_level0_unit_materialize_pinned;
        self.work(pins.len().saturating_add(1))?;
        if pins.windows(2).any(|pair| pair[0] >= pair[1]) {
            return Err(invalid(
                self.0,
                "counted root retry pins are not strictly ordered",
            ));
        }
        let bound = pins
            .len()
            .checked_add(end)
            .and_then(|n| n.checked_add(1))
            .ok_or_else(|| invalid(self.0, "counted root pass size overflow"))?;
        let amount =
            u64::try_from(bound).map_err(|_| invalid(self.0, "counted root counter overflow"))?;
        for value in [
            s.stats.lrat_materialize_calls,
            s.stats.lrat_materialize_incomplete_chains,
            s.stats.lrat_materialize_root_trail_entries,
        ] {
            value
                .checked_add(amount)
                .ok_or_else(|| invalid(self.0, "counted root counter overflow"))?;
        }
        self.work(s.cold.veripb_hints.adds_by_pass.len().saturating_mul(2))?;
        for &value in s
            .cold
            .veripb_hints
            .adds_by_pass
            .iter()
            .chain(s.cold.veripb_hints.derived.red_by_pass.iter())
        {
            value
                .checked_add(amount)
                .ok_or_else(|| invalid(self.0, "counted root emission counter overflow"))?;
        }
        // Scratch and exceptional trace-provenance retirement are prepaid.
        let cleanup = pins
            .capacity()
            .checked_add(s.cold.lrat_materialize_hints_buf.capacity())
            .and_then(|n| {
                n.checked_add(
                    s.live_clause_trace()
                        .map_or(0, |t| t.scope_assumptions_capacity()),
                )
            })
            .and_then(|n| n.checked_add(32))
            .ok_or_else(|| self.0.refuse(CountedAdmissionError::WorkExhausted))?;
        self.work(cleanup)
    }
    fn record(&self, s: &mut Solver, lit: Literal) -> AdmissionResult<()> {
        // Each original ID recorder may binary-search/shift the live pin list.
        // It is separate from the detached retry vector, exactly as ordinary.
        let len = s.cold.lrat_level0_unit_materialize_pinned.len();
        self.work(len.saturating_add(16))?;
        let var = lit.variable().index();
        if !s.cold.lrat_enabled
            || var >= s.num_vars
            || s.var_data[var].level != 0
            || !s.var_is_assigned(var)
        {
            return Ok(());
        }
        let pos = s.var_data[var].trail_pos as usize;
        let end = s.trail_lim.first().copied().unwrap_or(s.trail.len());
        if pos >= end
            || pos >= s.cold.lrat_level0_unit_materialize_cursor
            || s.cold
                .lrat_level0_unit_materialize_pinned
                .binary_search(&pos)
                .is_ok()
        {
            return Ok(());
        }
        self.reserve(&mut s.cold.lrat_level0_unit_materialize_pinned, 1)
    }
}
