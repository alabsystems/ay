// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::solver::conflict_analysis_minimize_lrat::root::Policy as Root;

impl Policy for root::Counted<'_> {
    fn enter_chain(&self, s: &Solver, roots: &[usize]) -> AdmissionResult<()> {
        self.work(16)?;
        if !s.cold.lrat_enabled
            || s.proof_manager.is_some()
            || s.min.minimize_flags.len() < s.num_vars
            || !s.min.lrat_to_clear.is_empty()
        {
            return Err(invalid(
                self.0,
                "counted unit chain requires retired trace-only scratch",
            ));
        }
        let end = s.trail_lim.first().copied().unwrap_or(s.trail.len());
        if end > s.trail.len() {
            return Err(invalid(
                self.0,
                "counted unit chain root prefix out of bounds",
            ));
        }
        for &var in roots {
            self.work(1)?;
            if var >= s.var_data.len() || s.var_data[var].level != 0 {
                return Err(invalid(self.0, "counted unit chain seed is not level zero"));
            }
        }
        let bound = u64::try_from(s.num_vars)
            .map_err(|_| invalid(self.0, "unit-chain counter overflow"))?;
        for value in [
            s.stats.lrat_unit_chain_root_trail_entries,
            s.stats.lrat_unit_chain_hints,
            s.stats.lrat_unit_chain_missing_hints,
        ] {
            value
                .checked_add(bound)
                .ok_or_else(|| invalid(self.0, "unit-chain counter overflow"))?;
        }
        s.stats
            .lrat_unit_chain_calls
            .checked_add(1)
            .ok_or_else(|| invalid(self.0, "unit-chain call counter overflow"))?;
        Ok(())
    }
    fn mark(&self, s: &mut Solver) -> AdmissionResult<()> {
        // Register before setting the flag, and prepay its quiet retirement.
        self.work(3)?;
        try_reserve(self.0, &mut s.min.lrat_to_clear, 1)
    }
    fn chain(&self, s: &mut Solver, id: u64) -> AdmissionResult<()> {
        s.conflict.prepare_counted_standard_chain(self.0)?;
        s.conflict.add_to_chain(id);
        Ok(())
    }
    fn sort(&self, values: &mut [(usize, Literal, u64)]) -> AdmissionResult<()> {
        // Sealed core ipnsort: two log partitions, small-sort <=32, then
        // heapsort; identical ordinary equal-key behavior and no heap buffer.
        let levels = (usize::BITS - values.len().leading_zeros()) as usize + 1;
        let work = values
            .len()
            .checked_mul(levels)
            .and_then(|n| n.checked_mul(64))
            .ok_or_else(|| self.0.refuse(CountedAdmissionError::WorkExhausted))?;
        let bytes = levels
            .checked_mul(256)
            .and_then(|n| n.checked_add(4096))
            .ok_or_else(|| self.0.refuse(CountedAdmissionError::StorageExhausted))?;
        self.0.admit(work, bytes)?;
        values.sort_unstable_by_key(|b| std::cmp::Reverse(b.0));
        Ok(())
    }
    fn new_filter(&self, len: usize) -> AdmissionResult<DetHashSet<Literal>> {
        filter::new(len, self.0)
    }
    fn filter(&self, values: &DetHashSet<Literal>) -> AdmissionResult<()> {
        filter::probe(values, self.0)
    }
}
