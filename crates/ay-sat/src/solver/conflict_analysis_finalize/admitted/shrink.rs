// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::solver::reap::Reap;
pub(in crate::solver) use crate::solver::shrink::admitted::Policy as SuperPolicy;

impl SuperPolicy for Counted<'_> {
    const COUNTED: bool = true;
    fn prepare(&self, s: &Solver) -> AdmissionResult<()> {
        self.0.admit(8, 0)?;
        if !s.ws_shrink_entries.is_empty()
            || !s.ws_shrink_result.is_empty()
            || !s.ws_shrink_block_lits.is_empty()
            || !s.ws_shrink_chain.is_empty()
            || !s.min.shrink_walked.is_empty()
            || !s.reap.is_empty()
        {
            return Err(invalid(self.0, "ordinary shrink scratch is not retired"));
        }
        Ok(())
    }
    fn reserve<T>(&self, values: &mut Vec<T>, additional: usize) -> AdmissionResult<()> {
        try_reserve(self.0, values, additional)
    }
    fn sort_entries(&self, entries: &mut [(u32, usize, usize)]) -> AdmissionResult<()> {
        sort::prepay_unstable(entries.len(), self.0)?;
        <Ordinary as SuperPolicy>::sort_entries(&Ordinary, entries).map_err(|never| match never {})
    }
    fn push(&self, reap: &mut Reap, value: u32) -> AdmissionResult<()> {
        reap.push_counted(value, self.0)
    }
    fn pop(&self, reap: &mut Reap) -> AdmissionResult<u32> {
        reap.pop_counted(self.0)
    }
    fn literal(&self, s: &Solver, lit: Literal) -> AdmissionResult<()> {
        self.0.admit(1, 0)?;
        minimize::bounded_literal(s, lit, self.0)
    }
    fn seen(&self, s: &mut Solver) -> AdmissionResult<()> {
        s.conflict.prepare_counted_ic3_seen(self.0)
    }
    fn open(&self, value: u32) -> AdmissionResult<()> {
        self.0.admit(1, 0)?;
        if value == u32::MAX {
            return Err(invalid(self.0, "ordinary shrink open counter overflow"));
        }
        Ok(())
    }
    fn chain(&self, _: &mut Solver, _: u64) -> AdmissionResult<()> {
        Err(invalid(
            self.0,
            "ordinary counted shrink proof chain is not admitted",
        ))
    }
}
