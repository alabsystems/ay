// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::solver::reap::Reap;

impl crate::solver::shrink::admitted::Policy for Counted<'_> {
    const COUNTED: bool = true;

    fn prepare(&self, s: &Solver) -> AdmissionResult<()> {
        self.0.admit(12, 0)?;
        if !s.ws_shrink_entries.is_empty()
            || !s.ws_shrink_result.is_empty()
            || !s.ws_shrink_block_lits.is_empty()
            || !s.ws_shrink_chain.is_empty()
            || !s.min.shrink_walked.is_empty()
            || !s.reap.is_empty()
        {
            return Err(invalid(
                self.0,
                "counted block shrinking requires retired scratch",
            ));
        }
        Ok(())
    }

    fn reserve<T>(&self, values: &mut Vec<T>, additional: usize) -> AdmissionResult<()> {
        try_reserve(self.0, values, additional)
    }

    fn sort_entries(&self, entries: &mut [(u32, usize, usize)]) -> AdmissionResult<()> {
        sort::by_block(entries, self.0)
    }

    fn push(&self, reap: &mut Reap, value: u32) -> AdmissionResult<()> {
        reap.push_counted(value, self.0)
    }

    fn pop(&self, reap: &mut Reap) -> AdmissionResult<u32> {
        reap.pop_counted(self.0)
    }

    fn literal(&self, s: &Solver, lit: Literal) -> AdmissionResult<()> {
        self.0.admit(1, 0)?;
        validate_literal(s, lit, self.0)
    }

    fn seen(&self, s: &mut Solver) -> AdmissionResult<()> {
        s.conflict.prepare_counted_ic3_seen(self.0)
    }

    fn open(&self, count: u32) -> AdmissionResult<()> {
        self.0.admit(1, 0)?;
        if count == u32::MAX {
            return Err(invalid(self.0, "counted block open counter overflow"));
        }
        Ok(())
    }

    fn chain(&self, _: &mut Solver, _: u64) -> AdmissionResult<()> {
        // The current scoped caller is proof-free. Ordinary/proof calls use
        // the same engine with their real chain append, never this policy.
        Err(invalid(
            self.0,
            "counted shrink proof-chain attachment is not admitted",
        ))
    }
}

mod sort;
