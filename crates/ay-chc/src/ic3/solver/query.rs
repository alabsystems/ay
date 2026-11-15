// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SAT refusal is terminal for an IC3 attempt, not a missing cube or core.

use super::{Ic3Result, Ic3Solver};
use ay_sat::{AssumeResult, Literal, SolverAssumeResult};

#[derive(Debug, PartialEq, Eq)]
pub(in crate::ic3) struct QueryStopped;

impl Ic3Solver {
    pub(in crate::ic3) fn deadline(&self) -> Option<ay_core::time::Instant> {
        self.deadline
    }

    pub(in crate::ic3) fn init_query(
        &mut self,
        assumptions: &[Literal],
    ) -> Result<AssumeResult, QueryStopped> {
        if self.resource_exhausted() {
            return Err(QueryStopped);
        }
        let owner = self.resource_poll.clone();
        let result = self
            .init_solver
            .solve_incremental_ic3_interruptible(assumptions, || {
                owner.as_ref().is_some_and(|poll| !poll())
            });
        self.admit_query(result)
    }

    pub(in crate::ic3) fn transition_query(
        &mut self,
        assumptions: &[Literal],
    ) -> Result<AssumeResult, QueryStopped> {
        if self.resource_exhausted() {
            return Err(QueryStopped);
        }
        let owner = self.resource_poll.clone();
        let result = self
            .solver
            .solve_incremental_ic3_interruptible(assumptions, || {
                owner.as_ref().is_some_and(|poll| !poll())
            });
        self.admit_query(result)
    }

    pub(in crate::ic3) fn admit_query(
        &self,
        result: SolverAssumeResult,
    ) -> Result<AssumeResult, QueryStopped> {
        let result = result.into_inner();
        if self.resource_exhausted()
            || !matches!(result, AssumeResult::Sat(_) | AssumeResult::Unsat(..))
        {
            self.query_stopped.set(true);
            return Err(QueryStopped);
        }
        Ok(result)
    }

    pub(in crate::ic3) fn after_query_cleanup(
        &self,
        result: Result<AssumeResult, QueryStopped>,
    ) -> Result<AssumeResult, QueryStopped> {
        if self.resource_exhausted() {
            Err(QueryStopped)
        } else {
            result
        }
    }

    // Called after the search worker's obligations and other scratch have been
    // destroyed. This also rejects a late fixpoint or initial counterexample.
    pub(super) fn admit_result(&self, result: Ic3Result) -> Ic3Result {
        if self.resource_exhausted() {
            drop(result);
            Ic3Result::Unknown
        } else {
            result
        }
    }
}

#[cfg(test)]
mod tests;
