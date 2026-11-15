// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Shared ordinary learned insertion and asserting assignment. The counted
//! caller retains the analysis owner; this is not a complete search endpoint.

use super::*;
use crate::counted_storage::Result as AdmissionResult;
use ay_core::original_query::{CountedAdmission, CountedAdmissionError};
use std::convert::Infallible;

mod eager;
mod enqueue;
mod learning_trace;
pub(in crate::solver) mod prepare;

pub(in crate::solver) trait Policy {
    type Error;
    fn begin(&self, s: &mut Solver) -> Result<(), Self::Error>;
    fn insert(&self, s: &mut Solver, result: &mut ConflictResult)
        -> Result<ClauseRef, Self::Error>;
    fn enqueue(
        &self,
        s: &mut Solver,
        uip: Literal,
        reason: ClauseRef,
        jump: Option<Literal>,
    ) -> Result<(), Self::Error>;
}

pub(in crate::solver) struct Ordinary;
impl Policy for Ordinary {
    type Error = Infallible;
    fn begin(&self, s: &mut Solver) -> Result<(), Infallible> {
        s.set_diagnostic_pass(DiagnosticPass::Learning);
        Ok(())
    }
    fn insert(&self, s: &mut Solver, result: &mut ConflictResult) -> Result<ClauseRef, Infallible> {
        Ok(s.add_conflict_learned_clause(
            std::mem::take(&mut result.learned_clause),
            result.lbd,
            std::mem::take(&mut result.resolution_chain),
        ))
    }
    fn enqueue(
        &self,
        s: &mut Solver,
        uip: Literal,
        reason: ClauseRef,
        jump: Option<Literal>,
    ) -> Result<(), Infallible> {
        match jump {
            Some(other) => s.enqueue_binary_reason(uip, other),
            None => s.enqueue(uip, Some(reason)),
        }
        Ok(())
    }
}

pub(in crate::solver) struct Counted<'a>(pub(in crate::solver) &'a CountedAdmission);
impl Policy for Counted<'_> {
    type Error = CountedAdmissionError;
    fn begin(&self, s: &mut Solver) -> AdmissionResult<()> {
        // set_diagnostic_pass emits this exact event before changing context.
        // Counted I/O is fallible, never the ordinary expect/panic path.
        s.cold.diagnostic_pass = DiagnosticPass::Learning;
        s.learn_event_counted(
            TraceEvent::Inprocess {
                pass_code: Solver::diagnostic_pass_code(DiagnosticPass::Learning),
            },
            self.0,
        )
    }
    fn insert(&self, s: &mut Solver, result: &mut ConflictResult) -> AdmissionResult<ClauseRef> {
        s.add_conflict_learned_counted(result, self.0)
    }
    fn enqueue(
        &self,
        s: &mut Solver,
        uip: Literal,
        reason: ClauseRef,
        jump: Option<Literal>,
    ) -> AdmissionResult<()> {
        s.asserting_enqueue_counted(uip, reason, jump, self.0)
    }
}

impl Solver {
    pub(in crate::solver) fn learn_asserting_clause_admitted<P: Policy>(
        &mut self,
        result: &mut ConflictResult,
        actual_backtrack_level: u32,
        p: &P,
    ) -> Result<usize, P::Error> {
        let uip = result.learned_clause[0];
        p.begin(self)?;
        let jump_other =
            self.learned_binary_jump_reason(&result.learned_clause, actual_backtrack_level);
        let learned_ref = p.insert(self, result)?;
        self.clear_diagnostic_pass();
        self.update_lbd_ema(result.lbd);
        p.enqueue(self, uip, learned_ref, jump_other)?;
        Ok(learned_ref.index())
    }

    pub(in crate::solver) fn fix_learned_uip_at_root(&mut self, uip: Literal, actual: u32) {
        if actual == 0 && !self.var_lifecycle.is_inactive(uip.variable().index()) {
            self.fixed_count += 1;
            self.var_lifecycle.mark_fixed(uip.variable().index());
            self.l0_gc_dirty[uip.variable().index()] = true;
        }
    }
}
