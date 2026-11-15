// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Shared finalization policy. Counted use requires the exclusive ordinary
//! analysis guard: this module never grants a verdict, model or proof.

use super::*;
use crate::conflict::ConflictAnalyzer;
use crate::counted_storage::{try_reserve, Result as AdmissionResult};
use crate::decision_trace::counted_decision::invalid;
use crate::vsids::counted_analysis::ActivityStage;
use ay_core::original_query::{CountedAdmission, CountedAdmissionError};
use std::convert::Infallible;

pub(in crate::solver) use conflict_analysis_minimize::admitted::Ordinary;
mod counted;
pub(in crate::solver) use counted::prepare_scope;
mod minimize;
mod shrink;
mod sort;
#[cfg(test)]
mod tests;

pub(in crate::solver) struct Counted<'a>(pub(in crate::solver) &'a CountedAdmission);

pub(in crate::solver) trait Policy: shrink::SuperPolicy {
    fn enter_finalize(&self, s: &mut Solver, roots: &[usize]) -> Result<(), Self::Error>;
    fn removed_snapshot(&self) -> Result<(), Self::Error>;
    fn root_phase(&self, s: &mut Solver, uip: Literal, roots: &[usize]) -> Result<(), Self::Error>;
    fn reason_frame(&self) -> Result<(), Self::Error>;
    fn analysis_seen(&self, conflict: &mut ConflictAnalyzer) -> Result<(), Self::Error>;
    fn scale(&self, value: usize, factor: usize, add: usize) -> Result<usize, Self::Error>;
    fn activity(&self, s: &mut Solver, stage: ActivityStage) -> Result<(), Self::Error>;
    fn prepare_bump_order(&self, s: &mut Solver) -> Result<(), Self::Error>;
    fn sort_bumps(&self, values: &mut [(u64, usize)]) -> Result<(), Self::Error>;
    fn result(&self, s: &mut Solver) -> Result<(), Self::Error>;
    fn learned_order(&self, values: &mut [Literal], data: &[VarData]) -> Result<(), Self::Error>;
    fn diagnostics(&self, len: usize) -> Result<(), Self::Error>;
    #[cfg(debug_assertions)]
    fn debug_copy(&self, values: &[Literal]) -> Result<Vec<Literal>, Self::Error>;
}

impl Policy for Ordinary {
    fn root_phase(&self, s: &mut Solver, uip: Literal, roots: &[usize]) -> Result<(), Infallible> {
        conflict_analysis_lrat_unit_chain::admitted::finalize_roots(
            s,
            uip,
            roots,
            &conflict_analysis_minimize_lrat::root::Ordinary,
        )
    }
    fn enter_finalize(&self, _: &mut Solver, _: &[usize]) -> Result<(), Infallible> {
        Ok(())
    }
    fn removed_snapshot(&self) -> Result<(), Infallible> {
        Ok(())
    }
    fn reason_frame(&self) -> Result<(), Infallible> {
        Ok(())
    }
    fn analysis_seen(&self, _: &mut ConflictAnalyzer) -> Result<(), Infallible> {
        Ok(())
    }
    fn scale(&self, value: usize, factor: usize, add: usize) -> Result<usize, Infallible> {
        Ok(value * factor + add)
    }
    fn activity(&self, s: &mut Solver, stage: ActivityStage) -> Result<(), Infallible> {
        let vars = s.conflict.analyzed_vars();
        match stage {
            ActivityStage::Chb => {
                s.vsids.chb_bump_batch(vars);
                s.vsids.chb_on_conflict();
            }
            ActivityStage::Evsids => s.vsids.batch_bump(vars, &s.vals, true),
            ActivityStage::DormantEvsids => {
                s.vsids.bump_evsids_score_dormant_batch(vars);
                for &var in vars {
                    s.vsids.bump_vmtf_order_only(Variable(var as u32), &s.vals);
                }
            }
            ActivityStage::Vmtf => s
                .vsids
                .batch_bump_queue_sorted(&s.bump_order_sort_buf, &s.vals),
        }
        Ok(())
    }
    fn prepare_bump_order(&self, _: &mut Solver) -> Result<(), Infallible> {
        Ok(())
    }
    fn sort_bumps(&self, values: &mut [(u64, usize)]) -> Result<(), Infallible> {
        values.sort_unstable_by_key(|&(order, _)| order);
        Ok(())
    }
    fn result(&self, _: &mut Solver) -> Result<(), Infallible> {
        Ok(())
    }
    fn learned_order(&self, values: &mut [Literal], data: &[VarData]) -> Result<(), Infallible> {
        values.sort_by_key(|lit| std::cmp::Reverse(data[lit.variable().index()].level));
        Ok(())
    }
    fn diagnostics(&self, _: usize) -> Result<(), Infallible> {
        Ok(())
    }
    #[cfg(debug_assertions)]
    fn debug_copy(&self, values: &[Literal]) -> Result<Vec<Literal>, Infallible> {
        Ok(values.to_vec())
    }
}

/// Quiet cleanup after the core guard has acquired retired minimizer/shrink
/// scratch. Every dirty registration prepays removal; fixed Reap cleanup is
/// prepaid at the guard entry, even if failure occurs before shrinking starts.
pub(in crate::solver) fn retire(s: &mut Solver) {
    for &var in &s.min.lrat_to_clear {
        if let Some(flags) = s.min.minimize_flags.get_mut(var) {
            *flags &= !(LRAT_A | LRAT_B);
        }
    }
    s.min.lrat_to_clear.clear();
    for &var in &s.min.minimize_to_clear {
        if let Some(flags) = s.min.minimize_flags.get_mut(var) {
            *flags = 0;
        }
    }
    s.min.minimize_to_clear.clear();
    for &level in &s.min.minimize_levels_to_clear {
        if let Some(entry) = s.min.minimize_level_seen.get_mut(level as usize) {
            *entry = minimization_state::LevelSeen::EMPTY;
        }
    }
    s.min.minimize_levels_to_clear.clear();
    s.conflict.clause_buf_mut().clear();
    s.ws_shrink_entries.clear();
    s.ws_shrink_result.clear();
    s.ws_shrink_block_lits.clear();
    s.ws_shrink_chain.clear();
    s.min.shrink_walked.clear();
    s.reap.clear();
    s.bump_order_sort_buf.clear();
}
