// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Atomic admission for the real standard and IC3 backtrack kernels.
//!
//! All possible work and growth are admitted before phase/trail/frontier
//! mutation. A refused preflight can change capacities, never logical state.
//! Once admitted, the unchanged kernel completes without polling halfway
//! through compaction. The final fence follows disposal of planning scratch;
//! a stop at that fence leaves a consistent completed backtrack, not a partial
//! trail. This transaction does not authorize analysis, preprocessing, other
//! restart maintenance, or a complete counted solve.

use super::*;
use crate::counted_storage::Result as AdmissionResult;
use ay_core::original_query::{CountedAdmission, CountedAdmissionError};
use std::convert::Infallible;

mod prepare;
#[cfg(test)]
mod tests;

#[derive(Clone, Copy)]
pub(in crate::solver::backtrack) enum Lane {
    Standard { save_phases: bool },
    Ic3,
}

pub(in crate::solver::backtrack) trait Policy {
    type Error;
    fn prepare(&mut self, s: &mut Solver, target: u32, lane: Lane) -> Result<(), Self::Error>;
    #[cfg(any(debug_assertions, feature = "relevancy-frontier-invariants"))]
    fn check_frontier(&mut self, s: &mut Solver);
}

pub(in crate::solver::backtrack) struct Ordinary;

impl Policy for Ordinary {
    type Error = Infallible;
    fn prepare(&mut self, _: &mut Solver, _: u32, _: Lane) -> Result<(), Infallible> {
        Ok(())
    }
    #[cfg(any(debug_assertions, feature = "relevancy-frontier-invariants"))]
    fn check_frontier(&mut self, s: &mut Solver) {
        s.debug_assert_relevancy_frontier_exact_after_fold();
    }
}

struct Counted {
    owner: CountedAdmission,
    #[cfg(any(debug_assertions, feature = "relevancy-frontier-invariants"))]
    reference: Vec<bool>,
}

impl Policy for Counted {
    type Error = CountedAdmissionError;
    fn prepare(&mut self, s: &mut Solver, target: u32, lane: Lane) -> AdmissionResult<()> {
        prepare::transaction(s, target, lane, &self.owner)?;
        if target < s.decision_level {
            // Restore the borrowed cache on every preflight result. Reservations
            // do not consume its check quota, invalidate it, or change counters.
            let mut frontier = std::mem::take(&mut s.relevancy_frontier);
            let result = frontier.prepare_backtrack(s, target, lane.start(s, target), &self.owner);
            s.relevancy_frontier = frontier;
            #[cfg(any(debug_assertions, feature = "relevancy-frontier-invariants"))]
            {
                self.reference = result?;
            }
            #[cfg(not(any(debug_assertions, feature = "relevancy-frontier-invariants")))]
            result?;
        }
        self.owner.check()
    }
    #[cfg(any(debug_assertions, feature = "relevancy-frontier-invariants"))]
    fn check_frontier(&mut self, s: &mut Solver) {
        s.debug_assert_relevancy_frontier_exact_after_fold_with(&mut self.reference);
    }
}

impl Lane {
    fn start(self, s: &Solver, target: u32) -> usize {
        match self {
            Self::Standard { .. } => s.trail_lim[target as usize],
            Self::Ic3 if target == 0 => 0,
            Self::Ic3 => s.trail_lim[target as usize - 1],
        }
    }
}

impl Solver {
    /// Fallible real backtrack; callers must propagate refusal before resuming
    /// search. Legacy analysis/preprocessing callers remain separately audited.
    pub(in crate::solver) fn backtrack_counted(
        &mut self,
        target: u32,
    ) -> Result<(), SatUnknownReason> {
        self.backtrack_with_owner(target, Lane::Standard { save_phases: true })
    }

    pub(in crate::solver) fn backtrack_ic3_counted(
        &mut self,
        target: u32,
    ) -> Result<(), SatUnknownReason> {
        self.backtrack_with_owner(target, Lane::Ic3)
    }

    fn backtrack_with_owner(&mut self, target: u32, lane: Lane) -> Result<(), SatUnknownReason> {
        let Some(owner) = self.cold.counted_admission.clone() else {
            match lane {
                Lane::Standard { save_phases } => self.backtrack_ordinary(target, save_phases),
                Lane::Ic3 => self.backtrack_ic3(target),
            }
            return Ok(());
        };
        let result = {
            let mut policy = Counted {
                owner: owner.clone(),
                #[cfg(any(debug_assertions, feature = "relevancy-frontier-invariants"))]
                reference: Vec::new(),
            };
            match lane {
                Lane::Standard { save_phases } => {
                    self.backtrack_core(target, save_phases, &mut policy)
                }
                Lane::Ic3 => self.backtrack_ic3_admitted(target, &mut policy),
            }
        };
        // Planning buffers have been dropped before the publication fence.
        owner
            .check()
            .map_err(crate::solver::counted_admission::reason)?;
        result.map_err(crate::solver::counted_admission::reason)
    }
}

/// Bounds have checked arithmetic and a sticky refusal, never saturation into
/// an apparently affordable amount. One work unit denotes a bounded visit.
#[cfg(any(debug_assertions, feature = "relevancy-frontier-invariants"))]
pub(in crate::solver) fn admit_visits(
    owner: &CountedAdmission,
    count: usize,
    passes: usize,
) -> AdmissionResult<()> {
    let work = count
        .checked_mul(passes)
        .ok_or_else(|| owner.refuse(CountedAdmissionError::WorkExhausted))?;
    owner.admit(work, 0)
}
