// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::vsids::counted_analysis::ActivityStage;

pub(super) struct Counted<'a>(pub(super) &'a CountedAdmission);

impl Policy for Counted<'_> {
    type Error = SatUnknownReason;

    fn backtrack(&mut self, s: &mut Solver, level: u32) -> Result<(), SatUnknownReason> {
        s.backtrack_counted(level)
    }
    fn level(
        &mut self,
        s: &mut Solver,
        reference: ClauseRef,
    ) -> Result<(u32, Option<Literal>), SatUnknownReason> {
        s.find_conflict_level_admitted(reference, &level::Counted(self.0))
            .map_err(counted_admission::reason)
    }
    fn unit(&mut self, s: &mut Solver, reference: ClauseRef) -> Result<bool, SatUnknownReason> {
        unit::install(s, reference, self.0).map_err(counted_admission::reason)
    }
    fn force(
        &mut self,
        s: &mut Solver,
        reference: ClauseRef,
        lit: Literal,
        level: u32,
    ) -> Result<(), SatUnknownReason> {
        self.0.admit(16, 0).map_err(counted_admission::reason)?;
        s.prepare_asserting_enqueue_counted(lit, reference, None, self.0)
            .map_err(counted_admission::reason)?;
        // No observer between the root mark and the prepaid actual enqueue.
        s.conflict_dispatch_force(reference, lit, level);
        self.0.check().map_err(counted_admission::reason)
    }
    fn note_forced(&mut self, s: &mut Solver, kind: ForcedKind) -> Result<(), SatUnknownReason> {
        self.0.admit(24, 0).map_err(counted_admission::reason)?;
        s.conflict_dispatch_note_forced(kind);
        self.0.check().map_err(counted_admission::reason)
    }
    fn terminal(&mut self, _: &mut Solver, _: ClauseRef) -> Result<(), SatUnknownReason> {
        Err(refusal(
            self.0,
            "selected root-conflict proof emission is not admitted",
        ))
    }
    fn decay(&mut self, s: &mut Solver) -> Result<(), SatUnknownReason> {
        match s.active_branch_heuristic {
            BranchHeuristic::Evsids => s.vsids.decay_counted(ActivityStage::Evsids, self.0),
            BranchHeuristic::Chb => s.vsids.decay_counted(ActivityStage::DormantEvsids, self.0),
            BranchHeuristic::Vmtf => self.0.admit(1, 0),
        }
        .map_err(counted_admission::reason)
    }
}
