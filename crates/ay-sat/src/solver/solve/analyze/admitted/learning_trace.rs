// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::decision_trace::counted_decision::invalid;

impl Solver {
    pub(in crate::solver) fn learn_event_counted(
        &mut self,
        event: TraceEvent,
        owner: &CountedAdmission,
    ) -> AdmissionResult<()> {
        owner.admit(4, 0)?;
        if let Some(replay) = &self.cold.replay_trace {
            replay.admit_learning_event(&event, owner)?;
        }
        if let Some(writer) = &self.cold.decision_trace {
            writer.admit_learning_event(&event, owner)?;
        }
        owner.check()?;
        if let Some(replay) = &mut self.cold.replay_trace {
            if !replay.commit_admitted_learning_event(&event) {
                return Err(invalid(owner, "learning replay changed after admission"));
            }
        }
        if let Some(writer) = &mut self.cold.decision_trace {
            writer
                .write_event(&event)
                .map_err(|_| invalid(owner, "counted learning trace write failed"))?;
        }
        owner.check()
    }
}
