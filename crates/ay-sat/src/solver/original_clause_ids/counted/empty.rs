// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::solver::clause_add::terminal::Policy as _;
use crate::solver::conflict_analysis_minimize_lrat::root;

impl Fresh<'_> {
    pub(super) fn empty(&mut self, original_id: u64) -> Result<()> {
        let owner = self.owner;
        owner.admit(64, 0)?;
        if self.solver.veripb_hints_active() {
            return Err(invalid(
                owner,
                "selected empty-input hints are not admitted",
            ));
        }
        // This admission checks every selected proof writer/diagnostic mode,
        // counter and fixed proof emission tail before the shared kernel runs.
        root::Counted(owner).empty(self.solver)?;
        let id = self.next;
        let traced = self.solver.cold.lrat_enabled;
        let authority = FreshInputTraceEvent {
            id,
            prefix: self.prefix,
            previous: self.previous,
            kind: FreshEventKind::Empty,
            owner,
        };
        let hints: &[u64] = if traced {
            std::slice::from_ref(&original_id)
        } else {
            &[]
        };
        self.solver
            .publish_empty_clause(hints, Vec::new(), |s, actual, trace_hints| {
                owner.admit(16, 0)?;
                if actual != id || !trace_hints.is_empty() {
                    return Err(invalid(owner, "ordinary empty-input trace event changed"));
                }
                let trace = s
                    .cold
                    .clause_trace
                    .as_mut()
                    .ok_or_else(|| invalid(owner, "fresh empty-input trace detached"))?;
                let prepared = trace.prepare_counted_original(&authority, &[])?;
                owner.check()?;
                prepared.commit();
                Ok(())
            })?;
        if traced {
            self.next = id + 1;
            self.prefix += 1;
            self.previous = Some(id);
        }
        owner.check()
    }
}
