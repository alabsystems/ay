// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::counted_storage::try_reserve;
use crate::decision_trace::counted_decision::invalid;

impl Solver {
    pub(in crate::solver) fn asserting_enqueue_counted(
        &mut self,
        lit: Literal,
        reason: ClauseRef,
        jump: Option<Literal>,
        owner: &CountedAdmission,
    ) -> AdmissionResult<()> {
        self.prepare_asserting_enqueue_counted(lit, reason, jump, owner)?;
        self.enqueue(lit, Some(reason));
        owner.check()
    }

    /// Reserve the actual asserting assignment before an enclosing dispatch
    /// transaction changes root-fixed metadata. No assignment is performed.
    pub(in crate::solver) fn prepare_asserting_enqueue_counted(
        &mut self,
        lit: Literal,
        reason: ClauseRef,
        jump: Option<Literal>,
        owner: &CountedAdmission,
    ) -> AdmissionResult<()> {
        owner.admit(48, 0)?;
        let var = lit.variable().index();
        if var >= self.num_vars
            || self.trail.len() >= self.num_vars
            || self.var_is_assigned(var)
            || self.var_lifecycle.is_removed(var)
            || jump.is_some()
            || self.two_stage_clause_management
        {
            return Err(invalid(owner, "invalid or unadmitted asserting assignment"));
        }
        // Live ClauseTrace chooses ordinary long-clause reasons even for
        // binaries. Do not enable/disable the jump-reason option to force it.
        let lits = self.arena.literals(reason.index());
        let mut found = false;
        for &other in lits {
            owner.admit(2, 0)?; // validation and assignment_level's actual scan
            if other.variable().index() >= self.num_vars {
                return Err(invalid(owner, "asserting reason literal is out of bounds"));
            }
            if other == lit {
                found = true;
            } else if self.lit_val(other) >= 0 {
                return Err(invalid(owner, "learned reason is not asserting"));
            }
        }
        if !found {
            return Err(invalid(owner, "learned reason omits its UIP"));
        }
        try_reserve(owner, &mut self.trail, 1)?;
        #[cfg(debug_assertions)]
        if (self.trail.len() + 1) & 0x3ff == 0 {
            owner.admit(self.num_vars, 0)?;
        }
        if self.fixed_count == i64::MAX {
            return Err(invalid(owner, "fixed-variable counter overflow"));
        }
        owner.check()
    }
}
