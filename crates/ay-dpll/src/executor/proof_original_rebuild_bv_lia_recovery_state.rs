// Copyright 2026 Andrew Yates, Inc.
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Permit-bound routing state for exact definitional-UF rejection recovery.

use super::Executor;
use crate::executor_types::SolveResult;

#[derive(Default)]
pub(in crate::executor) struct ExactIteUfDefinitionRecovery {
    pub(in crate::executor) armed: bool,
    pub(in crate::executor) rejected: bool,
    pub(in crate::executor) attempted: bool,
}

impl ExactIteUfDefinitionRecovery {
    pub(in crate::executor) fn begin(&mut self, armed: bool) {
        *self = Self {
            armed,
            ..Self::default()
        };
    }

    /// True only after the pure exact-root checker independently established
    /// UNSAT. Callers may stop disposable SAT-recovery trajectories, but this
    /// remains a routing hint: the restored outer seam reauthenticates and
    /// strictly checks its proof before changing a verdict.
    pub(in crate::executor) fn ready(&self) -> bool {
        self.armed && self.rejected
    }

    pub(in crate::executor) fn clear(&mut self) {
        *self = Self::default();
    }

    pub(in crate::executor) fn take_rejected_and_disarm(&mut self) -> bool {
        self.armed = false;
        std::mem::take(&mut self.rejected)
    }
}

impl Executor {
    /// Arm only an opaque authored-plain query; all other origins remain inert.
    pub(in crate::executor) fn begin_exact_ite_uf_definition_recovery(
        &mut self,
        authored_plain: bool,
    ) {
        self.ite_uf_definition_recovery
            .begin(authored_plain && crate::quant_unit_authority::consequence_replay_enabled());
    }

    /// Consume the hint only after temporary windows restore, then run the
    /// independent exact-root proof completion.
    pub(in crate::executor) fn complete_exact_ite_uf_definition_recovery(
        &mut self,
        proposed: SolveResult,
        authored_plain: bool,
    ) -> SolveResult {
        let rejected = self.ite_uf_definition_recovery.take_rejected_and_disarm();
        if proposed.is_unknown() && authored_plain && rejected {
            self.try_complete_exact_ite_uf_definition_rejection(proposed)
        } else {
            proposed
        }
    }
}
