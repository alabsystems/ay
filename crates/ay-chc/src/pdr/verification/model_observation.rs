// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact submitted-model failure markers and inherited context term ceilings.

mod confirmation;

use super::*;
use crate::engines::ExternalInvariantValidation;

impl PdrSolver {
    pub(in crate::pdr) fn validation_memory(&mut self) -> crate::bmc::memory::Budget {
        let memory = crate::bmc::memory::Budget::capture(
            self.config.memory_budget,
            self.smt.term_memory_budget,
        );
        // A warm context predates the scope: tighten it explicitly as well.
        self.smt.set_term_memory_budget(memory.term_limit());
        memory
    }

    pub(super) fn unconfirmed_model() -> (PredicateId, ChcExpr, PredicateId, ChcExpr) {
        (
            PredicateId::new(0),
            ChcExpr::Bool(false),
            PredicateId::new(0),
            ChcExpr::Bool(false),
        )
    }

    pub(super) fn note_model_rejection(&mut self) {
        self.telemetry.model_validation_failure = Some(ExternalInvariantValidation::Rejected);
    }

    pub(super) fn note_original_model_refutation(&mut self) {
        self.telemetry.model_validation_failure = Some(ExternalInvariantValidation::Refuted);
    }

    pub(crate) fn observed_model_validation_failure(&self) -> Option<ExternalInvariantValidation> {
        self.telemetry.model_validation_failure
    }
}

#[cfg(test)]
mod tests;
