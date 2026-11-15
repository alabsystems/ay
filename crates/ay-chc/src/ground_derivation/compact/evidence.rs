// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! A carried candidate keeps its complete values AND the original allowance.
//! Presence is not authority: every accepting boundary replays the original.

use super::{CompactDerivation, Owner, Result};

pub(crate) struct CompactEvidence {
    derivation: CompactDerivation,
    owner: super::owner::RetainedOwner,
}

impl std::fmt::Debug for CompactEvidence {
    fn fmt(&self, out: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        out.debug_struct("CompactEvidence")
            .field("nodes", &self.derivation.arena.nodes().len())
            .field("steps", &self.derivation.steps.len())
            .finish_non_exhaustive()
    }
}

impl CompactEvidence {
    pub(crate) fn new(derivation: CompactDerivation, owner: Owner<'static>) -> Self {
        Self {
            derivation,
            owner: owner.into_retained(),
        }
    }

    pub(crate) fn derivation(&self) -> &CompactDerivation {
        &self.derivation
    }

    pub(crate) fn owner(&self) -> Owner<'static> {
        self.owner.owner()
    }

    pub(crate) fn validate(&self, problem: &crate::ChcProblem) -> Result<()> {
        super::validate(problem, &self.derivation, &mut self.owner())
    }
}
