// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Checked branch-transfer evidence for provenance-authenticated ITE repair.

use ay_core::TermId;

use super::proof_trust_surgery_ite::ProvenanceFarkasLemma;

pub(super) enum ProvenanceBranchLemma {
    Farkas(ProvenanceFarkasLemma),
    Transitive {
        clause: Vec<TermId>,
        supports: Vec<TermId>,
    },
}

impl ProvenanceBranchLemma {
    pub(super) fn clause(&self) -> &[TermId] {
        match self {
            Self::Farkas(lemma) => &lemma.clause,
            Self::Transitive { clause, .. } => clause,
        }
    }

    pub(super) fn supports(&self) -> &[TermId] {
        match self {
            Self::Farkas(lemma) => &lemma.supports,
            Self::Transitive { supports, .. } => supports,
        }
    }
}

impl From<ProvenanceFarkasLemma> for ProvenanceBranchLemma {
    fn from(lemma: ProvenanceFarkasLemma) -> Self {
        Self::Farkas(lemma)
    }
}
