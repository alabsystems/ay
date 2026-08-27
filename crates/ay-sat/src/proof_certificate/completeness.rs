// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::ProofCertificate;
use crate::solver::backward_proof::BackwardProofResult;

/// Whether the producer reconstructed every proof dependency it expected.
///
/// This is reconstruction metadata, not a proof-checker verdict. Parsing LRAT
/// syntax does not establish that the steps derive a contradiction from a
/// particular CNF. Consumers that need proof authority must still run an
/// independent checker.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProofCompleteness {
    /// The producer supplied its complete reconstructed step stream.
    Complete,
    /// Complete reconstruction was not established, was unavailable, or has gaps.
    NotEstablished,
}

impl ProofCompleteness {
    pub(crate) const fn from_reconstruction(complete: bool) -> Self {
        if complete {
            Self::Complete
        } else {
            Self::NotEstablished
        }
    }

    /// Whether reconstruction completed without a known gap.
    #[must_use]
    pub const fn is_complete(self) -> bool {
        matches!(self, Self::Complete)
    }
}

impl ProofCertificate {
    pub(crate) fn from_backward_reconstruction(backward: BackwardProofResult) -> Self {
        Self::from_backward_result(
            backward.steps,
            ProofCompleteness::from_reconstruction(backward.complete),
        )
    }
}
