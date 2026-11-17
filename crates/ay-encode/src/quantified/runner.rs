// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_chc::quantified::QuantifiedChcResult;
use std::panic::AssertUnwindSafe;

pub(super) fn caught<T>(work: impl FnOnce() -> crate::Result<T>) -> crate::Result<T> {
    ay_core::catch_ay_panics(AssertUnwindSafe(work), |reason| {
        Err(crate::EncodeError::SolverPanicked(reason))
    })
}

// Private injection seam: only Native is used by the public constructor.
pub(super) trait Runner {
    type Evidence;

    fn kind(&self, _: &Self::Evidence) -> EvidenceKind {
        EvidenceKind::Safe
    }

    fn solve(
        &mut self,
        problem: &QuantifiedChcProblem,
        budget: Duration,
        memory: Option<usize>,
        token: &CancellationToken,
    ) -> crate::Result<Option<Self::Evidence>>;

    fn source<'a>(&self, evidence: &'a Self::Evidence) -> &'a str;

    fn recheck(
        &mut self,
        evidence: &Self::Evidence,
        problem: &QuantifiedChcProblem,
        budget: Duration,
        token: &CancellationToken,
    ) -> crate::Result<bool>;
}

pub(super) struct Native;

#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum EvidenceKind {
    Safe,
    Unsafe,
}

#[expect(
    clippy::large_enum_variant,
    reason = "source-bound evidence stays by value through scheduling and replay without a fresh unmetered post-verdict allocation"
)]
pub(super) enum NativeEvidence {
    Safe(QuantifiedChcSafety),
    Unsafe(QuantifiedChcCounterexample),
}

impl Runner for Native {
    type Evidence = NativeEvidence;

    fn kind(&self, evidence: &Self::Evidence) -> EvidenceKind {
        match evidence {
            NativeEvidence::Safe(_) => EvidenceKind::Safe,
            NativeEvidence::Unsafe(_) => EvidenceKind::Unsafe,
        }
    }

    fn solve(
        &mut self,
        problem: &QuantifiedChcProblem,
        budget: Duration,
        memory: Option<usize>,
        token: &CancellationToken,
    ) -> crate::Result<Option<Self::Evidence>> {
        caught(|| {
            Ok(match problem.solve(budget, memory, token) {
                QuantifiedChcResult::Safe(evidence) => Some(NativeEvidence::Safe(evidence)),
                QuantifiedChcResult::Unsafe(evidence) => Some(NativeEvidence::Unsafe(evidence)),
                QuantifiedChcResult::Unknown => None,
            })
        })
    }

    fn source<'a>(&self, evidence: &'a Self::Evidence) -> &'a str {
        match evidence {
            NativeEvidence::Safe(evidence) => evidence.source_smtlib(),
            NativeEvidence::Unsafe(evidence) => evidence.source_smtlib(),
        }
    }

    fn recheck(
        &mut self,
        evidence: &Self::Evidence,
        problem: &QuantifiedChcProblem,
        budget: Duration,
        token: &CancellationToken,
    ) -> crate::Result<bool> {
        caught(|| {
            Ok(match evidence {
                NativeEvidence::Safe(evidence) => evidence.recheck(problem, budget, token),
                NativeEvidence::Unsafe(evidence) => evidence.recheck(problem, budget, token),
            })
        })
    }
}
