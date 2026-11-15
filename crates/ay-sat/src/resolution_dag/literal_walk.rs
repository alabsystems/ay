// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Cancellation-only walks over already-budgeted original literals.

use super::{Instant, Literal, ProofControl, ResolutionProofError, ResolutionProofPhase};

// Fixed internal polling granularity, not a resource allowance. Capacity and
// literal counts remain charged by the caller before these walks begin.
const CHUNK_LITERALS: usize = 256;

pub(super) fn append(
    target: &mut Vec<Literal>,
    source: &[Literal],
    deadline: Option<Instant>,
    phase: ResolutionProofPhase,
    control: &ProofControl<'_>,
) -> Result<(), ResolutionProofError> {
    for chunk in source.chunks(CHUNK_LITERALS) {
        control.check(deadline, phase)?;
        target.extend_from_slice(chunk);
    }
    control.check(deadline, phase)
}

pub(super) fn compare(
    actual: &[Literal],
    expected: &[Literal],
    clause_index: usize,
    deadline: Option<Instant>,
    control: &ProofControl<'_>,
) -> Result<(), ResolutionProofError> {
    if actual.len() != expected.len() {
        return Err(ResolutionProofError::OriginalClauseMismatch {
            index: clause_index,
        });
    }
    for (actual, expected) in actual
        .chunks(CHUNK_LITERALS)
        .zip(expected.chunks(CHUNK_LITERALS))
    {
        control.check(deadline, ResolutionProofPhase::Parse)?;
        if actual != expected {
            return Err(ResolutionProofError::OriginalClauseMismatch {
                index: clause_index,
            });
        }
    }
    control.check(deadline, ResolutionProofPhase::Parse)
}
