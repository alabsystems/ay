// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Resource limits for optional ITE arithmetic-model repair.

use ay_core::TermId;
use num_bigint::BigInt;
use num_rational::BigRational;
use std::mem::size_of;

/// The repair is optional model completion, so fail closed instead of letting
/// a very large/shared assertion DAG amplify work before mandatory validation.
const ITE_FIXUP_WORK_LIMIT: usize = 100_000;
/// Aggregate exact-value work/retention admitted by one optional repair.
const ITE_FIXUP_PATCH_PAYLOAD_LIMIT: usize = 8 * 1024 * 1024;
/// Independent cardinality cap for zero/small-value patch candidates.
const ITE_FIXUP_PATCH_CANDIDATE_LIMIT: usize = 4_096;

#[derive(Clone, Copy)]
pub(in crate::executor::model) struct IteFixupLimits {
    pub(in crate::executor::model) work: usize,
    pub(in crate::executor::model) patch_payload_bytes: usize,
    pub(in crate::executor::model) patch_candidates: usize,
}

pub(in crate::executor::model) const ITE_FIXUP_LIMITS: IteFixupLimits = IteFixupLimits {
    work: ITE_FIXUP_WORK_LIMIT,
    patch_payload_bytes: ITE_FIXUP_PATCH_PAYLOAD_LIMIT,
    patch_candidates: ITE_FIXUP_PATCH_CANDIDATE_LIMIT,
};

fn bigint_payload_bytes(value: &BigInt) -> Option<usize> {
    let bytes = usize::try_from(value.bits().checked_add(7)? / 8).ok()?;
    let word = size_of::<usize>();
    bytes
        .checked_add(word.checked_sub(1)?)?
        .checked_div(word)?
        .checked_mul(word)
}

fn rational_payload_bytes(value: &BigRational) -> Option<usize> {
    bigint_payload_bytes(value.numer())?.checked_add(bigint_payload_bytes(value.denom())?)
}

pub(in crate::executor::model) fn patch_candidate_bytes(value: &BigRational) -> Option<usize> {
    // The inline key/value, conservative hash-table/allocator metadata, and
    // both heap-backed integer payloads. Later commit clones are only a fixed
    // multiple of this globally bounded retained set.
    size_of::<(TermId, BigRational)>()
        .checked_add(4usize.checked_mul(size_of::<usize>())?)?
        .checked_add(rational_payload_bytes(value)?)
}

#[cfg(test)]
pub(in crate::executor::model) fn patch_candidate_bytes_for_test(value: &BigRational) -> usize {
    patch_candidate_bytes(value).expect("test rational payload must fit usize")
}
