// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::Literal;
use std::mem::size_of;

type ProofLit = ay_proof_common::literal::Literal;

// Compile-time guard: both Literal types must remain layout-compatible.
// The `to_proof_lits` conversion relies on identical u32 encoding.
const _: () = assert!(
    size_of::<Literal>() == size_of::<ProofLit>(),
    "ay_sat::Literal and ay_proof_common::Literal must have identical size"
);

/// Convert `&[ay_sat::Literal]` to `Vec<ay_proof_common::Literal>`.
///
/// Both types are `#[repr(transparent)]` over `u32` with identical encoding
/// (`positive = 2*var, negative = 2*var + 1`). This allocates a Vec per call,
/// which is acceptable because `ForwardChecker` is `#[cfg(debug_assertions)]` only.
/// Previous zero-cost unsafe cast (#5626) replaced to enable `#![forbid(unsafe_code)]` (#5838).
#[inline]
pub(super) fn to_proof_lits(clause: &[Literal]) -> Vec<ProofLit> {
    clause
        .iter()
        .map(|lit| ProofLit::from_index(lit.0 as usize))
        .collect()
}
