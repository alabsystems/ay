// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Read-only disclosure of an authenticated native proof-support export.

/// One emitted proof assumption and its exact original assertion occurrence.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExternalProofAssumption {
    pub(crate) proof_step: u32,
    pub(crate) original_assertion_index: usize,
}

impl ExternalProofAssumption {
    /// Numeric id of the `Assume` step in the unchanged emitted proof.
    #[must_use]
    pub fn proof_step(&self) -> u32 {
        self.proof_step
    }

    /// Index in the full ordered original assertion vector, before projection.
    #[must_use]
    pub fn original_assertion_index(&self) -> usize {
        self.original_assertion_index
    }
}

/// Disclosure of the original query and the exact problem used by an external
/// proof checker.
///
/// The proof refutes an authenticated subset of the full native query. Every
/// emitted assumption is an exact original premise; none is invented or
/// retyped. Refuting that subset refutes the full conjunction. The full native
/// query remains the solver admission boundary.
///
/// These hashes describe evidence. This type has no public constructor or
/// deserializer, and its data cannot recreate the private live-source seal.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExternalProofSupport {
    pub(crate) full_typed_query_sha256: [u8; 32],
    pub(crate) declaration_context_sha256: [u8; 32],
    pub(crate) original_assertion_count: usize,
    pub(crate) assumptions: Vec<ExternalProofAssumption>,
    pub(crate) proof_sha256: [u8; 32],
    pub(crate) supported_problem_sha256: [u8; 32],
}

impl ExternalProofSupport {
    /// Schema of this disclosure and its domain-separated scope codec.
    #[must_use]
    pub fn schema(&self) -> &'static str {
        "ay-native-external-proof-support-v1"
    }

    /// Digest of the full ordered live typed query, including unused roots,
    /// duplicate occurrences, and their complete typed term closure.
    ///
    /// This is distinct from the diagnostic native-replay artifact digest.
    #[must_use]
    pub fn full_typed_query_sha256(&self) -> [u8; 32] {
        self.full_typed_query_sha256
    }

    /// Digest of the full original declaration context, before projection.
    #[must_use]
    pub fn declaration_context_sha256(&self) -> [u8; 32] {
        self.declaration_context_sha256
    }

    /// Original assertion occurrences, including duplicates.
    #[must_use]
    pub fn original_assertion_count(&self) -> usize {
        self.original_assertion_count
    }

    /// Exact source occurrence selected for every emitted `Assume` step.
    #[must_use]
    pub fn assumptions(&self) -> &[ExternalProofAssumption] {
        &self.assumptions
    }

    /// Digest of the exact emitted proof bytes.
    #[must_use]
    pub fn proof_sha256(&self) -> [u8; 32] {
        self.proof_sha256
    }

    /// Digest of the exact supported SMT-LIB problem carried by the artifact.
    #[must_use]
    pub fn supported_problem_sha256(&self) -> [u8; 32] {
        self.supported_problem_sha256
    }
}
