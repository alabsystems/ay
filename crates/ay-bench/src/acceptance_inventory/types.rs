// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::path::PathBuf;

use serde::{Deserialize, Serialize};

/// Status polarity is part of the pinned input contract, never a corpus guess.
#[derive(Debug, Clone, Copy, Deserialize, Serialize, PartialEq, Eq)]
#[serde(rename_all = "kebab-case")]
pub enum InputDialect {
    Smt2,
    HornQuery,
    ChcComp,
}

impl InputDialect {
    /// Map source semantics to the CLI's exact result for this dialect.
    #[must_use]
    pub const fn cli_status(self, expected: SemanticExpectation) -> Option<CliStatus> {
        match (self, expected) {
            (Self::Smt2, SemanticExpectation::Sat) => Some(CliStatus::Sat),
            (Self::Smt2, SemanticExpectation::Unsat) => Some(CliStatus::Unsat),
            (Self::HornQuery, SemanticExpectation::Safe)
            | (Self::ChcComp, SemanticExpectation::Unsafe) => Some(CliStatus::Unsat),
            (Self::HornQuery, SemanticExpectation::Unsafe)
            | (Self::ChcComp, SemanticExpectation::Safe) => Some(CliStatus::Sat),
            _ => None,
        }
    }

    /// Which CHC semantic verdict the validation telemetry must authenticate.
    #[must_use]
    pub const fn chc_semantics(self, status: CliStatus) -> Option<SemanticExpectation> {
        match (self, status) {
            (Self::HornQuery, CliStatus::Unsat) | (Self::ChcComp, CliStatus::Sat) => {
                Some(SemanticExpectation::Safe)
            }
            (Self::HornQuery, CliStatus::Sat) | (Self::ChcComp, CliStatus::Unsat) => {
                Some(SemanticExpectation::Unsafe)
            }
            (Self::Smt2, _) => None,
        }
    }
}

#[derive(Debug, Clone, Copy, Deserialize, Serialize, PartialEq, Eq)]
#[serde(rename_all = "kebab-case")]
pub enum SemanticExpectation {
    Sat,
    Unsat,
    Safe,
    Unsafe,
}

impl SemanticExpectation {
    /// Unbound consumer oracles deliberately have no score-bearing expectation.
    #[must_use]
    pub fn from_inventory(value: &str) -> Option<Self> {
        match value {
            "sat" | "Sat" => Some(Self::Sat),
            "unsat" | "Unsat" => Some(Self::Unsat),
            "Safe" => Some(Self::Safe),
            "Unsafe" => Some(Self::Unsafe),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, Copy, Deserialize, Serialize, PartialEq, Eq)]
#[serde(rename_all = "lowercase")]
pub enum CliStatus {
    Sat,
    Unsat,
}

impl CliStatus {
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Sat => "sat",
            Self::Unsat => "unsat",
        }
    }
}

/// Diagnostic publication requires checked evidence for the original query.
#[derive(Debug, Clone, Copy, Deserialize, Serialize, PartialEq, Eq)]
#[serde(rename_all = "kebab-case")]
pub enum ProofPolicy {
    StrictOriginalQuery,
}

/// One selected whole-HORN diagnostic. This contract cannot close an ask.
#[derive(Debug, Clone, Deserialize, Serialize, PartialEq, Eq)]
pub struct ChcDiagnosticCase {
    pub input_id: String,
    pub request_ids: Vec<String>,
    pub path: PathBuf,
    pub expected_sha256: String,
    pub expected_size_bytes: u64,
    pub original_repository: String,
    pub original_revision: String,
    pub original_path: String,
    pub dialect: InputDialect,
    pub semantic_expectation: SemanticExpectation,
    pub expected_cli_status: CliStatus,
    pub proof_policy: ProofPolicy,
    pub timeout_ms: u64,
    pub solver_memory_mib: usize,
    pub tree_memory_mib: usize,
    pub promotable_for_ask_closure: bool,
}
