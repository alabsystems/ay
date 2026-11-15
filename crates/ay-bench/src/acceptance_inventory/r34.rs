// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact R34 replay adapter. This extends the acceptance inventory, not a
//! second solver or a pass checker. Records are never whole-request acceptance.
//! The caller supplies the ORIGINAL live resource guard and cancellation;
//! parsing, preparation, solve, original-model validation, strict replay and
//! retirement share its minima. No worker, retry, duration or work grant is
//! created by the adapter. Original per-row caps only tighten that owner.

mod archive;
mod capture;
mod identity;
mod rows;
#[cfg(test)]
mod tests;
mod witness;

use std::collections::BTreeMap;
use std::path::Path;

use ay_chc::engines::ExternalInvariantValidation;
use serde::Serialize;

use super::Inventory;
use crate::{BenchError, Result};

/// The four captured first-pass problems requested by the W5/W6 refresh.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub enum R34Row {
    StaticErrorP0,
    StaticErrorDefinition7,
    StaticErrorP22,
    AllocErrorP28,
}

impl R34Row {
    pub const ALL: [Self; 4] = [
        Self::StaticErrorP0,
        Self::StaticErrorDefinition7,
        Self::StaticErrorP22,
        Self::AllocErrorP28,
    ];

    fn index(self) -> usize {
        match self {
            Self::StaticErrorP0 => 0,
            Self::StaticErrorDefinition7 => 1,
            Self::StaticErrorP22 => 2,
            Self::AllocErrorP28 => 3,
        }
    }
}

/// Invocation identity is retained even when two inputs have identical bytes.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub enum R34Witness {
    Static0001,
    Static0003,
    Bitmask0026,
}

impl R34Witness {
    pub const ALL: [Self; 3] = [Self::Static0001, Self::Static0003, Self::Bitmask0026];

    fn index(self) -> usize {
        match self {
            Self::Static0001 => 0,
            Self::Static0003 => 1,
            Self::Bitmask0026 => 2,
        }
    }
}

/// Authenticated archived members, held privately after their container hash
/// and each selected member's independent identity have been checked.
pub struct R34Archive {
    capture: capture::Capture,
    files: BTreeMap<String, Vec<u8>>,
    inventory_sha256: String,
}

impl R34Archive {
    /// Authenticate the existing inventory and the original .tar.gz. Does not
    /// extract to disk, spawn a process, parse a formula or run a solver.
    pub fn load(inventory: &Path, archive: &Path) -> Result<Self> {
        archive::load(inventory, archive)
    }

    fn text(&self, name: &str) -> Result<&str> {
        let bytes = self.files.get(name).ok_or_else(|| {
            BenchError::msg(format!("R34 authenticated member is missing: {name}"))
        })?;
        std::str::from_utf8(bytes).map_err(|error| BenchError::msg(error.to_string()))
    }

    /// Original dispositions are not inferred from SMT polarity or Unknown.
    #[must_use]
    pub fn original_dispositions(&self) -> &BTreeMap<String, String> {
        &self.capture.dispositions
    }
}

/// Diagnostic observation, not a reusable certificate or acceptance receipt.
#[derive(Debug, Serialize)]
pub struct R34RowRecord {
    pub case: R34Row,
    pub inventory_sha256: String,
    pub archive_sha256: String,
    pub source_sha256: String,
    pub content_sha256: String,
    pub prepared_sha256: String,
    pub original_timeout_ns: u64,
    pub original_config_sha256: String,
    pub captured_environment: serde_json::Value,
    pub elapsed_ns: u128,
    pub current_binding: Option<R34PreparedIdentity>,
    pub status: R34RowStatus,
    /// Always false: an in-process row cannot authenticate a compiler tuple,
    /// process-tree RSS envelope, full batch, or Rust-level bug attribution.
    pub promotable_for_ask_closure: bool,
}

#[derive(Debug, Serialize)]
pub enum R34RowStatus {
    BindingRefused {
        reason: String,
    },
    BoundOnly,
    ExecutionError {
        reason: String,
    },
    ResourceRefused {
        observed: String,
    },
    OriginalModelRejected {
        observed: String,
    },
    Observed {
        result: String,
        original_model_validation: Option<String>,
        checked_original_replay: bool,
        metadata: serde_json::Value,
    },
}

fn refused(kind: ExternalInvariantValidation) -> R34RowStatus {
    // Preserve the typed API's exact variant, including newer non-exhaustive
    // causes such as WorkLimit. No clock-based inference or catch-all verdict.
    R34RowStatus::ResourceRefused {
        observed: format!("{kind:?}"),
    }
}

fn chc_error(error: BenchError) -> ay_chc::ChcError {
    ay_chc::ChcError::Verification(error.to_string())
}

pub use rows::R34PreparedIdentity;
pub use witness::{R34WitnessBinding, R34WitnessBlocker};
