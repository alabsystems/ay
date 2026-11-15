// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Source-bound planning for MODEL_CHECKER_CONSUMER's AY requests.
//!
//! Loading an inventory is not execution evidence. The complete request plan
//! stays unqualified, including routes for which a whole-HORN diagnostic can
//! be selected. Diagnostics never replace prepared consumer property inputs.

mod diagnostic;
mod document;
mod identity;
mod input;
mod json;
mod planning;
pub mod r34;
mod smt_cli;
mod types;
mod validation;

#[cfg(test)]
mod tests;

#[cfg(test)]
pub(crate) use tests::document as test_document;

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use sha2::{Digest as _, Sha256};

use crate::Result;

pub use document::{
    CaseDefaults, ConsumerUnit, DatasetReference, DatasetSource, DatasetSourceRow,
    InventoryBlocker, InventoryDocument, MeasurementContract, NamedContract, PerformanceContracts,
    PerformanceTarget, RequestContract, ResourcePolicySelection, SourceAuthorityDefaults,
    StoredInput,
};
pub use smt_cli::{
    run_smt_cli, DefaultObservation, SmtCliArgs, SmtCliBlocker, SmtCliCase, SmtCliRecord,
    SmtCliReport, SmtCliTerminal, SmtMemoryVariant,
};

pub use planning::{AcceptancePlan, BlockerKind, PlanBlocker, PlannedRequest, RouteObligation};
pub use types::{ChcDiagnosticCase, CliStatus, InputDialect, ProofPolicy, SemanticExpectation};

/// Historical exact 28-request inventory contract.
pub const INVENTORY_SCHEMA: &str = "ay.model-checker-consumer-acceptance-inventory/v1";
/// Exact 32 acceptance contracts across 29 request groups; original 28 IDs retain their meaning.
pub const INVENTORY_SCHEMA_V2: &str = "ay.model-checker-consumer-acceptance-inventory/v2";
/// Exact 33 acceptance contracts across 30 groups, adding the ordinary typed range-write ask.
pub const INVENTORY_SCHEMA_V3: &str = "ay.model-checker-consumer-acceptance-inventory/v3";
/// Exact 34 contracts, including the whole-BMC-proof-budget request.
pub const INVENTORY_SCHEMA_V4: &str = "ay.model-checker-consumer-acceptance-inventory/v4";
/// Exact 39 contracts, adding current effort, datatype and per-row requests.
pub const INVENTORY_SCHEMA_V5: &str = "ay.model-checker-consumer-acceptance-inventory/v5";
/// Exact 44 contracts, retaining original array, replay, drain and export asks.
pub const INVENTORY_SCHEMA_V6: &str = "ay.model-checker-consumer-acceptance-inventory/v6";
/// Exact 45 contracts, adding default-posture proof runaways and strict controls.
pub const INVENTORY_SCHEMA_V7: &str = "ay.model-checker-consumer-acceptance-inventory/v7";
/// Exact 46 contracts, adding the original ALL mixed BV/FP counterexample.
pub const INVENTORY_SCHEMA_V8: &str = "ay.model-checker-consumer-acceptance-inventory/v8";
/// Smaller than the general benchmark metadata bound; inventory is not a corpus.
const MAX_INVENTORY_BYTES: u64 = 1024 * 1024;

/// Validated inventory, retaining its exact serialized-byte identity.
#[derive(Debug, Clone)]
pub struct Inventory {
    pub sha256: String,
    pub document: InventoryDocument,
}

impl Inventory {
    /// Read a bounded regular file without following a final-component symlink.
    ///
    /// No child processes are started and no solver evidence is produced.
    pub fn load(path: &Path) -> Result<Self> {
        let text = crate::resource::read_bounded_text(
            path,
            MAX_INVENTORY_BYTES,
            "MODEL_CHECKER_CONSUMER acceptance inventory",
        )?;
        Self::parse(&text)
    }

    fn parse(text: &str) -> Result<Self> {
        let value = json::read(text)?;
        identity::validate(&value)?;
        let document: InventoryDocument = serde_json::from_value(value)?;
        validation::validate(&document)?;
        Ok(Self {
            sha256: format!("sha256:{:x}", Sha256::digest(text.as_bytes())),
            document,
        })
    }

    /// Preserve every request and its unresolved route/evidence obligations.
    #[must_use]
    pub fn plan(&self) -> AcceptancePlan {
        planning::plan(self)
    }

    /// Resolve explicitly selected stored whole-HORN diagnostic inputs.
    ///
    /// The runner must authenticate these expected identities against its
    /// streamed private input snapshots before spawning any solver. Local
    /// pathname resolution alone does not establish a repository revision.
    pub fn chc_diagnostic_cases(
        &self,
        repository_roots: &BTreeMap<String, PathBuf>,
        stored_input_ids: &[String],
    ) -> Result<Vec<ChcDiagnosticCase>> {
        diagnostic::select(self, repository_roots, stored_input_ids)
    }
}
