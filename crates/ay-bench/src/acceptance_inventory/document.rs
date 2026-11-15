// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};
use serde_json::Value;

/// Typed executable identity fields with lossless non-executable prose.
#[derive(Debug, Clone, Deserialize, Serialize, PartialEq, Eq)]
pub struct InventoryDocument {
    pub schema: String,
    pub captured_date: String,
    pub qualification: String,
    pub snapshots: BTreeMap<String, Value>,
    pub resource_policies: Vec<NamedContract>,
    pub routes: Vec<NamedContract>,
    pub request_inventory: Vec<RequestContract>,
    pub stored_inputs: Vec<StoredInput>,
    pub consumer_units: Vec<ConsumerUnit>,
    pub datasets: Vec<DatasetReference>,
    pub integration_controls: Vec<NamedContract>,
    pub blockers: Vec<InventoryBlocker>,
    pub case_defaults: CaseDefaults,
    pub source_authority_defaults: SourceAuthorityDefaults,
    pub performance_contracts: PerformanceContracts,
    pub unresolved_bindings: Vec<Value>,
    #[serde(flatten)]
    pub metadata: BTreeMap<String, Value>,
}

#[derive(Debug, Clone, Deserialize, Serialize, PartialEq, Eq)]
pub struct NamedContract {
    pub id: String,
    #[serde(flatten)]
    pub details: BTreeMap<String, Value>,
}

#[derive(Debug, Clone, Deserialize, Serialize, PartialEq, Eq)]
pub struct RequestContract {
    pub id: String,
    pub title: String,
    pub source_requests: Vec<String>,
    pub required_routes: Vec<String>,
    pub harness_or_solve_budget_ms: Option<u64>,
    pub required_checks: Vec<String>,
    pub stored_input_ids: Vec<String>,
    pub status: Option<String>,
    pub resource_policy: Option<ResourcePolicySelection>,
    pub sample_dataset: Option<String>,
    pub additional_family_dataset: Option<String>,
    pub additional_source_dataset: Option<String>,
    pub source_inventory_dataset: Option<String>,
    #[serde(flatten)]
    pub metadata: BTreeMap<String, Value>,
}

impl RequestContract {
    #[must_use]
    pub fn resolved_status<'a>(&'a self, defaults: &'a CaseDefaults) -> &'a str {
        self.status.as_deref().unwrap_or(&defaults.request_status)
    }

    #[must_use]
    pub fn resource_policy_ids<'a>(&'a self, defaults: &'a CaseDefaults) -> Vec<&'a str> {
        match &self.resource_policy {
            Some(ResourcePolicySelection::One(id)) => vec![id],
            Some(ResourcePolicySelection::Many(ids)) => ids.iter().map(String::as_str).collect(),
            None => vec![&defaults.resource_policy],
        }
    }

    #[must_use]
    pub fn dataset_ids(&self) -> Vec<&str> {
        [
            self.sample_dataset.as_deref(),
            self.additional_family_dataset.as_deref(),
            self.additional_source_dataset.as_deref(),
            self.source_inventory_dataset.as_deref(),
        ]
        .into_iter()
        .flatten()
        .collect()
    }
}

#[derive(Debug, Clone, Deserialize, Serialize, PartialEq, Eq)]
#[serde(untagged)]
pub enum ResourcePolicySelection {
    One(String),
    Many(Vec<String>),
}

#[derive(Debug, Clone, Deserialize, Serialize, PartialEq, Eq)]
pub struct StoredInput {
    pub id: String,
    pub repository: String,
    pub revision: Option<String>,
    pub path: String,
    pub sha256: Option<String>,
    pub size_bytes: Option<u64>,
    pub kind: Option<String>,
    pub smt_logic: Option<String>,
    pub request_ids: Vec<String>,
    pub expected_semantic_result: String,
    pub availability: String,
    #[serde(flatten)]
    pub metadata: BTreeMap<String, Value>,
}

#[derive(Debug, Clone, Deserialize, Serialize, PartialEq, Eq)]
pub struct ConsumerUnit {
    pub id: String,
    pub repository: String,
    pub revision: Option<String>,
    pub request_ids: Vec<String>,
    #[serde(flatten)]
    pub details: BTreeMap<String, Value>,
}

#[derive(Debug, Clone, Serialize, PartialEq, Eq)]
pub struct DatasetReference {
    pub id: String,
    pub repository: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub revision: Option<String>,
    #[serde(flatten)]
    pub source: DatasetSource,
    #[serde(flatten)]
    pub details: BTreeMap<String, Value>,
}

/// A dataset is either one exact source file or a cohort of individually bound
/// source rows. A cohort has no invented aggregate pathname or aggregate hash.
#[derive(Debug, Clone, Serialize, PartialEq, Eq)]
#[serde(untagged)]
pub enum DatasetSource {
    File { path: String, sha256: String },
    SourceRows { rows: Vec<DatasetSourceRow> },
}

#[derive(Debug, Clone, Deserialize, Serialize, PartialEq, Eq)]
pub struct DatasetSourceRow {
    pub path: String,
    pub sha256: String,
    pub size_bytes: u64,
    #[serde(flatten)]
    pub details: BTreeMap<String, Value>,
}

impl<'de> Deserialize<'de> for DatasetReference {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        use serde::de::Error as _;

        // Deserialize common metadata first so an untagged flatten cannot
        // swallow source fields or silently accept both mutually exclusive
        // representations. Unknown historical metadata remains lossless.
        #[derive(Deserialize)]
        struct Metadata {
            id: String,
            repository: String,
            revision: Option<String>,
            #[serde(flatten)]
            details: BTreeMap<String, Value>,
        }
        let mut metadata = Metadata::deserialize(deserializer)?;
        let source =
            match (
                metadata.details.remove("path"),
                metadata.details.remove("sha256"),
                metadata.details.remove("rows"),
            ) {
                (Some(path), Some(sha256), None) => DatasetSource::File {
                    path: serde_json::from_value(path).map_err(D::Error::custom)?,
                    sha256: serde_json::from_value(sha256).map_err(D::Error::custom)?,
                },
                (None, None, Some(rows)) => DatasetSource::SourceRows {
                    rows: serde_json::from_value(rows).map_err(D::Error::custom)?,
                },
                _ => return Err(D::Error::custom(
                    "dataset requires exactly a path/hash pair or individually bound source rows",
                )),
            };
        Ok(Self {
            id: metadata.id,
            repository: metadata.repository,
            revision: metadata.revision,
            source,
            details: metadata.details,
        })
    }
}

#[derive(Debug, Clone, Deserialize, Serialize, PartialEq, Eq)]
pub struct InventoryBlocker {
    pub id: String,
    pub request_ids: Vec<String>,
    pub reason: String,
    #[serde(flatten)]
    pub details: BTreeMap<String, Value>,
}

#[derive(Debug, Clone, Deserialize, Serialize, PartialEq, Eq)]
pub struct CaseDefaults {
    pub resource_policy: String,
    pub request_status: String,
    pub consumer_selection: String,
    pub stored_model_checker_consumer_input_revision: String,
    pub whole_horn_export_equivalence: String,
    pub tracked_solver_input_bytes_must_be_preserved: bool,
    pub prepared_consumer_exports: String,
    #[serde(flatten)]
    pub metadata: BTreeMap<String, Value>,
}

#[derive(Debug, Clone, Deserialize, Serialize, PartialEq, Eq)]
pub struct SourceAuthorityDefaults {
    pub consumer_units_repository_revision: String,
    pub request_and_dataset_repository: String,
    pub request_and_dataset_revision: String,
    #[serde(flatten)]
    pub details: BTreeMap<String, Value>,
}

#[derive(Debug, Clone, Deserialize, Serialize, PartialEq, Eq)]
pub struct PerformanceContracts {
    pub authority: String,
    pub measurement: MeasurementContract,
    pub targets: Vec<PerformanceTarget>,
    #[serde(flatten)]
    pub details: BTreeMap<String, Value>,
}

#[derive(Debug, Clone, Deserialize, Serialize, PartialEq, Eq)]
pub struct MeasurementContract {
    pub minimum_alternating_pairs: u32,
    pub pair_order: String,
    pub match_fields: Vec<String>,
    pub record_fields: Vec<String>,
    pub timeout_treatment: String,
    pub missing_reference_treatment: String,
    pub historical_binary_authority: String,
    #[serde(flatten)]
    pub details: BTreeMap<String, Value>,
}

#[derive(Debug, Clone, Deserialize, Serialize, PartialEq, Eq)]
pub struct PerformanceTarget {
    pub id: String,
    pub request_ids: Vec<String>,
    pub stored_input_ids: Vec<String>,
    pub required_routes: Vec<String>,
    pub candidate_policy: String,
    pub comparison_policy: String,
    pub median_limit: BTreeMap<String, Value>,
    pub every_candidate_run_deadline_ms: u64,
    #[serde(flatten)]
    pub details: BTreeMap<String, Value>,
}
