// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::collections::BTreeSet;
use std::path::{Component, Path};

use super::{
    DatasetReference, DatasetSource, InventoryDocument, INVENTORY_SCHEMA, INVENTORY_SCHEMA_V2,
    INVENTORY_SCHEMA_V3, INVENTORY_SCHEMA_V4, INVENTORY_SCHEMA_V5, INVENTORY_SCHEMA_V6,
    INVENTORY_SCHEMA_V7, INVENTORY_SCHEMA_V8,
};
use crate::{BenchError, Result};

pub(super) const MAX_TIMEOUT_MS: u64 = 7 * 24 * 60 * 60 * 1000;

pub(super) fn validate(document: &InventoryDocument) -> Result<()> {
    let additions: &[&str] = match document.schema.as_str() {
        INVENTORY_SCHEMA => &[],
        INVENTORY_SCHEMA_V2 => &["R22a", "R22b", "R22c", "R22d"],
        INVENTORY_SCHEMA_V3 => &["R22a", "R22b", "R22c", "R22d", "R23"],
        INVENTORY_SCHEMA_V4 => &["R22a", "R22b", "R22c", "R22d", "R23", "R24"],
        INVENTORY_SCHEMA_V5 => &[
            "R22a", "R22b", "R22c", "R22d", "R23", "R24", "R25", "R26", "R27", "R28", "R29",
        ],
        INVENTORY_SCHEMA_V6 => &[
            "R22a", "R22b", "R22c", "R22d", "R23", "R24", "R25", "R26", "R27", "R28", "R29", "R30",
            "R31", "R32", "R33", "R34",
        ],
        INVENTORY_SCHEMA_V7 => &[
            "R22a", "R22b", "R22c", "R22d", "R23", "R24", "R25", "R26", "R27", "R28", "R29", "R30",
            "R31", "R32", "R33", "R34", "R35",
        ],
        INVENTORY_SCHEMA_V8 => &[
            "R22a", "R22b", "R22c", "R22d", "R23", "R24", "R25", "R26", "R27", "R28", "R29", "R30",
            "R31", "R32", "R33", "R34", "R35", "R36",
        ],
        _ => {
            return Err(BenchError::msg(
                "unsupported MODEL_CHECKER_CONSUMER acceptance inventory schema",
            ));
        }
    };
    let requests = unique_ids(document.request_inventory.iter().map(|row| row.id.as_str()))?;
    let required: BTreeSet<String> = (1..=21)
        .map(|number| format!("R{number:02}"))
        .chain((1..=7).map(|number| format!("U{number}")))
        .chain(additions.iter().map(|id| (*id).to_owned()))
        .collect();
    if requests
        .iter()
        .copied()
        .ne(required.iter().map(String::as_str))
    {
        return Err(BenchError::msg(format!(
            "inventory schema requires exactly R01-R21 and U1-U7 plus {additions:?}",
        )));
    }
    let inputs = unique_ids(document.stored_inputs.iter().map(|row| row.id.as_str()))?;
    let routes = unique_ids(document.routes.iter().map(|row| row.id.as_str()))?;
    let policies = unique_ids(document.resource_policies.iter().map(|row| row.id.as_str()))?;
    let datasets = unique_ids(document.datasets.iter().map(|row| row.id.as_str()))?;
    unique_ids(document.consumer_units.iter().map(|row| row.id.as_str()))?;
    unique_ids(
        document
            .integration_controls
            .iter()
            .map(|row| row.id.as_str()),
    )?;
    unique_ids(document.blockers.iter().map(|row| row.id.as_str()))?;
    validate_defaults(document, &policies)?;
    for request in &document.request_inventory {
        nonempty(&request.title, "request title")?;
        if request.source_requests.is_empty() || request.required_checks.is_empty() {
            return Err(BenchError::msg(format!(
                "{} lacks source/check obligations",
                request.id
            )));
        }
        for path in &request.source_requests {
            relative_path(path)?;
        }
        references(&request.required_routes, &routes, "request route", true)?;
        references(&request.stored_input_ids, &inputs, "request input", false)?;
        let selected = request.resource_policy_ids(&document.case_defaults);
        references_iter(selected.iter().copied(), &policies, "resource policy", true)?;
        references_iter(request.dataset_ids(), &datasets, "request dataset", false)?;
        if let Some(timeout) = request.harness_or_solve_budget_ms {
            timeout_ms(timeout)?;
        }
        for id in &request.stored_input_ids {
            let linked = document
                .stored_inputs
                .iter()
                .any(|input| input.id == *id && input.request_ids.contains(&request.id));
            if !linked {
                return Err(BenchError::msg(format!(
                    "{} input {id} has no reverse binding",
                    request.id
                )));
            }
        }
    }
    validate_sources(document, &requests)?;
    validate_performance(document, &requests, &inputs, &routes)
}

fn validate_defaults(document: &InventoryDocument, policies: &BTreeSet<&str>) -> Result<()> {
    let defaults = &document.case_defaults;
    if !defaults.tracked_solver_input_bytes_must_be_preserved {
        return Err(BenchError::msg(
            "inventory cannot disable exact input-byte preservation",
        ));
    }
    if !policies.contains(defaults.resource_policy.as_str()) {
        return Err(BenchError::msg(
            "inventory default resource policy is undefined",
        ));
    }
    revision(&defaults.stored_model_checker_consumer_input_revision)?;
    revision(
        &document
            .source_authority_defaults
            .consumer_units_repository_revision,
    )?;
    revision(
        &document
            .source_authority_defaults
            .request_and_dataset_revision,
    )?;
    nonempty(&defaults.request_status, "default request status")?;
    nonempty(
        &defaults.prepared_consumer_exports,
        "prepared-export default",
    )?;
    Ok(())
}

fn validate_sources(document: &InventoryDocument, requests: &BTreeSet<&str>) -> Result<()> {
    for input in &document.stored_inputs {
        super::input::validate(input)?;
        relative_path(&input.path)?;
        nonempty(&input.repository, "input repository")?;
        references(&input.request_ids, requests, "input request", true)?;
        if let Some(value) = &input.revision {
            revision(value)?;
        }
        if let Some(value) = &input.sha256 {
            sha256(value)?;
        }
        if input.size_bytes == Some(0) {
            return Err(BenchError::msg(format!(
                "{} declares an empty solver/source input",
                input.id
            )));
        }
        for id in &input.request_ids {
            if !document
                .request_inventory
                .iter()
                .any(|request| request.id == *id && request.stored_input_ids.contains(&input.id))
            {
                return Err(BenchError::msg(format!(
                    "{} request {id} has no reverse binding",
                    input.id
                )));
            }
        }
    }
    for consumer in &document.consumer_units {
        references(&consumer.request_ids, requests, "consumer request", true)?;
        if let Some(value) = &consumer.revision {
            revision(value)?;
        }
    }
    for dataset in &document.datasets {
        validate_dataset(dataset)?;
        if let Some(value) = &dataset.revision {
            revision(value)?;
        }
    }
    for blocker in &document.blockers {
        references(&blocker.request_ids, requests, "blocker request", true)?;
        nonempty(&blocker.reason, "blocker reason")?;
    }
    Ok(())
}

fn validate_dataset(dataset: &DatasetReference) -> Result<()> {
    nonempty(&dataset.repository, "dataset repository")?;
    let validate_path = |path: &str| {
        if dataset.repository == "external-measurement" {
            external_reference_path(path)
        } else {
            relative_path(path)
        }
    };
    match &dataset.source {
        DatasetSource::File {
            path,
            sha256: digest,
        } => {
            validate_path(path)?;
            sha256(digest)?;
        }
        DatasetSource::SourceRows { rows } => {
            if rows.is_empty() {
                return Err(BenchError::msg("dataset source cohort cannot be empty"));
            }
            for row in rows {
                validate_path(&row.path)?;
                sha256(&row.sha256)?;
                if row.size_bytes == 0 {
                    return Err(BenchError::msg(
                        "dataset source row must have a nonempty byte identity",
                    ));
                }
            }
        }
    }
    Ok(())
}

fn external_reference_path(value: &str) -> Result<()> {
    let path = Path::new(value);
    if !path.is_absolute()
        || !path
            .components()
            .all(|part| matches!(part, Component::RootDir | Component::Normal(_)))
    {
        return Err(BenchError::msg(
            "external historical dataset must have a normalized absolute reference path",
        ));
    }
    // This is historical provenance, not local execution admission. Do not
    // stat/open it or reinterpret it as a repository-root solver input.
    Ok(())
}

fn validate_performance(
    document: &InventoryDocument,
    requests: &BTreeSet<&str>,
    inputs: &BTreeSet<&str>,
    routes: &BTreeSet<&str>,
) -> Result<()> {
    let contract = &document.performance_contracts;
    if contract.measurement.minimum_alternating_pairs < 3 {
        return Err(BenchError::msg(
            "performance contract requires at least three alternating pairs",
        ));
    }
    unique_ids(contract.targets.iter().map(|target| target.id.as_str()))?;
    for request in ["R13", "R16"] {
        if !contract
            .targets
            .iter()
            .any(|target| target.request_ids.iter().any(|id| id == request))
        {
            return Err(BenchError::msg(format!(
                "inventory lacks its frozen {request} performance contract"
            )));
        }
    }
    for target in &contract.targets {
        references(&target.request_ids, requests, "performance request", true)?;
        references(&target.stored_input_ids, inputs, "performance input", true)?;
        references(&target.required_routes, routes, "performance route", true)?;
        timeout_ms(target.every_candidate_run_deadline_ms)?;
        if target.median_limit.is_empty() {
            return Err(BenchError::msg(format!(
                "{} lacks its frozen median limit",
                target.id
            )));
        }
    }
    Ok(())
}

fn unique_ids<'a>(ids: impl IntoIterator<Item = &'a str>) -> Result<BTreeSet<&'a str>> {
    let mut seen = BTreeSet::new();
    for id in ids {
        nonempty(id, "contract ID")?;
        if !seen.insert(id) {
            return Err(BenchError::msg(format!(
                "duplicate inventory contract ID: {id}"
            )));
        }
    }
    Ok(seen)
}

fn references(
    selected: &[String],
    known: &BTreeSet<&str>,
    label: &str,
    required: bool,
) -> Result<()> {
    references_iter(selected.iter().map(String::as_str), known, label, required)
}

fn references_iter<'a>(
    selected: impl IntoIterator<Item = &'a str>,
    known: &BTreeSet<&str>,
    label: &str,
    required: bool,
) -> Result<()> {
    let selected = unique_ids(selected)?;
    if required && selected.is_empty() {
        return Err(BenchError::msg(format!("missing {label} references")));
    }
    for id in selected {
        if !known.contains(id) {
            return Err(BenchError::msg(format!("undefined {label}: {id}")));
        }
    }
    Ok(())
}

fn nonempty(value: &str, label: &str) -> Result<()> {
    if value.trim().is_empty() {
        return Err(BenchError::msg(format!("empty {label}")));
    }
    Ok(())
}

pub(super) fn timeout_ms(value: u64) -> Result<()> {
    if value == 0 || value > MAX_TIMEOUT_MS {
        return Err(BenchError::msg(
            "inventory timeout is outside the benchmark envelope",
        ));
    }
    Ok(())
}

pub(super) fn relative_path(value: &str) -> Result<()> {
    if value.is_empty()
        || !Path::new(value)
            .components()
            .all(|part| matches!(part, Component::Normal(_)))
    {
        return Err(BenchError::msg(format!(
            "inventory path must be a normalized relative path: {value}"
        )));
    }
    Ok(())
}

pub(super) fn revision(value: &str) -> Result<()> {
    if value.len() != 40 || !lower_hex(value) {
        return Err(BenchError::msg(
            "inventory revision must be a full lowercase git SHA",
        ));
    }
    Ok(())
}

pub(super) fn sha256(value: &str) -> Result<()> {
    if value.len() != 64 || !lower_hex(value) {
        return Err(BenchError::msg(
            "inventory input digest must be a full lowercase SHA256",
        ));
    }
    Ok(())
}

fn lower_hex(value: &str) -> bool {
    value
        .bytes()
        .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
}
