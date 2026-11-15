// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};

use super::{
    ChcDiagnosticCase, InputDialect, Inventory, ProofPolicy, SemanticExpectation, StoredInput,
};
use crate::{BenchError, Result, WithContext as _};

const DIAGNOSTIC_MEMORY_MIB: usize = 4096;

pub(super) fn select(
    inventory: &Inventory,
    roots: &BTreeMap<String, PathBuf>,
    selected: &[String],
) -> Result<Vec<ChcDiagnosticCase>> {
    if selected.is_empty() {
        return Err(BenchError::msg(
            "CHC diagnostics require explicit stored input IDs",
        ));
    }
    let mut seen_ids = BTreeSet::new();
    let mut seen_paths = BTreeSet::new();
    let mut cases = Vec::new();
    for id in selected {
        if !seen_ids.insert(id) {
            return Err(BenchError::msg(format!(
                "duplicate selected stored input: {id}"
            )));
        }
        let input = inventory
            .document
            .stored_inputs
            .iter()
            .find(|input| input.id == *id)
            .ok_or_else(|| BenchError::msg(format!("undefined selected stored input: {id}")))?;
        let case = resolve_case(inventory, roots, input)?;
        if !seen_paths.insert(case.path.clone()) {
            return Err(BenchError::msg(
                "selected diagnostic IDs resolve to the same input path",
            ));
        }
        cases.push(case);
    }
    Ok(cases)
}

fn resolve_case(
    inventory: &Inventory,
    roots: &BTreeMap<String, PathBuf>,
    input: &StoredInput,
) -> Result<ChcDiagnosticCase> {
    if !super::input::direct_solver_file(input) || input.kind.as_deref() != Some("horn-query") {
        return Err(BenchError::msg(format!(
            "{} is not an available stored whole-HORN diagnostic",
            input.id
        )));
    }
    if input
        .smt_logic
        .as_deref()
        .is_some_and(|logic| logic != "HORN")
    {
        return Err(BenchError::msg(format!(
            "{} declares a non-HORN logic",
            input.id
        )));
    }
    let sha256 = input
        .sha256
        .as_deref()
        .ok_or_else(|| BenchError::msg(format!("{} lacks its exact input digest", input.id)))?;
    super::validation::sha256(sha256)?;
    let size = input
        .size_bytes
        .filter(|size| *size > 0 && *size <= crate::resource::MAX_DECOMPRESSED_BYTES)
        .ok_or_else(|| BenchError::msg(format!("{} lacks a bounded exact input size", input.id)))?;
    let semantic_expectation = SemanticExpectation::from_inventory(&input.expected_semantic_result)
        .ok_or_else(|| {
            BenchError::msg(format!("{} has an unresolved consumer oracle", input.id))
        })?;
    let dialect = InputDialect::HornQuery;
    let expected_cli_status = dialect
        .cli_status(semantic_expectation)
        .ok_or_else(|| BenchError::msg("diagnostic semantic expectation has no CLI status"))?;
    validate_envelope(inventory, input)?;
    let original_revision = input_revision(inventory, input)?;
    let timeout_ms = input_timeout(inventory, input, InputDialect::HornQuery)?;
    let root = roots.get(&input.repository).ok_or_else(|| {
        BenchError::msg(format!(
            "{} lacks an explicit repository root",
            input.repository
        ))
    })?;
    let path = resolve_path(root, &input.path, size)?;
    Ok(ChcDiagnosticCase {
        input_id: input.id.clone(),
        request_ids: input.request_ids.clone(),
        path,
        expected_sha256: format!("sha256:{sha256}"),
        expected_size_bytes: size,
        original_repository: input.repository.clone(),
        original_revision,
        original_path: input.path.clone(),
        dialect,
        semantic_expectation,
        expected_cli_status,
        proof_policy: ProofPolicy::StrictOriginalQuery,
        timeout_ms,
        solver_memory_mib: DIAGNOSTIC_MEMORY_MIB,
        tree_memory_mib: DIAGNOSTIC_MEMORY_MIB,
        promotable_for_ask_closure: false,
    })
}

pub(super) fn validate_envelope(inventory: &Inventory, input: &StoredInput) -> Result<()> {
    const POLICY_ID: &str = "serial-enforced-tree-4g";
    let policy = inventory
        .document
        .resource_policies
        .iter()
        .find(|policy| policy.id == POLICY_ID)
        .ok_or_else(|| BenchError::msg("diagnostic requires serial-enforced-tree-4g policy"))?;
    let jobs = policy
        .details
        .get("jobs")
        .and_then(serde_json::Value::as_u64);
    let tree_bytes = policy
        .details
        .get("child_tree_peak_bytes_max")
        .and_then(serde_json::Value::as_u64);
    let solver_bytes = policy
        .details
        .get("solver_budget_bytes")
        .map(serde_json::Value::as_u64);
    let expected_bytes = (DIAGNOSTIC_MEMORY_MIB as u64) * 1024 * 1024;
    if jobs != Some(1)
        || tree_bytes != Some(expected_bytes)
        || solver_bytes.is_some_and(|value| value != Some(expected_bytes))
    {
        return Err(BenchError::msg(
            "diagnostic serial-enforced-tree-4g policy has a contradictory or missing envelope",
        ));
    }
    for id in &input.request_ids {
        let request = inventory
            .document
            .request_inventory
            .iter()
            .find(|request| request.id == *id)
            .ok_or_else(|| BenchError::msg(format!("undefined diagnostic request: {id}")))?;
        if !request
            .resource_policy_ids(&inventory.document.case_defaults)
            .contains(&POLICY_ID)
        {
            return Err(BenchError::msg(format!(
                "{id} does not declare the diagnostic serial-enforced-tree-4g profile"
            )));
        }
    }
    // Other request variants remain unresolved in plan(); selecting this
    // diagnostic does not replace a historical or machine-default comparison.
    Ok(())
}

pub(super) fn input_revision(inventory: &Inventory, input: &StoredInput) -> Result<String> {
    let revision = match input.revision.as_deref() {
        Some(revision) => revision,
        None if input.repository == "model-checker-consumer" => {
            &inventory
                .document
                .case_defaults
                .stored_model_checker_consumer_input_revision
        }
        None => {
            return Err(BenchError::msg(format!(
                "{} has no repository revision",
                input.id
            )))
        }
    };
    super::validation::revision(revision)?;
    Ok(revision.to_owned())
}

pub(super) fn input_timeout(
    inventory: &Inventory,
    input: &StoredInput,
    dialect: InputDialect,
) -> Result<u64> {
    let mut timeout = None;
    for id in &input.request_ids {
        let request = inventory
            .document
            .request_inventory
            .iter()
            .find(|request| request.id == *id)
            .ok_or_else(|| BenchError::msg(format!("undefined diagnostic request: {id}")))?;
        // The frozen strict-SMT controls are distinct from the consumer cohort.
        // This route's declared duration never replaces the runner's enclosing
        // absolute deadline. Longer unrelated diagnostic metadata is ignored.
        let route_bound = match (
            dialect,
            request.metadata.get("strict_smt_control_budget_ms"),
        ) {
            (InputDialect::Smt2, Some(value)) => Some(value.as_u64().ok_or_else(|| {
                BenchError::msg("strict SMT control budget must be an integer duration")
            })?),
            _ => request.harness_or_solve_budget_ms,
        };
        let bound = route_bound.ok_or_else(|| {
            BenchError::msg(format!(
                "{} needs a route-specific timeout binding",
                request.id
            ))
        })?;
        super::validation::timeout_ms(bound)?;
        timeout = Some(timeout.map_or(bound, |previous: u64| previous.min(bound)));
    }
    timeout.ok_or_else(|| BenchError::msg("diagnostic has no bound request timeout"))
}

pub(super) fn resolve_path(root: &Path, relative: &str, expected_size: u64) -> Result<PathBuf> {
    super::validation::relative_path(relative)?;
    let root_metadata = fs::symlink_metadata(root).with_bench_context(|| {
        format!("inspecting diagnostic repository root {}", root.display())
    })?;
    if !root_metadata.file_type().is_dir() {
        return Err(BenchError::msg(
            "diagnostic repository root must be a non-symlink directory",
        ));
    }
    let root = fs::canonicalize(root)?;
    let mut path = root.clone();
    let relative = Path::new(relative);
    let mut parts = relative.components().peekable();
    while let Some(part) = parts.next() {
        path.push(part.as_os_str());
        let metadata = fs::symlink_metadata(&path)
            .with_bench_context(|| format!("inspecting diagnostic input {}", path.display()))?;
        if parts.peek().is_some() {
            if !metadata.file_type().is_dir() {
                return Err(BenchError::msg(
                    "diagnostic source directory must not be a symlink",
                ));
            }
        } else if !metadata.file_type().is_file() || metadata.len() != expected_size {
            return Err(BenchError::msg(
                "diagnostic source must be a regular file of the declared size",
            ));
        }
    }
    let canonical = fs::canonicalize(&path)?;
    if !canonical.starts_with(&root) {
        return Err(BenchError::msg(
            "diagnostic input escapes its explicit repository root",
        ));
    }
    Ok(canonical)
}
