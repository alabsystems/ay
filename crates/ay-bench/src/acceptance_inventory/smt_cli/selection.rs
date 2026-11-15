// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::super::{InputDialect, Inventory, SemanticExpectation};
use super::{SmtCliCase, SmtMemoryVariant};
use crate::{BenchError, Result};
use serde::Deserialize;
use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Selection {
    schema: String,
    inventory: PathBuf,
    inventory_sha256: String,
    repository_roots: BTreeMap<String, PathBuf>,
    stored_input_ids: Vec<String>,
    memory_variants: Vec<SmtMemoryVariant>,
}

pub(super) fn load(path: &Path) -> Result<(Inventory, String, Vec<SmtCliCase>)> {
    let bytes = crate::resource::read_bounded_text(path, 1024 * 1024, "SMT acceptance selection")?;
    let selected: Selection = serde_json::from_str(&bytes)?;
    if selected.schema != "ay.model-checker-consumer-smt-cli-selection/v1" {
        return Err(invalid("unsupported SMT acceptance selection schema"));
    }
    if selected.stored_input_ids.is_empty()
        || selected.memory_variants.is_empty()
        || selected.memory_variants.len() > 3
        || selected.stored_input_ids.len() > 256
    {
        return Err(invalid("empty or oversized SMT acceptance selection"));
    }
    let parent = path.parent().unwrap_or_else(|| Path::new("."));
    let inventory = Inventory::load(&parent.join(selected.inventory))?;
    if inventory.sha256 != selected.inventory_sha256 {
        return Err(invalid("inventory hash mismatch"));
    }
    let roots: BTreeMap<_, _> = selected
        .repository_roots
        .into_iter()
        .map(|(name, path)| (name, parent.join(path)))
        .collect();
    let cases = select(
        &inventory,
        &roots,
        &selected.stored_input_ids,
        &selected.memory_variants,
    )?;
    Ok((inventory, super::snapshot::hash(bytes.as_bytes()), cases))
}

pub(super) fn select(
    inventory: &Inventory,
    roots: &BTreeMap<String, PathBuf>,
    ids: &[String],
    variants: &[SmtMemoryVariant],
) -> Result<Vec<SmtCliCase>> {
    let mut seen = BTreeSet::new();
    let mut paths = BTreeSet::new();
    let mut profiles = BTreeSet::new();
    for variant in variants {
        if !profiles.insert(variant.policy()) {
            return Err(invalid("duplicate memory profile"));
        }
    }
    let mut cases = Vec::new();
    for id in ids {
        if !seen.insert(id) {
            return Err(invalid("duplicate input selection"));
        }
        let input = inventory
            .document
            .stored_inputs
            .iter()
            .find(|input| input.id == *id)
            .ok_or_else(|| invalid("undefined SMT input"))?;
        if !super::super::input::direct_solver_file(input) || input.kind.as_deref() != Some("smt2")
        {
            return Err(invalid("SMT route requires available original SMT bytes"));
        }
        if input.id.len() > 256
            || input.repository.len() > 128
            || input.path.len() > 4096
            || input.request_ids.len() > 28
            || input.request_ids.iter().any(|id| id.len() > 32)
        {
            return Err(invalid(
                "SMT input identity exceeds bounded metadata profile",
            ));
        }
        if input.smt_logic.as_deref() == Some("HORN") {
            return Err(invalid("declared HORN input cannot use the SMT route"));
        }
        let digest = input
            .sha256
            .as_deref()
            .ok_or_else(|| invalid("missing input hash"))?;
        super::super::validation::sha256(digest)?;
        let size = input
            .size_bytes
            .filter(|n| *n > 0 && *n <= crate::resource::MAX_DECOMPRESSED_BYTES)
            .ok_or_else(|| invalid("missing or unbounded input size"))?;
        let expected = SemanticExpectation::from_inventory(&input.expected_semantic_result)
            .and_then(|expected| InputDialect::Smt2.cli_status(expected))
            .ok_or_else(|| invalid("unbound SMT oracle or dialect mismatch"))?;
        let revision = super::super::diagnostic::input_revision(inventory, input)?;
        let timeout_ms =
            super::super::diagnostic::input_timeout(inventory, input, InputDialect::Smt2)?;
        let root = roots
            .get(&input.repository)
            .ok_or_else(|| invalid("missing repository root"))?;
        let path = super::super::diagnostic::resolve_path(root, &input.path, size)?;
        if !paths.insert(path.clone()) {
            return Err(invalid("aliased selected input paths"));
        }
        for variant in variants {
            validate_profile(inventory, input, *variant)?;
            cases.push(SmtCliCase {
                input_id: id.clone(),
                request_ids: input.request_ids.clone(),
                repository: input.repository.clone(),
                revision: revision.clone(),
                original_path: input.path.clone(),
                path: path.clone(),
                sha256: format!("sha256:{digest}"),
                size_bytes: size,
                expected,
                timeout_ms,
                variant: *variant,
            });
        }
    }
    Ok(cases)
}

fn validate_profile(
    inventory: &Inventory,
    input: &super::super::StoredInput,
    variant: SmtMemoryVariant,
) -> Result<()> {
    super::super::diagnostic::validate_envelope(inventory, input)?;
    let profile = inventory
        .document
        .resource_policies
        .iter()
        .find(|p| p.id == variant.policy())
        .ok_or_else(|| invalid("missing memory profile"))?;
    for id in &input.request_ids {
        let request = inventory
            .document
            .request_inventory
            .iter()
            .find(|request| request.id == *id)
            .ok_or_else(|| invalid("missing request"))?;
        if !request
            .required_routes
            .iter()
            .any(|route| route == "smt-cli")
            || !request
                .resource_policy_ids(&inventory.document.case_defaults)
                .contains(&variant.policy())
        {
            return Err(invalid("request does not declare this SMT route/profile"));
        }
    }
    if variant == SmtMemoryVariant::Historical2GiB
        && profile
            .details
            .get("solver_budget_bytes")
            .and_then(serde_json::Value::as_u64)
            != Some(2 * 1024 * 1024 * 1024)
    {
        return Err(invalid("historical profile does not bind exactly2GiB"));
    }
    if variant == SmtMemoryVariant::MachineDefault
        && !profile
            .details
            .get("solver_budget_bytes")
            .is_some_and(serde_json::Value::is_string)
    {
        return Err(invalid(
            "machine-default profile lacks a declared observation requirement",
        ));
    }
    if variant != SmtMemoryVariant::Serial4GiB
        && (profile
            .details
            .get("jobs")
            .and_then(serde_json::Value::as_u64)
            != Some(1)
            || profile
                .details
                .get("enforced_process_tree_cap_required")
                .and_then(serde_json::Value::as_bool)
                != Some(true))
    {
        return Err(invalid("profile lacks serial enforced tree contract"));
    }
    Ok(())
}

pub(super) fn invalid(detail: impl Into<String>) -> BenchError {
    BenchError::msg(detail)
}
