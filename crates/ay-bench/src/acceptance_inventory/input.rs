// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Archive identities and typed artifacts are provenance, not parser inputs.

use super::{validation, StoredInput};
use crate::{BenchError, Result};

pub(super) fn archived(input: &StoredInput) -> bool {
    input.availability == "tracked-archive-member" || input.metadata.contains_key("archive_member")
}

pub(super) fn direct_solver_file(input: &StoredInput) -> bool {
    super::planning::tracked(&input.availability)
        && !archived(input)
        && input
            .metadata
            .get("not_smtlib_parser_input")
            .and_then(serde_json::Value::as_bool)
            != Some(true)
}

pub(super) fn validate(input: &StoredInput) -> Result<()> {
    if let Some(flag) = input.metadata.get("not_smtlib_parser_input") {
        if !flag.is_boolean() {
            return Err(BenchError::msg("parser-input exclusion must be a boolean"));
        }
    }
    let archive_fields = ["archive_member", "archive_sha256", "archive_size_bytes"];
    if !archived(input)
        && !archive_fields
            .iter()
            .any(|key| input.metadata.contains_key(*key))
    {
        return Ok(());
    }
    if input.availability != "tracked-archive-member" {
        return Err(BenchError::msg(
            "archive member cannot be relabelled as a direct solver file",
        ));
    }
    let member = input
        .metadata
        .get("archive_member")
        .and_then(serde_json::Value::as_str)
        .ok_or_else(|| BenchError::msg("archive input lacks a member path"))?;
    validation::relative_path(member)?;
    let digest = input
        .metadata
        .get("archive_sha256")
        .and_then(serde_json::Value::as_str)
        .ok_or_else(|| BenchError::msg("archive input lacks its container digest"))?;
    validation::sha256(digest)?;
    if !input
        .metadata
        .get("archive_size_bytes")
        .and_then(serde_json::Value::as_u64)
        .is_some_and(|size| size > 0)
        || input.sha256.is_none()
        || input.size_bytes.is_none()
    {
        return Err(BenchError::msg(
            "archive input requires separate container and member identities",
        ));
    }
    Ok(())
}
