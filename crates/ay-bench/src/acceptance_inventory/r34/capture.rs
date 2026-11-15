// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use crate::{BenchError, Result};
use serde::Deserialize;
use serde_json::Value;
use sha2::{Digest as _, Sha256};
use std::collections::BTreeMap;

#[derive(Deserialize)]
pub(super) struct Capture {
    pub archive: ArchiveIdentity,
    pub sources: BTreeMap<String, Source>,
    pub rows: Vec<Row>,
    pub witnesses: Vec<Witness>,
    pub files: BTreeMap<String, FileIdentity>,
    pub dispositions: BTreeMap<String, String>,
}

#[derive(Deserialize)]
pub(super) struct ArchiveIdentity {
    pub path: String,
    pub sha256: String,
    pub bytes: u64,
}

#[derive(Deserialize)]
pub(super) struct FileIdentity {
    pub sha256: String,
    pub bytes: u64,
}

#[derive(Deserialize)]
pub(super) struct Source {
    pub base: String,
    pub source: Value,
    pub source_problem: Value,
    pub aggregate_problem: Value,
    pub per_property_batch: Value,
    pub execution_environment: Value,
}

#[derive(Deserialize)]
pub(super) struct Row {
    pub source: String,
    pub label: String,
    pub timeout_ns: u64,
    pub config_file: String,
    pub row: Value,
}

#[derive(Deserialize)]
pub(super) struct Witness {
    pub source: String,
    pub record: Value,
    pub remaining_budget_recorded: bool,
}

pub(super) fn load() -> Result<Capture> {
    Ok(serde_json::from_str(include_str!("capture.json"))?)
}

pub(super) fn string<'a>(value: &'a Value, key: &str) -> Result<&'a str> {
    value
        .get(key)
        .and_then(Value::as_str)
        .ok_or_else(|| BenchError::msg(format!("R34 capture lacks string {key}")))
}

pub(super) fn number(value: &Value, key: &str) -> Result<u64> {
    value
        .get(key)
        .and_then(Value::as_u64)
        .ok_or_else(|| BenchError::msg(format!("R34 capture lacks number {key}")))
}

pub(super) fn digest(bytes: &[u8]) -> String {
    format!("{:x}", Sha256::digest(bytes))
}

pub(super) fn require_hash(actual: &str, expected: &str, what: &str) -> Result<()> {
    if actual != expected {
        return Err(BenchError::msg(format!(
            "R34 {what} identity mismatch: expected {expected}, observed {actual}; no solve"
        )));
    }
    Ok(())
}

pub(super) fn parse_source(
    archive: &super::R34Archive,
    source: &Source,
) -> Result<ay_chc::ChcProblem> {
    let path = format!("{}/{}", source.base, string(&source.source, "file")?);
    let text = archive.text(&path)?;
    require_hash(
        &digest(text.as_bytes()),
        string(&source.source, "sha256")?,
        "source bytes",
    )?;
    ay_chc::ChcParser::parse(text)
        .map_err(|error| BenchError::msg(format!("R34 source parse: {error}")))
}
