// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::{capture, R34Archive, R34PreparedIdentity};
use crate::{BenchError, Result};
use ay_chc::{AdaptiveExecutionMode, ChcProblem};
use ay_encode::invoke::{EncodeConfig, Engine, ProofMode};
use std::time::Duration;

mod identity;
#[cfg(test)]
mod migration_tests;

pub(super) struct Prepared {
    pub problem: ChcProblem,
    pub identity: R34PreparedIdentity,
}

pub(super) fn config(archive: &R34Archive, row: &capture::Row) -> Result<EncodeConfig> {
    let call = &row.row["solve_call"];
    if capture::string(call, "entry_point")?
        != "ay_encode::invoke::solve_with_proof_report_with_cancellation"
        || capture::string(call, "engine")? != "Auto"
        || capture::string(call, "proof_mode")? != "None"
        || capture::string(call, "execution_mode")? != "AdaptiveParallel"
        || call["strict_validation"] != true
        || call["adaptive_strict_proofs"] != true
        || capture::number(call, "lemma_hints")? != 0
        || row.timeout_ns / 1_000_000 != capture::number(call, "timeout_ms")?
    {
        return Err(BenchError::msg(
            "R34 unsupported or inconsistent captured configuration",
        ));
    }
    let memory = usize::try_from(capture::number(call, "memory_budget_bytes")?)
        .map_err(|_| BenchError::msg("R34 memory cap does not fit this platform"))?;
    // Explicit fields avoid changing the captured execution policy via defaults
    // or AY_DETERMINISTIC. The owner and external RSS cap may only tighten it.
    let config = EncodeConfig {
        engine: Engine::Auto,
        timeout: Some(Duration::from_nanos(row.timeout_ns)),
        proof_mode: ProofMode::None,
        strict_validation: true,
        lemma_hints: Vec::new(),
        execution_mode: AdaptiveExecutionMode::AdaptiveParallel,
        memory_budget: Some(memory),
        effort: None,
        pdr_max_frames: None,
    };
    let raw = archive.text(&row.config_file)?;
    let file = archive
        .capture
        .files
        .get(&row.config_file)
        .ok_or_else(|| BenchError::msg("R34 configuration identity is absent"))?;
    capture::require_hash(
        &capture::digest(raw.as_bytes()),
        &file.sha256,
        "configuration bytes",
    )?;
    let expected = raw
        .split_once("EncodeConfig {")
        .and_then(|(_, rest)| rest.split_once("\n\n# AdaptiveConfig"))
        .map(|(config, _)| format!("EncodeConfig {{{}", config.trim_end()))
        .ok_or_else(|| BenchError::msg("R34 archived EncodeConfig boundary is missing"))?;
    require_captured_encode(&config, &expected)?;
    Ok(config)
}

fn require_captured_encode(config: &EncodeConfig, expected: &str) -> Result<()> {
    let current = format!("{config:#?}");
    // Captures predate the optional PDR frame cap and, earlier, effort
    // (origin e8de16eff). This config explicitly leaves both at None. Only
    // their exact default lines may be absent; a requested cap is distinct.
    let without_frame_cap = current.replacen("\n    pdr_max_frames: None,", "", 1);
    let historical = without_frame_cap.replacen("\n    effort: None,", "", 1);
    if current != expected && without_frame_cap != expected && historical != expected {
        return Err(BenchError::msg(
            "R34 exact captured EncodeConfig differs; no solve",
        ));
    }
    Ok(())
}

pub(super) enum AdaptiveBinding {
    Exact,
    HistoricalGroundTraceFalse,
    Refused(String),
}

pub(super) fn adaptive_binding(
    archive: &R34Archive,
    row: &capture::Row,
    config: &EncodeConfig,
) -> Result<AdaptiveBinding> {
    let adaptive = archive
        .text(&row.config_file)?
        .split_once("\nAdaptiveConfig {")
        .map(|(_, body)| format!("AdaptiveConfig {{{}", body.trim_end()))
        .ok_or_else(|| BenchError::msg("R34 archived AdaptiveConfig boundary is missing"))?;
    Ok(compare_adaptive(&config.to_adaptive_config(), &adaptive))
}

fn compare_adaptive(current: &ay_chc::AdaptiveConfig, captured: &str) -> AdaptiveBinding {
    let actual = format!("{current:#?}");
    if actual == captured {
        return AdaptiveBinding::Exact;
    }
    // The only admitted extension is the new false field. Its sole production
    // reader immediately returns the pre-existing outcome when false; no
    // witness replay/holding path is selected. Every other byte stays exact.
    const PRIOR: &str = "\n    strict_proofs: true,\n";
    const EXTENDED: &str = "\n    strict_proofs: true,\n    require_ground_unsafe_trace: false,\n";
    if !current.require_ground_unsafe_trace
        && captured.matches(PRIOR).count() == 1
        && actual == captured.replacen(PRIOR, EXTENDED, 1)
    {
        AdaptiveBinding::HistoricalGroundTraceFalse
    } else {
        AdaptiveBinding::Refused("derived AdaptiveConfig changed beyond the exact false-only historical field extension; no solve".to_owned())
    }
}

pub(super) fn prepare_with_progress(
    archive: &R34Archive,
    row: &capture::Row,
    progress: &mut dyn FnMut() -> bool,
) -> Result<Option<Prepared>> {
    if !progress() {
        return Ok(None);
    }
    let source = archive
        .capture
        .sources
        .get(&row.source)
        .ok_or_else(|| BenchError::msg("R34 source record missing"))?;
    require_recipe(source)?;
    let problem = capture::parse_source(archive, source)?;
    require_dimensions(&problem, &source.source_problem)?;
    let source_normalized = problem.normalized_input();
    let (id, mut prepared) = select(&problem, row)?;
    let identity = &row.row["identity"];
    let content_normalized = prepared.normalized_input();
    capture::require_hash(
        &capture::digest(content_normalized.as_bytes()),
        id.content_sha256(),
        "selected current AST",
    )?;
    let Some(source_match) = identity::compare(
        &problem,
        &source_normalized,
        capture::string(&source.source_problem, "normalized_input_sha256")?,
        None,
        progress,
    )?
    else {
        return Ok(None);
    };
    let Some(content_match) = identity::compare(
        &prepared,
        &content_normalized,
        capture::string(identity, "content_sha256")?,
        None,
        progress,
    )?
    else {
        return Ok(None);
    };
    prepared.expand_nullary_fail_queries(false);
    require_dimensions(&prepared, &row.row["prepared_problem"])?;
    let prepared_normalized = prepared.normalized_input();
    let captured_prepared = archive.text(&format!(
        "{}/{}",
        source.base,
        capture::string(&row.row["prepared_problem"], "file")?
    ))?;
    let Some(prepared_match) = identity::compare(
        &prepared,
        &prepared_normalized,
        capture::string(&row.row["prepared_problem"], "normalized_input_sha256")?,
        Some(captured_prepared),
        progress,
    )?
    else {
        return Ok(None);
    };
    let mut binding = R34PreparedIdentity {
        source_schema: schema(&source_normalized),
        source_sha256: capture::digest(source_normalized.as_bytes()),
        content_schema: id.normalized_input_schema().to_owned(),
        content_sha256: id.content_sha256().to_owned(),
        prepared_schema: schema(&prepared_normalized),
        prepared_sha256: capture::digest(prepared_normalized.as_bytes()),
        mismatches: Vec::new(),
        migrations: Vec::new(),
    };
    for (what, comparison) in [
        ("source normalized", source_match),
        ("obligation content", content_match),
        ("prepared normalized", prepared_match),
    ] {
        match comparison {
            identity::Comparison::Exact => {}
            identity::Comparison::Historical { captured, current } => binding.migrations.push(format!(
                "{what}: actual complete AST matches historical v1={captured}; retained current v2={current}"
            )),
            identity::Comparison::Refused(reason) => binding.mismatches.push(format!("{what}: {reason}")),
        }
    }
    if !progress() {
        return Ok(None);
    }
    Ok(Some(Prepared {
        problem: prepared,
        identity: binding,
    }))
}

fn select(
    problem: &ChcProblem,
    row: &capture::Row,
) -> Result<(ay_chc::ChcQueryObligationId, ChcProblem)> {
    let obligations = problem
        .query_obligations()
        .map_err(|error| BenchError::msg(format!("R34 original slicing: {error}")))?;
    let mut found = obligations
        .into_iter()
        .filter(|row_problem| row_problem.id().label() == row.label);
    let selected = found
        .next()
        .ok_or_else(|| BenchError::msg("R34 original obligation missing"))?;
    if found.next().is_some() {
        return Err(BenchError::msg("R34 ambiguous obligation label"));
    }
    let (id, prepared) = selected.into_parts();
    let identity = &row.row["identity"];
    if id.source_query_ordinal() as u64 != capture::number(identity, "source_query_ordinal")?
        || id.query_clause_index() as u64 != capture::number(identity, "query_clause_index")?
        || id.defining_clause_index().map(|v| v as u64)
            != identity["defining_clause_index"].as_u64()
    {
        return Err(BenchError::msg(
            "R34 original clause/obligation coordinates changed",
        ));
    }
    Ok((id, prepared))
}

fn schema(normalized: &str) -> String {
    normalized.lines().next().unwrap_or("").to_owned()
}

fn require_dimensions(problem: &ChcProblem, captured: &serde_json::Value) -> Result<()> {
    if problem.predicates().len() as u64 != capture::number(captured, "predicates")?
        || problem.clauses().len() as u64 != capture::number(captured, "clauses")?
    {
        return Err(BenchError::msg(
            "R34 captured AST dimensions changed; no solve",
        ));
    }
    Ok(())
}

fn require_recipe(source: &capture::Source) -> Result<()> {
    let recipe = &source.per_property_batch["row_preparation"];
    if recipe["expand_nullary_fail_queries"] != true
        || capture::string(recipe, "transforms")?
            != "ObligationTransforms { scalarize: false, split_ite: false, split_or: false }"
        || source.per_property_batch["skip_verify"] != false
        || source.per_property_batch["lemma_hints"]["count"] != 0
    {
        return Err(BenchError::msg(
            "R34 captured preparation recipe is unsupported",
        ));
    }
    Ok(())
}
