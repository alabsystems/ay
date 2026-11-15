// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use ay_chc::engines::ExternalInvariantValidationOwner;
use ay_chc::{CancellationToken, PdrConfig};
use ay_core::resource::ResourceGuard;
use ay_core::time::Instant;
use serde::Serialize;

use super::{capture, chc_error, refused, R34Archive, R34Row, R34RowRecord, R34RowStatus};
use crate::{BenchError, Result};

#[cfg(test)]
mod deadline_tests;
mod execution;
mod preparation;
#[cfg(test)]
mod validation_tests;

#[derive(Debug, Serialize)]
pub struct R34PreparedIdentity {
    pub source_schema: String,
    pub source_sha256: String,
    pub content_schema: String,
    pub content_sha256: String,
    pub prepared_schema: String,
    pub prepared_sha256: String,
    /// Unmatched identities; authenticated schema changes are recorded separately.
    pub mismatches: Vec<String>,
    /// Exact historical equivalence checks, not waivers or proof authority.
    pub migrations: Vec<String>,
}

enum Mode {
    BindOnly,
    Execute,
}

impl R34Archive {
    /// Reconstruct the actual prepared problem, without any solver invocation.
    /// Only an exact authenticated historical equivalence can migrate identity;
    /// unrelated differences refuse instead of rebaselining themselves.
    pub fn inspect_row(
        &self,
        case: R34Row,
        original: &ResourceGuard,
        cancellation: &CancellationToken,
    ) -> Result<R34RowRecord> {
        self.row_attempt(case, original, cancellation, Mode::BindOnly)
    }

    /// Use the unchanged production ay-encode entrypoint. Validation and checked
    /// replay consume the original remainder, never new full-duration grants.
    /// This is cooperative and is NOT complete primitive accounting or a hard
    /// process-RSS/drain guarantee. The outer harness must enforce those bounds.
    pub fn replay_row(
        &self,
        case: R34Row,
        original: &ResourceGuard,
        cancellation: &CancellationToken,
    ) -> Result<R34RowRecord> {
        self.row_attempt(case, original, cancellation, Mode::Execute)
    }

    fn row_attempt(
        &self,
        case: R34Row,
        original: &ResourceGuard,
        cancellation: &CancellationToken,
        mode: Mode,
    ) -> Result<R34RowRecord> {
        let started = Instant::now();
        let row = self
            .capture
            .rows
            .get(case.index())
            .ok_or_else(|| BenchError::msg("R34 captured row is absent"))?;
        let source = self
            .capture
            .sources
            .get(&row.source)
            .ok_or_else(|| BenchError::msg("R34 captured source is absent"))?;
        let config = preparation::config(self, row)?;
        let mut validation = config.to_pdr_config();
        validation.cancellation_token = Some(cancellation.clone());
        let owner = row_owner(original, &validation, started, row.timeout_ns)?;
        let mut binding = None;
        let attempt = owner.with_resources(|| {
            let Some(mut prepared) = preparation::prepare_with_progress(self, row, &mut || {
                owner.check().is_none()
            }).map_err(chc_error)? else {
                return Ok(refused(owner.check().unwrap_or(
                    ay_chc::engines::ExternalInvariantValidation::Inconclusive,
                )));
            };
            match preparation::adaptive_binding(self, row, &config).map_err(chc_error)? {
                preparation::AdaptiveBinding::Exact => {}
                preparation::AdaptiveBinding::HistoricalGroundTraceFalse => prepared.identity
                    .migrations.push("AdaptiveConfig: exact historical fields plus require_ground_unsafe_trace=false (legacy pass-through semantics)".to_owned()),
                preparation::AdaptiveBinding::Refused(reason) => prepared.identity.mismatches.push(reason),
            }
            let mismatch = (!prepared.identity.mismatches.is_empty())
                .then(|| prepared.identity.mismatches.join("; "));
            binding = Some(prepared.identity);
            if let Some(reason) = mismatch {
                return Ok(R34RowStatus::BindingRefused { reason });
            }
            match mode {
                Mode::BindOnly => Ok(R34RowStatus::BoundOnly),
                Mode::Execute => {
                    execution::run(prepared.problem, &config, validation, &owner, cancellation)
                }
            }
        });
        // The retained problem, model and proof run have died inside the phase.
        // This final fence also covers the phase's temporary TLS cleanup.
        let status = match attempt {
            Err(error) => R34RowStatus::ExecutionError {
                reason: error.to_string(),
            },
            Ok(Err(kind)) => refused(kind),
            Ok(Ok(status)) => owner.check().map_or(status, refused),
        };
        let config_identity = self
            .capture
            .files
            .get(&row.config_file)
            .ok_or_else(|| BenchError::msg("R34 config identity is absent"))?;
        let mut record = R34RowRecord {
            case,
            inventory_sha256: self.inventory_sha256.clone(),
            archive_sha256: self.capture.archive.sha256.clone(),
            source_sha256: capture::string(&source.source, "sha256")?.to_owned(),
            content_sha256: capture::string(&row.row["identity"], "content_sha256")?.to_owned(),
            prepared_sha256: capture::string(
                &row.row["prepared_problem"],
                "normalized_input_sha256",
            )?
            .to_owned(),
            original_timeout_ns: row.timeout_ns,
            original_config_sha256: config_identity.sha256.clone(),
            captured_environment: source.execution_environment.clone(),
            elapsed_ns: started.elapsed().as_nanos(),
            current_binding: binding,
            status,
            promotable_for_ask_closure: false,
        };
        if let Some(kind) = owner.check() {
            // Keep genuine internal/reconstruction errors even when retirement
            // also observes a resource stop, matching the typed owner contract.
            if !matches!(record.status, R34RowStatus::ExecutionError { .. }) {
                record.status = refused(kind);
            }
        }
        Ok(record)
    }
}

fn row_owner(
    original: &ResourceGuard,
    validation: &PdrConfig,
    started: Instant,
    timeout_ns: u64,
) -> Result<ExternalInvariantValidationOwner> {
    // Bind the absolute row end, not a sampled remainder later rebased by
    // capture(). Configuration inspection and every later phase consume it.
    let end = started
        .checked_add(std::time::Duration::from_nanos(timeout_ns))
        .ok_or_else(|| BenchError::msg("R34 absolute row deadline overflow"))?;
    let end = original.effective_deadline().map_or(end, |at| at.min(end));
    let mut bounded = original.clone();
    // A setter on a clone makes a view: ticks, cancellation and ancestor caps
    // remain shared, while the caller's own deadline is never rewritten.
    bounded.set_deadline(Some(end));
    Ok(ExternalInvariantValidationOwner::capture(
        &bounded, validation,
    ))
}
