// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

pub(super) struct CheckReportSeal {
    _private: (),
}

impl CheckReportSeal {
    fn new() -> Self {
        Self { _private: () }
    }
}

pub(super) struct CheckState {
    pub(super) status: CheckStatus,
    pub(super) notes: Vec<String>,
}

impl CheckState {
    pub(super) fn new() -> Self {
        Self {
            status: CheckStatus::Verified,
            notes: Vec::new(),
        }
    }

    pub(super) fn demote(&mut self, status: CheckStatus) {
        if status_rank(status) > status_rank(self.status) {
            self.status = status;
        }
    }
}

/// Independently re-check a `.ayc` certificate against the original model text.
///
/// The checker re-parses the model and re-derives every binding and claim. A
/// replay-only claim can never reach [`CheckStatus::Verified`].
#[must_use]
pub fn check(cert_text: &str, model_text: &str) -> CheckReport {
    let certificate = match parse(cert_text) {
        Ok(certificate) => certificate,
        Err(error) => return malformed_report(error),
    };
    let mut state = CheckState::new();
    check_file_binding(&certificate, model_text, &mut state);
    let problem = match crate::read_mps(model_text) {
        Ok(problem) => problem,
        Err(error) => {
            state.notes.push(format!("model does not parse: {error}"));
            return CheckReport::new(
                CheckReportSeal::new(),
                CheckStatus::Mismatch,
                Vec::new(),
                state.notes,
            );
        }
    };
    check_model_binding(&certificate, &problem, &mut state);
    let claimed_value = claimed_model_value(&certificate, &problem.obj_scale);
    let affine = verify_affine(&certificate, &problem.model, &mut state);
    let reports = check_claims(
        &certificate,
        &problem.model,
        claimed_value.as_ref(),
        affine.as_ref(),
        &mut state,
    );
    enforce_claim_policy(&certificate, &mut state);
    append_metadata_notes(&certificate, &reports, &mut state);
    if state.status == CheckStatus::Unverified && reports.iter().any(ClaimReport::is_verified) {
        state.status = CheckStatus::Partial;
    }
    CheckReport::new(CheckReportSeal::new(), state.status, reports, state.notes)
}

fn malformed_report(error: CertIoError) -> CheckReport {
    CheckReport::new(
        CheckReportSeal::new(),
        CheckStatus::Refuted,
        Vec::new(),
        vec![format!("certificate malformed: {error}")],
    )
}

fn status_rank(status: CheckStatus) -> u8 {
    match status {
        CheckStatus::Verified => 0,
        CheckStatus::Partial => 1,
        CheckStatus::Unverified => 2,
        CheckStatus::Refuted => 3,
        CheckStatus::Mismatch => 4,
    }
}

fn check_file_binding(certificate: &Certificate, model_text: &str, state: &mut CheckState) {
    let digest = sha256_hex(model_text.as_bytes());
    if digest == certificate.header.file_digest && model_text.len() == certificate.header.file_bytes
    {
        state
            .notes
            .push(format!("model file digest matches (sha256:{digest})"));
    } else {
        state.notes.push(format!(
            "model file digest MISMATCH: certificate says sha256:{} bytes={}, this file is \
             sha256:{digest} bytes={}",
            certificate.header.file_digest,
            certificate.header.file_bytes,
            model_text.len()
        ));
        state.demote(CheckStatus::Mismatch);
    }
    if !certificate.end_digest_ok {
        state
            .notes
            .push("%END body digest MISMATCH (the certificate was edited)".into());
        state.demote(CheckStatus::Mismatch);
    }
}

fn check_model_binding(
    certificate: &Certificate,
    problem: &crate::MpsProblem,
    state: &mut CheckState,
) {
    let model = &problem.model;
    let digest = canonical_digest(model);
    if digest == certificate.header.canon_digest {
        state
            .notes
            .push(format!("model canon v1 digest matches (sha256:{digest})"));
    } else {
        state.notes.push(format!(
            "model canon v1 digest MISMATCH: certificate says sha256:{}, re-derived sha256:{digest}",
            certificate.header.canon_digest
        ));
        state.demote(CheckStatus::Mismatch);
    }
    let intcols = (0..model.num_cols())
        .filter(|&column| model.col_kind(Col(column as u32)).is_integral())
        .count();
    if certificate.header.rows != model.num_rows()
        || certificate.header.cols != model.num_cols()
        || certificate.header.intcols != intcols
        || certificate.header.sense != model.sense()
        || certificate.header.obj_scale != problem.obj_scale
    {
        state
            .notes
            .push("model shape record MISMATCH against the re-parsed model".into());
        state.demote(CheckStatus::Mismatch);
    }
}

fn claimed_model_value(
    certificate: &Certificate,
    objective_scale: &BigRational,
) -> Option<BigRational> {
    certificate
        .value
        .as_ref()
        .map(|value| match certificate.value_frame.as_str() {
            "file" => value * objective_scale,
            _ => value.clone(),
        })
}

fn verify_affine(
    certificate: &Certificate,
    model: &Model,
    state: &mut CheckState,
) -> Option<Result<AffineAggregationVerification, AffineAggregationCertificateError>> {
    let verification = certificate
        .affine_aggregation
        .as_ref()
        .map(|artifact| artifact.verify(model));
    if let Some(Err(error)) = &verification {
        state.notes.push(format!(
            "affine aggregation artifact DOES NOT verify: {error}"
        ));
        state.demote(CheckStatus::Refuted);
    }
    verification
}
