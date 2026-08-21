// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

pub(super) struct ParseState {
    pub(super) certificate: Certificate,
    pub(super) saw_version: bool,
}

impl ParseState {
    pub(super) fn new() -> Self {
        Self {
            certificate: Certificate {
                header: Header {
                    file_digest: String::new(),
                    file_bytes: 0,
                    canon_digest: String::new(),
                    rows: 0,
                    cols: 0,
                    intcols: 0,
                    sense: Sense::Minimize,
                    obj_scale: BigRational::one(),
                    solver: String::new(),
                },
                verdict: String::new(),
                value: None,
                value_frame: String::new(),
                claims: Vec::new(),
                witness: None,
                farkas: None,
                optcert: None,
                optcert_trivial: false,
                tree: None,
                affine_aggregation: None,
                parity_infeasibility: None,
                sat_relu_infeasibility: None,
                network_design_infeasibility: None,
                network_design_optimality: None,
                block_angular_optimality: None,
                single_machine_scheduling_optimality: None,
                single_row_dp: None,
                multi_row_bdd: None,
                open_domain_dp: None,
                open_domain_bdd: None,
                open_domain_hybrid_pb_lp: None,
                open_domain_hybrid_integer_lift: None,
                hybrid_pb_lp: None,
                hybrid_integer_lift: None,
                replay: Vec::new(),
                unchecked: Vec::new(),
                truncated: Vec::new(),
                reason: None,
                end_digest_ok: false,
            },
            saw_version: false,
        }
    }
}

/// Parse a `.ayc` certificate.
///
/// # Errors
/// Returns [`CertIoError`] for malformed input, unsupported versions,
/// mislabelled evidence, or proof values outside their arithmetic caps.
pub(super) fn parse_metadata(
    fields: &[&str],
    record: &str,
    line: &mut usize,
    state: &mut ParseState,
) -> Result<(), CertIoError> {
    match fields[0] {
        "%AYC" => parse_version(fields, *line, state)?,
        "model" => parse_model_header(fields, *line, &mut state.certificate.header)?,
        "solver" => state.certificate.header.solver = record.to_owned(),
        "verdict" => parse_verdict(fields, *line, &mut state.certificate)?,
        "evidence" => state
            .certificate
            .claims
            .push(parse_evidence(fields, *line)?),
        "unchecked" => state.certificate.unchecked.push(record.to_owned()),
        "truncated" => state.certificate.truncated.push(record.to_owned()),
        "reason" => {
            state.certificate.reason = Some(record["reason".len()..].trim().to_owned());
        }
        _ => return Err(malformed(*line, "unknown metadata record")),
    }
    *line += 1;
    Ok(())
}

pub(super) fn parse_version(
    fields: &[&str],
    line: usize,
    state: &mut ParseState,
) -> Result<(), CertIoError> {
    let version = fields
        .get(1)
        .and_then(|value| value.parse::<u32>().ok())
        .ok_or_else(|| malformed(line, "malformed %AYC version"))?;
    if version != AYC_VERSION {
        return Err(malformed(
            line,
            &format!("unsupported format version {version}"),
        ));
    }
    state.saw_version = true;
    Ok(())
}

pub(super) fn parse_model_header(
    fields: &[&str],
    line: usize,
    header: &mut Header,
) -> Result<(), CertIoError> {
    match fields.get(1).copied() {
        Some("file") => {
            header.file_digest = strip_sha(fields.get(2).copied().unwrap_or_default())
                .ok_or_else(|| malformed(line, "malformed model file digest"))?;
            header.file_bytes = kv_usize(fields, "bytes")
                .ok_or_else(|| malformed(line, "malformed model file bytes"))?;
        }
        Some("canon") => {
            if fields.get(2) != Some(&"v1") {
                return Err(malformed(line, "unsupported canonicalisation rule"));
            }
            header.canon_digest = strip_sha(fields.get(3).copied().unwrap_or_default())
                .ok_or_else(|| malformed(line, "malformed canon digest"))?;
        }
        Some("shape") => parse_shape(fields, line, header)?,
        _ => return Err(malformed(line, "unknown model record")),
    }
    Ok(())
}

pub(super) fn parse_shape(
    fields: &[&str],
    line: usize,
    header: &mut Header,
) -> Result<(), CertIoError> {
    header.rows = kv_usize(fields, "rows").ok_or_else(|| malformed(line, "shape rows"))?;
    header.cols = kv_usize(fields, "cols").ok_or_else(|| malformed(line, "shape cols"))?;
    header.intcols = kv_usize(fields, "intcols").ok_or_else(|| malformed(line, "shape intcols"))?;
    header.sense = kv(fields, "sense")
        .and_then(parse_sense)
        .ok_or_else(|| malformed(line, "shape sense"))?;
    header.obj_scale = kv(fields, "obj_scale")
        .and_then(parse_rat)
        .ok_or_else(|| malformed(line, "shape obj_scale"))?;
    Ok(())
}

pub(super) fn parse_verdict(
    fields: &[&str],
    line: usize,
    certificate: &mut Certificate,
) -> Result<(), CertIoError> {
    certificate.verdict = fields
        .get(1)
        .ok_or_else(|| malformed(line, "verdict has no word"))?
        .to_string();
    if let Some(value) = kv(fields, "value") {
        certificate.value =
            Some(parse_rat(value).ok_or_else(|| malformed(line, "malformed verdict value"))?);
        certificate.value_frame = kv(fields, "frame")
            .ok_or_else(|| malformed(line, "verdict value has no frame"))?
            .to_owned();
    }
    Ok(())
}

pub(super) fn parse_evidence(fields: &[&str], line: usize) -> Result<ParsedClaim, CertIoError> {
    let name = fields
        .get(1)
        .ok_or_else(|| malformed(line, "evidence has no claim"))?;
    let kind = fields
        .get(2)
        .and_then(|token| EvidenceKind::from_token(token))
        .ok_or_else(|| malformed(line, "evidence has no kind"))?;
    let source = fields.get(3).map(|value| (*value).to_owned());
    validate_evidence_source(kind, source.as_deref(), line)?;
    Ok(ParsedClaim {
        name: (*name).to_owned(),
        kind,
        source,
    })
}

pub(super) fn validate_evidence_source(
    kind: EvidenceKind,
    source: Option<&str>,
    line: usize,
) -> Result<(), CertIoError> {
    let required = match kind {
        EvidenceKind::Succinct => source
            .ok_or_else(|| malformed(line, "SUCCINCT evidence names no source"))
            .map(|source| (source, SUCCINCT_SOURCES.contains(&source))),
        EvidenceKind::Replay => source
            .ok_or_else(|| malformed(line, "REPLAY evidence names no claim"))
            .map(|source| (source, !SUCCINCT_SOURCES.contains(&source))),
        EvidenceKind::None => {
            return match source {
                Some(source) if !NONE_SOURCES.contains(&source) => {
                    Err(mislabelled(line, kind, source))
                }
                _ => Ok(()),
            }
        }
    }?;
    if required.1 {
        Ok(())
    } else {
        Err(mislabelled(line, kind, required.0))
    }
}

pub(super) fn malformed(line: usize, message: &str) -> CertIoError {
    CertIoError::Malformed {
        line: line + 1,
        msg: message.to_owned(),
    }
}

pub(super) fn mislabelled(line: usize, kind: EvidenceKind, source: &str) -> CertIoError {
    CertIoError::MislabelledEvidence {
        line: line + 1,
        kind: kind.token().to_owned(),
        source_token: source.to_owned(),
    }
}
