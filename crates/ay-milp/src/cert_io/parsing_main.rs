// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// Parse a `.ayc` certificate.
///
/// # Errors
/// Returns [`CertIoError`] for malformed input, unsupported versions,
/// mislabelled evidence, or proof values outside their arithmetic caps.
pub fn parse(text: &str) -> Result<Certificate, CertIoError> {
    preflight_input(text)?;
    let lines: Vec<&str> = text.lines().collect();
    let mut state = ParseState::new();
    let mut line = 0usize;
    while line < lines.len() {
        let raw = lines[line];
        let record = raw.trim();
        if record.is_empty() || record.starts_with('#') {
            line += 1;
            continue;
        }
        parse_record(text, &lines, &mut line, record, &mut state)?;
    }
    if !state.saw_version {
        return Err(malformed(0, "not an AYC certificate (no %AYC banner)"));
    }
    Ok(state.certificate)
}

fn preflight_input(text: &str) -> Result<(), CertIoError> {
    if text.len() > MAX_AYC_INPUT_BYTES {
        return Err(malformed(0, "AYC input exceeds the 512 MiB parser cap"));
    }
    let line_count = text.bytes().try_fold(1usize, |count, byte| {
        if byte == b'\n' {
            count.checked_add(1)
        } else {
            Some(count)
        }
    });
    let line_count = line_count.ok_or_else(|| malformed(0, "AYC line count overflows usize"))?;
    if line_count > MAX_AYC_INPUT_LINES {
        return Err(malformed(
            0,
            "AYC input exceeds the 8,000,000-line parser cap",
        ));
    }
    Ok(())
}

fn parse_record(
    text: &str,
    lines: &[&str],
    line: &mut usize,
    record: &str,
    state: &mut ParseState,
) -> Result<(), CertIoError> {
    let fields: Vec<&str> = record.split_whitespace().collect();
    match fields[0] {
        "%AYC" | "model" | "solver" | "verdict" | "evidence" | "unchecked" | "truncated"
        | "reason" => parse_metadata(&fields, record, line, state),
        "witness" | "farkas" | "optcert" | "tree" | "opttree" | "affine-aggregation"
        | "parity-gf2" | "sat-relu-rup" => parse_core_block(lines, line, state),
        "network-design-infeasibility"
        | "network-design-optimality"
        | "block-angular-optimality"
        | "single-machine-scheduling-optimality" => parse_route_block(lines, &fields, line, state),
        "single-row-dp"
        | "multi-row-bdd"
        | "open-domain-dp"
        | "open-domain-bdd"
        | "open-domain-hybrid-pb-lp"
        | "open-domain-hybrid-integer-lift"
        | "hybrid-pb-lp"
        | "hybrid-integer-lift" => parse_encoded_block(lines, line, state),
        "replay" => {
            let (claim, next) = parse_replay(lines, *line)?;
            state.certificate.replay.push(claim);
            *line = next;
            Ok(())
        }
        "%END" => parse_end(text, lines, &fields, line, state),
        other => Err(malformed(*line, &format!("unknown record `{other}`"))),
    }
}

fn parse_end(
    text: &str,
    lines: &[&str],
    fields: &[&str],
    line: &mut usize,
    state: &mut ParseState,
) -> Result<(), CertIoError> {
    let wanted = strip_sha(fields.get(1).copied().unwrap_or_default())
        .ok_or_else(|| malformed(*line, "malformed %END digest"))?;
    let mut body_len = 0usize;
    for body_line in &lines[..*line] {
        body_len = body_len
            .checked_add(body_line.len())
            .and_then(|length| length.checked_add(1))
            .ok_or_else(|| malformed(*line, "%END body length overflow"))?;
    }
    let body = &text[..body_len.min(text.len())];
    state.certificate.end_digest_ok = sha256_hex(body.as_bytes()) == wanted;
    *line += 1;
    Ok(())
}
