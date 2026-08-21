// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

struct RupHeader {
    format: u32,
    model_digest: [u8; 32],
    cnf_digest: [u8; 32],
    num_vars: usize,
    original_count: usize,
    step_count: usize,
    derived_literals: usize,
    hints: usize,
    empty_clause_id: u64,
}

struct RupBody {
    derived: Vec<RupStep>,
    known_ids: Vec<u64>,
    derived_literals: usize,
    hints: usize,
}

pub(super) fn parse_sat_relu_rup(
    lines: &[&str],
    start: usize,
) -> Result<(SatReluInfeasibilityCertificate, usize), CertIoError> {
    let header = parse_rup_header(lines, start)?;
    let body_end = validate_rup_extent(lines, start, header.step_count)?;
    let mut cursor = start + 1;
    let mut body = RupBody {
        derived: Vec::new(),
        known_ids: Vec::new(),
        derived_literals: 0,
        hints: 0,
    };
    for _ in 0..header.step_count {
        parse_rup_step(lines, cursor, &header, &mut body)?;
        cursor += 1;
    }
    if body.derived_literals != header.derived_literals || body.hints != header.hints {
        return Err(rup_error(
            start,
            "sat-relu-rup aggregate counts do not match the body",
        ));
    }
    if lines.get(cursor).map(|line| line.trim()) != Some("end") {
        return Err(rup_error(cursor, "sat-relu-rup block not terminated"));
    }
    let Some(last) = body.derived.last() else {
        return Err(rup_error(start, "sat-relu-rup has no derived steps"));
    };
    if last.id != header.empty_clause_id || !last.clause.is_empty() {
        return Err(rup_error(
            cursor,
            "sat-relu-rup final step is not the named empty clause",
        ));
    }
    Ok((
        SatReluInfeasibilityCertificate::from_wire_parts(
            header.format,
            header.model_digest,
            header.cnf_digest,
            header.num_vars,
            header.original_count,
            body.derived,
            header.empty_clause_id,
        ),
        body_end + 1,
    ))
}

fn parse_rup_header(lines: &[&str], start: usize) -> Result<RupHeader, CertIoError> {
    if lines[start].len() > 4096 {
        return Err(rup_error(start, "sat-relu-rup header exceeds 4096 bytes"));
    }
    let fields: Vec<&str> = lines[start].split_whitespace().collect();
    let header = RupHeader {
        format: kv(&fields, "format")
            .and_then(|token| token.parse().ok())
            .ok_or_else(|| rup_error(start, "sat-relu-rup has no valid format="))?,
        model_digest: kv(&fields, "model")
            .and_then(parse_digest32)
            .ok_or_else(|| rup_error(start, "sat-relu-rup has no canonical model digest"))?,
        cnf_digest: kv(&fields, "cnf")
            .and_then(parse_digest32)
            .ok_or_else(|| rup_error(start, "sat-relu-rup has no canonical CNF digest"))?,
        num_vars: required_count(&fields, "vars", start)?,
        original_count: required_count(&fields, "originals", start)?,
        step_count: required_count(&fields, "steps", start)?,
        derived_literals: required_count(&fields, "derived_lits", start)?,
        hints: required_count(&fields, "hints", start)?,
        empty_clause_id: kv(&fields, "empty")
            .and_then(|token| token.parse().ok())
            .ok_or_else(|| rup_error(start, "sat-relu-rup has no valid empty="))?,
    };
    if header.format != 1
        || header.num_vars > MAX_SAT_RELU_RUP_VARS
        || header.original_count > MAX_SAT_RELU_RUP_ORIGINALS
        || header.step_count > MAX_SAT_RELU_RUP_STEPS
        || header.derived_literals > MAX_SAT_RELU_RUP_LITERALS
        || header.hints > MAX_SAT_RELU_RUP_HINTS
        || header.empty_clause_id == 0
        || header.empty_clause_id > u64::from(u32::MAX)
    {
        return Err(rup_error(
            start,
            "sat-relu-rup header exceeds parser resource limits",
        ));
    }
    Ok(header)
}

fn required_count(fields: &[&str], name: &str, line: usize) -> Result<usize, CertIoError> {
    kv_usize(fields, name).ok_or_else(|| rup_error(line, &format!("sat-relu-rup has no {name}=")))
}

fn validate_rup_extent(
    lines: &[&str],
    start: usize,
    step_count: usize,
) -> Result<usize, CertIoError> {
    let body_end = start
        .checked_add(step_count)
        .and_then(|value| value.checked_add(1))
        .ok_or_else(|| rup_error(start, "sat-relu-rup line count overflows"))?;
    if body_end >= lines.len() {
        return Err(rup_error(start, "sat-relu-rup body is truncated"));
    }
    let mut block_bytes = 0usize;
    for (offset, line) in lines[start..=body_end].iter().enumerate() {
        if line.len() > MAX_SAT_RELU_RUP_BYTES / 2 {
            return Err(rup_error(
                start + offset,
                "sat-relu-rup record exceeds the per-line byte cap",
            ));
        }
        block_bytes = block_bytes
            .checked_add(line.len().saturating_add(1))
            .ok_or_else(|| rup_error(start, "sat-relu-rup byte count overflows"))?;
        if block_bytes > MAX_SAT_RELU_RUP_BYTES {
            return Err(rup_error(start, "sat-relu-rup block exceeds 64 MiB"));
        }
    }
    Ok(body_end)
}

fn parse_rup_step(
    lines: &[&str],
    line: usize,
    header: &RupHeader,
    body: &mut RupBody,
) -> Result<(), CertIoError> {
    let record = lines
        .get(line)
        .ok_or_else(|| rup_error(line, "sat-relu-rup steps are truncated"))?;
    let mut fields = record.split_whitespace();
    if fields.next() != Some("step") {
        return Err(rup_error(line, "expected sat-relu-rup step record"));
    }
    let id = parse_step_id(&mut fields, line, header, &body.known_ids)?;
    let literal_count = parse_item_count(&mut fields, "lits", line)?;
    let clause = parse_step_literals(&mut fields, literal_count, header.num_vars, line)?;
    let hint_count = parse_item_count(&mut fields, "hints", line)?;
    update_rup_totals(body, literal_count, hint_count, header, line)?;
    let rup_hints = parse_step_hints(
        &mut fields,
        hint_count,
        id,
        header.original_count,
        &body.known_ids,
        line,
    )?;
    if fields.next().is_some() {
        return Err(rup_error(line, "sat-relu-rup step has trailing tokens"));
    }
    push_parsed_value(
        &mut body.derived,
        RupStep {
            id,
            clause,
            rup_hints,
        },
        line + 1,
        "derived steps",
    )?;
    push_parsed_value(&mut body.known_ids, id, line + 1, "derived IDs")
}

fn parse_step_id(
    fields: &mut std::str::SplitWhitespace<'_>,
    line: usize,
    header: &RupHeader,
    known_ids: &[u64],
) -> Result<u64, CertIoError> {
    let id = fields
        .next()
        .and_then(|token| token.parse::<u64>().ok())
        .ok_or_else(|| rup_error(line, "sat-relu-rup step has invalid id"))?;
    if id <= header.original_count as u64
        || id > u64::from(u32::MAX)
        || known_ids.last().is_some_and(|previous| *previous >= id)
    {
        return Err(rup_error(
            line,
            "sat-relu-rup step id is not a positive monotone derived id",
        ));
    }
    Ok(id)
}

fn parse_item_count(
    fields: &mut std::str::SplitWhitespace<'_>,
    name: &str,
    line: usize,
) -> Result<usize, CertIoError> {
    let count = fields
        .next()
        .and_then(|token| token.strip_prefix(name))
        .and_then(|token| token.strip_prefix('='))
        .and_then(|token| token.parse().ok())
        .ok_or_else(|| rup_error(line, &format!("sat-relu-rup step has invalid {name}=")))?;
    if count > MAX_SAT_RELU_RUP_ITEMS_PER_STEP {
        return Err(rup_error(
            line,
            &format!("sat-relu-rup step has too many {name}"),
        ));
    }
    Ok(count)
}

fn parse_step_literals(
    fields: &mut std::str::SplitWhitespace<'_>,
    count: usize,
    num_vars: usize,
    line: usize,
) -> Result<Vec<Literal>, CertIoError> {
    let mut clause = Vec::new();
    for _ in 0..count {
        let token = fields
            .next()
            .ok_or_else(|| rup_error(line, "sat-relu-rup step literals are truncated"))?;
        let literal = parse_resolution_literal(token, num_vars, line + 1)?;
        push_parsed_value(&mut clause, literal, line + 1, "derived clause")?;
    }
    Ok(clause)
}

fn update_rup_totals(
    body: &mut RupBody,
    literals: usize,
    hints: usize,
    header: &RupHeader,
    line: usize,
) -> Result<(), CertIoError> {
    body.derived_literals = body
        .derived_literals
        .checked_add(literals)
        .ok_or_else(|| rup_error(line, "sat-relu-rup derived literal count overflows"))?;
    body.hints = body
        .hints
        .checked_add(hints)
        .ok_or_else(|| rup_error(line, "sat-relu-rup hint count overflows"))?;
    if body.derived_literals > header.derived_literals || body.hints > header.hints {
        return Err(rup_error(
            line,
            "sat-relu-rup carries more proof data than declared",
        ));
    }
    Ok(())
}

fn parse_step_hints(
    fields: &mut std::str::SplitWhitespace<'_>,
    count: usize,
    id: u64,
    original_count: usize,
    known_ids: &[u64],
    line: usize,
) -> Result<Vec<u64>, CertIoError> {
    let mut hints = Vec::new();
    for _ in 0..count {
        let hint = fields
            .next()
            .and_then(|token| token.parse::<u64>().ok())
            .ok_or_else(|| rup_error(line, "sat-relu-rup step has an invalid hint id"))?;
        let known = hint > 0
            && hint < id
            && (hint <= original_count as u64 || known_ids.binary_search(&hint).is_ok());
        if !known || hint > u64::from(u32::MAX) {
            return Err(rup_error(
                line,
                "sat-relu-rup step references an unknown or forward hint",
            ));
        }
        push_parsed_value(&mut hints, hint, line + 1, "RUP hints")?;
    }
    Ok(hints)
}

fn rup_error(line: usize, message: &str) -> CertIoError {
    CertIoError::Malformed {
        line: line + 1,
        msg: message.to_owned(),
    }
}

pub(super) fn parse_witness(
    lines: &[&str],
    start: usize,
) -> Result<(Vec<BigRational>, usize), CertIoError> {
    let head: Vec<&str> = lines[start].split_whitespace().collect();
    let n = kv_usize(&head, "cols").ok_or(CertIoError::Malformed {
        line: start + 1,
        msg: "witness has no cols=".into(),
    })?;
    let mut vals = Vec::with_capacity(n);
    let mut i = start + 1;
    while i < lines.len() {
        let l = lines[i].trim();
        if l == "end" {
            i += 1;
            break;
        }
        let f: Vec<&str> = l.split_whitespace().collect();
        // `x <index> <name> <value>` — the index is checked against position so
        // a reordered or dropped record cannot silently shift the point.
        if f.len() != 4 || f[0] != "x" {
            return Err(CertIoError::Malformed {
                line: i + 1,
                msg: "malformed witness record".into(),
            });
        }
        if f[1].parse::<usize>().ok() != Some(vals.len()) {
            return Err(CertIoError::Malformed {
                line: i + 1,
                msg: "witness column index out of order".into(),
            });
        }
        vals.push(parse_rat(f[3]).ok_or(CertIoError::Malformed {
            line: i + 1,
            msg: "malformed witness value".into(),
        })?);
        i += 1;
    }
    if vals.len() != n {
        return Err(CertIoError::Malformed {
            line: start + 1,
            msg: format!("witness declares {n} columns, carries {}", vals.len()),
        });
    }
    Ok((vals, i))
}
