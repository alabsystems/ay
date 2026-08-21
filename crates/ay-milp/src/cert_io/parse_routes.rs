// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

pub(super) fn parse_single_row_dp(
    lines: &[&str],
    start: usize,
) -> Result<(SingleRowDpInfeasibilityCertificate, usize), CertIoError> {
    let head: Vec<&str> = lines[start].split_whitespace().collect();
    let expected_bytes = kv_usize(&head, "json_bytes").ok_or(CertIoError::Malformed {
        line: start + 1,
        msg: "single-row-dp has no json_bytes=".into(),
    })?;
    let json_line = lines.get(start + 1).ok_or(CertIoError::Malformed {
        line: start + 1,
        msg: "single-row-dp JSON body is absent".into(),
    })?;
    if json_line.len() != expected_bytes {
        return Err(CertIoError::Malformed {
            line: start + 2,
            msg: format!(
                "single-row-dp JSON has {} bytes, header declares {expected_bytes}",
                json_line.len()
            ),
        });
    }
    if lines.get(start + 2).map(|line| line.trim()) != Some("end") {
        return Err(CertIoError::Malformed {
            line: start + 3,
            msg: "single-row-dp block not terminated".into(),
        });
    }
    let certificate = decode_single_row_dp_infeasibility_certificate_json(json_line.as_bytes())
        .map_err(|error| CertIoError::Malformed {
            line: start + 2,
            msg: format!("single-row-dp JSON rejected: {error}"),
        })?;
    Ok((certificate, start + 3))
}

pub(super) fn parse_multi_row_bdd(
    lines: &[&str],
    start: usize,
) -> Result<(MultiRowBddInfeasibilityCertificate, usize), CertIoError> {
    let head: Vec<&str> = lines[start].split_whitespace().collect();
    let expected_bytes = kv_usize(&head, "json_bytes").ok_or(CertIoError::Malformed {
        line: start + 1,
        msg: "multi-row-bdd has no json_bytes=".into(),
    })?;
    let json_line = lines.get(start + 1).ok_or(CertIoError::Malformed {
        line: start + 1,
        msg: "multi-row-bdd JSON body is absent".into(),
    })?;
    if json_line.len() != expected_bytes {
        return Err(CertIoError::Malformed {
            line: start + 2,
            msg: format!(
                "multi-row-bdd JSON has {} bytes, header declares {expected_bytes}",
                json_line.len()
            ),
        });
    }
    if lines.get(start + 2).map(|line| line.trim()) != Some("end") {
        return Err(CertIoError::Malformed {
            line: start + 3,
            msg: "multi-row-bdd block not terminated".into(),
        });
    }
    let certificate = decode_multi_row_bdd_infeasibility_certificate_json(json_line.as_bytes())
        .map_err(|error| CertIoError::Malformed {
            line: start + 2,
            msg: format!("multi-row-bdd JSON rejected: {error}"),
        })?;
    Ok((certificate, start + 3))
}

pub(super) fn parse_single_machine_scheduling_optimality(
    lines: &[&str],
    start: usize,
) -> Result<(SingleMachineSchedulingOptimalityCertificate, usize), CertIoError> {
    let malformed = |line: usize, msg: String| CertIoError::Malformed { line, msg };
    let head: Vec<&str> = lines[start].split_whitespace().collect();
    if kv(&head, "frame") != Some("model") {
        return Err(malformed(
            start + 1,
            "single-machine scheduling value must use frame=model".into(),
        ));
    }
    let value = kv(&head, "value").and_then(parse_rat).ok_or_else(|| {
        malformed(
            start + 1,
            "single-machine scheduling block has invalid value=".into(),
        )
    })?;
    let jobs = kv_usize(&head, "jobs").ok_or_else(|| {
        malformed(
            start + 1,
            "single-machine scheduling block has invalid jobs=".into(),
        )
    })?;
    let sequence_line = lines.get(start + 1).ok_or_else(|| {
        malformed(
            start + 2,
            "single-machine scheduling sequence is absent".into(),
        )
    })?;
    let fields: Vec<&str> = sequence_line.split_whitespace().collect();
    let expected_fields = jobs.checked_add(1).ok_or_else(|| {
        malformed(
            start + 1,
            "single-machine scheduling jobs= overflows the sequence length".into(),
        )
    })?;
    if fields.first().copied() != Some("sequence") || fields.len() != expected_fields {
        return Err(malformed(
            start + 2,
            format!(
                "single-machine scheduling sequence has {} jobs, header declares {jobs}",
                fields.len().saturating_sub(1)
            ),
        ));
    }
    let sequence = fields[1..]
        .iter()
        .map(|token| {
            token.parse::<u32>().map_err(|_| {
                malformed(
                    start + 2,
                    format!("single-machine scheduling column `{token}` is not a u32"),
                )
            })
        })
        .collect::<Result<Vec<_>, _>>()?;
    if lines.get(start + 2).map(|line| line.trim()) != Some("end") {
        return Err(malformed(
            start + 3,
            "single-machine scheduling block not terminated".into(),
        ));
    }
    Ok((
        crate::scheduling_route::optimality_from_parts(value, sequence),
        start + 3,
    ))
}

pub(super) fn parse_json_body<'a>(
    lines: &'a [&'a str],
    start: usize,
    label: &str,
) -> Result<(&'a str, usize), CertIoError> {
    let head: Vec<&str> = lines[start].split_whitespace().collect();
    let expected_bytes = kv_usize(&head, "json_bytes").ok_or(CertIoError::Malformed {
        line: start + 1,
        msg: format!("{label} has no json_bytes="),
    })?;
    let json_line = lines.get(start + 1).ok_or(CertIoError::Malformed {
        line: start + 1,
        msg: format!("{label} JSON body is absent"),
    })?;
    if json_line.len() != expected_bytes {
        return Err(CertIoError::Malformed {
            line: start + 2,
            msg: format!(
                "{label} JSON has {} bytes, header declares {expected_bytes}",
                json_line.len()
            ),
        });
    }
    if lines.get(start + 2).map(|line| line.trim()) != Some("end") {
        return Err(CertIoError::Malformed {
            line: start + 3,
            msg: format!("{label} block not terminated"),
        });
    }
    Ok((json_line, start + 3))
}

pub(super) fn parse_network_design_pattern_count(
    lines: &[&str],
    start: usize,
) -> Result<
    (
        crate::pattern_count_route::PatternCountOptimalityCertificate,
        usize,
    ),
    CertIoError,
> {
    // These are wire-parser allocation guards, kept at the exact classifier's
    // public envelope. Replay independently re-applies the production caps.
    const MAX_BLOCKS: usize = 16;
    const MAX_WIDTH: usize = 96;

    let head: Vec<&str> = lines[start].split_whitespace().collect();
    let bad = |line: usize, msg: &str| CertIoError::Malformed {
        line: line + 1,
        msg: msg.to_owned(),
    };
    let block_count = kv_usize(&head, "blocks")
        .filter(|count| (2..=MAX_BLOCKS).contains(count))
        .ok_or_else(|| bad(start, "network-design pattern count has invalid blocks="))?;
    let width = kv_usize(&head, "width")
        .filter(|width| (1..=MAX_WIDTH).contains(width))
        .ok_or_else(|| bad(start, "network-design pattern count has invalid width="))?;
    let pb_value = kv(&head, "pb_value")
        .and_then(|value| value.parse::<i128>().ok())
        .ok_or_else(|| bad(start, "network-design pattern count has invalid pb_value="))?;

    let mut blocks = Vec::with_capacity(block_count);
    let mut seen = BTreeSet::new();
    for block_index in 0..block_count {
        let line_index = start + 1 + block_index;
        let line = lines
            .get(line_index)
            .ok_or_else(|| bad(line_index, "network-design pattern block is absent"))?;
        let max_line_bytes = 5usize
            .checked_add(
                width
                    .checked_mul(11)
                    .ok_or_else(|| bad(line_index, "network-design pattern block is too wide"))?,
            )
            .ok_or_else(|| bad(line_index, "network-design pattern block is too wide"))?;
        if line.len() > max_line_bytes {
            return Err(bad(
                line_index,
                "network-design pattern block exceeds its bounded wire width",
            ));
        }
        let fields: Vec<&str> = line.split_whitespace().collect();
        if fields.first() != Some(&"block") || fields.len() != width + 1 {
            return Err(bad(
                line_index,
                "network-design pattern block has the wrong width",
            ));
        }
        let mut variables = Vec::with_capacity(width);
        for token in &fields[1..] {
            let variable = token
                .parse::<u32>()
                .ok()
                .filter(|&value| value != 0)
                .ok_or_else(|| {
                    bad(
                        line_index,
                        "network-design pattern block has an invalid PB variable",
                    )
                })?;
            if !seen.insert(variable) {
                return Err(bad(
                    line_index,
                    "network-design pattern block repeats a PB variable",
                ));
            }
            variables.push(variable);
        }
        blocks.push(variables);
    }
    let end = start + 1 + block_count;
    if lines.get(end).map(|line| line.trim()) != Some("end") {
        return Err(bad(
            end,
            "network-design pattern-count block not terminated",
        ));
    }
    Ok((
        crate::pattern_count_route::PatternCountOptimalityCertificate { blocks, pb_value },
        end + 1,
    ))
}

pub(super) fn parse_block_angular_optimality(
    lines: &[&str],
    start: usize,
) -> Result<(BlockAngularOptimalityCertificate, usize), CertIoError> {
    const MAX_MASTERS: usize = 64;
    const MAX_BLOCKS: usize = 128;

    let bad = |line: usize, msg: &str| CertIoError::Malformed {
        line: line + 1,
        msg: msg.to_owned(),
    };
    let header: Vec<&str> = lines[start].split_whitespace().collect();
    if kv(&header, "frame") != Some("model") {
        return Err(bad(
            start,
            "block-angular optimality value must use frame=model",
        ));
    }
    let value = parse_block_angular_rat(
        start,
        "block-angular optimum value",
        kv(&header, "value").ok_or_else(|| bad(start, "block-angular-optimality has no value="))?,
    )?;
    let master_count = kv_usize(&header, "masters")
        .filter(|count| *count <= MAX_MASTERS)
        .ok_or_else(|| bad(start, "block-angular master count exceeds format cap"))?;
    let block_count = kv_usize(&header, "blocks")
        .filter(|count| *count <= MAX_BLOCKS)
        .ok_or_else(|| bad(start, "block-angular block count exceeds format cap"))?;

    let mut line = start + 1;
    let multipliers = parse_block_angular_masters(lines, &mut line, master_count)?;
    let minimizers = parse_block_angular_minimizers(lines, &mut line, block_count)?;
    if lines.get(line).map(|value| value.trim()) != Some("end") {
        return Err(bad(line, "block-angular-optimality block has no end"));
    }
    Ok((
        crate::block_angular_route::certificate_from_parts(value, multipliers, minimizers),
        line + 1,
    ))
}

fn parse_block_angular_masters(
    lines: &[&str],
    line: &mut usize,
    count: usize,
) -> Result<Vec<(u32, BigRational)>, CertIoError> {
    let mut multipliers = Vec::with_capacity(count);
    for _ in 0..count {
        let fields: Vec<&str> = lines
            .get(*line)
            .ok_or_else(|| malformed(*line, "truncated block-angular master list"))?
            .split_whitespace()
            .collect();
        if fields.len() != 3 || fields[0] != "master" {
            return Err(malformed(*line, "malformed block-angular master record"));
        }
        let row = fields[1]
            .parse::<u32>()
            .map_err(|_| malformed(*line, "invalid block-angular master row"))?;
        let multiplier =
            parse_block_angular_rat(*line, "block-angular master multiplier", fields[2])?;
        multipliers.push((row, multiplier));
        *line += 1;
    }
    Ok(multipliers)
}

fn parse_block_angular_minimizers(
    lines: &[&str],
    line: &mut usize,
    count: usize,
) -> Result<Vec<crate::block_angular_route::CertifiedBlockPattern>, CertIoError> {
    const MAX_WIDTH: usize = 8;
    let mut minimizers = Vec::with_capacity(count);
    for _ in 0..count {
        let fields: Vec<&str> = lines
            .get(*line)
            .ok_or_else(|| malformed(*line, "truncated block-angular minimizer list"))?
            .split_whitespace()
            .collect();
        match fields.first().copied() {
            Some("source") => {
                let width = kv_usize(&fields, "width")
                    .filter(|width| (1..=MAX_WIDTH).contains(width))
                    .ok_or_else(|| malformed(*line, "invalid block-angular source width"))?;
                if fields.len() != 3 + 2 * width || fields[2 + width] != "exits" {
                    return Err(malformed(*line, "malformed block-angular source minimizer"));
                }
                let amounts = fields[2..2 + width]
                    .iter()
                    .map(|value| {
                        value
                            .parse::<i64>()
                            .map_err(|_| malformed(*line, "invalid source amount"))
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let exits = fields[3 + width..]
                    .iter()
                    .map(|value| {
                        value
                            .parse::<u8>()
                            .map_err(|_| malformed(*line, "invalid source exit"))
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                minimizers.push(crate::block_angular_route::source_pattern(amounts, exits));
            }
            Some("initial") => {
                if fields.len() != 2 {
                    return Err(malformed(
                        *line,
                        "malformed block-angular initial minimizer",
                    ));
                }
                let exit = kv(&fields, "exit")
                    .and_then(|value| value.parse::<u8>().ok())
                    .ok_or_else(|| malformed(*line, "invalid initial exit"))?;
                minimizers.push(crate::block_angular_route::certified_initial_pattern(exit));
            }
            _ => return Err(malformed(*line, "unknown block-angular minimizer record")),
        }
        *line += 1;
    }
    Ok(minimizers)
}

fn parse_block_angular_rat(
    line: usize,
    field: &str,
    token: &str,
) -> Result<BigRational, CertIoError> {
    parse_rat_bounded(token, crate::block_angular_route::MAX_RATIONAL_BITS).map_err(|error| {
        match error {
            BoundedRatParseError::Malformed => malformed(line, &format!("invalid {field}")),
            BoundedRatParseError::BitLimit => CertIoError::RationalBitLimit {
                line: line + 1,
                field: field.to_owned(),
                max_bits: crate::block_angular_route::MAX_RATIONAL_BITS,
            },
        }
    })
}

pub(super) fn parse_hybrid_pb_lp(
    lines: &[&str],
    start: usize,
) -> Result<(HybridPbLpInfeasibilityCertificate, usize), CertIoError> {
    let (json, next) = parse_json_body(lines, start, "hybrid-pb-lp")?;
    let certificate =
        decode_hybrid_pb_lp_infeasibility_certificate_json(json.as_bytes()).map_err(|error| {
            CertIoError::Malformed {
                line: start + 2,
                msg: format!("hybrid-pb-lp JSON rejected: {error}"),
            }
        })?;
    Ok((certificate, next))
}

pub(super) fn parse_hybrid_integer_lift(
    lines: &[&str],
    start: usize,
) -> Result<(HybridIntegerLiftInfeasibilityCertificate, usize), CertIoError> {
    let (json, next) = parse_json_body(lines, start, "hybrid-integer-lift")?;
    let certificate = decode_hybrid_integer_lift_infeasibility_certificate_json(json.as_bytes())
        .map_err(|error| CertIoError::Malformed {
            line: start + 2,
            msg: format!("hybrid-integer-lift JSON rejected: {error}"),
        })?;
    Ok((certificate, next))
}
