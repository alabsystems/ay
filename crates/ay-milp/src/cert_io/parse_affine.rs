// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

pub(super) fn parse_affine_bound(token: &str) -> Option<Option<BigRational>> {
    if token == "-" {
        Some(None)
    } else {
        parse_affine_rat(token).map(Some)
    }
}

// ceil(log10(2) * MAX_RATIONAL_BITS), with log10(2) rounded upward.
pub(super) const MAX_AFFINE_DECIMAL_DIGITS: usize =
    ((MAX_RATIONAL_BITS as usize) * 30_103).div_ceil(100_000);
// Optional numerator sign, slash, numerator digits, and denominator digits.
pub(super) const MAX_AFFINE_RATIONAL_TOKEN_BYTES: usize = MAX_AFFINE_DECIMAL_DIGITS * 2 + 2;

pub(super) fn parse_affine_rat(token: &str) -> Option<BigRational> {
    if token.len() > MAX_AFFINE_RATIONAL_TOKEN_BYTES {
        return None;
    }
    let value = parse_rat(token)?;
    (value.numer().bits() <= MAX_RATIONAL_BITS && value.denom().bits() <= MAX_RATIONAL_BITS)
        .then_some(value)
}

pub(super) fn parse_affine_primal(
    lines: &[&str],
    start: usize,
    name: &str,
) -> Result<(Vec<BigRational>, usize), CertIoError> {
    let bad = |line: usize, msg: &str| CertIoError::Malformed {
        line: line + 1,
        msg: msg.to_owned(),
    };
    let head: Vec<&str> = lines
        .get(start)
        .ok_or_else(|| bad(start, "missing affine primal header"))?
        .split_whitespace()
        .collect();
    if head.first().copied() != Some(name) {
        return Err(bad(start, "wrong affine primal header"));
    }
    let values =
        kv_usize(&head, "values").ok_or_else(|| bad(start, "affine primal has no values count"))?;
    if values > lines.len() || values > MAX_ANALYSIS_COLS {
        return Err(bad(start, "affine primal count exceeds certificate lines"));
    }
    let mut point = Vec::new();
    point
        .try_reserve_exact(values)
        .map_err(|_| bad(start, "affine primal allocation failed"))?;
    let mut i = start + 1;
    for column in 0..values {
        let fields: Vec<&str> = lines
            .get(i)
            .ok_or_else(|| bad(i, "truncated affine primal"))?
            .split_whitespace()
            .collect();
        if fields.len() != 3
            || fields[0] != "point"
            || fields[1].parse::<usize>().ok() != Some(column)
        {
            return Err(bad(i, "malformed or out-of-order affine point"));
        }
        point.push(
            parse_affine_rat(fields[2]).ok_or_else(|| bad(i, "malformed affine point value"))?,
        );
        i += 1;
    }
    let terminator = format!("end-{name}");
    if lines.get(i).map(|line| line.trim()) != Some(terminator.as_str()) {
        return Err(bad(i, "affine primal block is not terminated"));
    }
    Ok((point, i + 1))
}

pub(super) fn parse_affine_aggregation(
    lines: &[&str],
    start: usize,
) -> Result<(AffineAggregationCertificate, usize), CertIoError> {
    let header = parse_affine_header(lines, start)?;
    let mut cursor = start + 1;
    let bounds = parse_affine_bounds(lines, &mut cursor, header.bounds_count, start)?;
    let steps = parse_affine_recoveries(lines, &mut cursor, header.steps_count, start)?;
    let objective_delta = parse_objective_delta(lines, &mut cursor)?;
    let claim = parse_affine_claim(lines, &mut cursor)?;
    let (reduced_primal, source_primal) = parse_affine_primals(lines, &mut cursor)?;
    let inner_proof = parse_affine_inner(lines, &mut cursor)?;
    if lines.get(cursor).map(|line| line.trim()) != Some("end-affine-aggregation") {
        return Err(affine_error(
            cursor,
            "affine-aggregation block is not terminated",
        ));
    }
    Ok((
        AffineAggregationCertificate {
            analysis: AffineAggregationAnalysis {
                source_digest: header.source_digest,
                reduced_digest: header.reduced_digest,
                bounds: Arc::from(bounds),
                steps: Arc::from(steps),
                objective_delta,
                caps: header.caps,
            },
            claim,
            inner_proof,
            reduced_primal,
            source_primal,
        },
        cursor + 1,
    ))
}

struct AffineHeader {
    source_digest: String,
    reduced_digest: String,
    bounds_count: usize,
    steps_count: usize,
    caps: AffineAggregationCaps,
}

fn parse_affine_header(lines: &[&str], start: usize) -> Result<AffineHeader, CertIoError> {
    let bad = |line: usize, msg: &str| CertIoError::Malformed {
        line: line + 1,
        msg: msg.to_owned(),
    };
    let head: Vec<&str> = lines
        .get(start)
        .ok_or_else(|| bad(start, "missing affine-aggregation header"))?
        .split_whitespace()
        .collect();
    if head.first() != Some(&"affine-aggregation") {
        return Err(bad(start, "wrong affine-aggregation header"));
    }
    let usize_field = |name: &str| {
        kv_usize(&head, name)
            .ok_or_else(|| bad(start, &format!("affine-aggregation has no {name}=")))
    };
    let version = usize_field("version")?;
    let version = u32::try_from(version).map_err(|_| bad(start, "affine version overflows u32"))?;
    let source_digest = kv(&head, "source")
        .and_then(strip_sha)
        .ok_or_else(|| bad(start, "malformed affine source digest"))?;
    let reduced_digest = kv(&head, "reduced")
        .and_then(strip_sha)
        .ok_or_else(|| bad(start, "malformed affine reduced digest"))?;
    let bounds_count = usize_field("bounds")?;
    let steps_count = usize_field("steps")?;
    if bounds_count > lines.len()
        || bounds_count > MAX_ANALYSIS_COLS
        || steps_count > lines.len()
        || steps_count > MAX_ELIMINATIONS
    {
        return Err(bad(
            start,
            "affine bounds/steps count exceeds certificate lines",
        ));
    }
    let max_rational_bits = kv(&head, "max_rational_bits")
        .and_then(|value| value.parse::<u64>().ok())
        .ok_or_else(|| bad(start, "malformed affine max_rational_bits"))?;
    let caps = AffineAggregationCaps {
        version,
        source_cols: usize_field("source_cols")?,
        source_rows: usize_field("source_rows")?,
        input_nnz: usize_field("input_nnz")?,
        nnz_cap: usize_field("nnz_cap")?,
        max_eliminations: usize_field("max_eliminations")?,
        max_row_terms: usize_field("max_row_terms")?,
        max_total_terms: usize_field("max_total_terms")?,
        max_recovery_terms: usize_field("max_recovery_terms")?,
        max_rational_bits,
        analysis_rounds: usize_field("analysis_rounds")?,
        analysis_term_visits: usize_field("analysis_term_visits")?,
    };
    if caps.source_cols != bounds_count
        || caps.source_cols > MAX_ANALYSIS_COLS
        || caps.source_rows > MAX_ANALYSIS_ROWS
    {
        return Err(bad(start, "affine source shape exceeds hard caps"));
    }
    Ok(AffineHeader {
        source_digest,
        reduced_digest,
        bounds_count,
        steps_count,
        caps,
    })
}

fn parse_affine_bounds(
    lines: &[&str],
    cursor: &mut usize,
    count: usize,
    start: usize,
) -> Result<Vec<AnalysisBound>, CertIoError> {
    let mut bounds = Vec::new();
    bounds
        .try_reserve_exact(count)
        .map_err(|_| affine_error(start, "affine bounds allocation failed"))?;
    for column in 0..count {
        let fields: Vec<&str> = lines
            .get(*cursor)
            .ok_or_else(|| affine_error(*cursor, "truncated affine analysis box"))?
            .split_whitespace()
            .collect();
        if fields.len() != 4
            || fields[0] != "analysis-bound"
            || fields[1].parse::<usize>().ok() != Some(column)
        {
            return Err(affine_error(
                *cursor,
                "malformed or out-of-order analysis-bound",
            ));
        }
        bounds.push(AnalysisBound {
            lower: parse_affine_bound(fields[2])
                .ok_or_else(|| affine_error(*cursor, "malformed affine lower bound"))?,
            upper: parse_affine_bound(fields[3])
                .ok_or_else(|| affine_error(*cursor, "malformed affine upper bound"))?,
        });
        *cursor += 1;
    }
    Ok(bounds)
}

fn parse_affine_recoveries(
    lines: &[&str],
    cursor: &mut usize,
    count: usize,
    start: usize,
) -> Result<Vec<AffineRecovery>, CertIoError> {
    let mut steps = Vec::new();
    steps
        .try_reserve_exact(count)
        .map_err(|_| affine_error(start, "affine steps allocation failed"))?;
    let mut recovery_terms = 0usize;
    for _ in 0..count {
        let fields: Vec<&str> = lines
            .get(*cursor)
            .ok_or_else(|| affine_error(*cursor, "truncated affine recovery"))?
            .split_whitespace()
            .collect();
        match fields.get(1).copied() {
            Some("fixed") if fields.len() == 4 && fields[0] == "recover" => {
                let col = fields[2]
                    .parse::<usize>()
                    .map_err(|_| affine_error(*cursor, "malformed fixed recovery column"))?;
                let value = parse_affine_rat(fields[3])
                    .ok_or_else(|| affine_error(*cursor, "malformed fixed recovery value"))?;
                steps.push(AffineRecovery::Fixed { col, value });
                *cursor += 1;
            }
            Some("equality") if fields.len() == 6 && fields[0] == "recover" => {
                let recovery =
                    parse_equality_recovery(lines, cursor, &fields, &mut recovery_terms)?;
                steps.push(recovery);
            }
            _ => return Err(affine_error(*cursor, "malformed affine recovery record")),
        }
    }
    Ok(steps)
}

fn parse_equality_recovery(
    lines: &[&str],
    cursor: &mut usize,
    fields: &[&str],
    recovery_terms: &mut usize,
) -> Result<AffineRecovery, CertIoError> {
    let row = fields[2]
        .parse::<usize>()
        .map_err(|_| affine_error(*cursor, "malformed equality recovery row"))?;
    let col = fields[3]
        .parse::<usize>()
        .map_err(|_| affine_error(*cursor, "malformed equality recovery column"))?;
    let constant = parse_affine_rat(fields[4])
        .ok_or_else(|| affine_error(*cursor, "malformed equality recovery constant"))?;
    let term_count = kv_usize(fields, "terms")
        .ok_or_else(|| affine_error(*cursor, "equality recovery has no terms count"))?;
    *recovery_terms = (*recovery_terms)
        .checked_add(term_count)
        .ok_or_else(|| affine_error(*cursor, "affine recovery term count overflow"))?;
    if term_count > lines.len()
        || term_count > MAX_ROW_TERMS
        || *recovery_terms > MAX_RECOVERY_TERMS
    {
        return Err(affine_error(
            *cursor,
            "affine term count exceeds certificate lines",
        ));
    }
    *cursor += 1;
    let terms = parse_affine_terms(lines, cursor, term_count)?;
    Ok(AffineRecovery::Equality {
        row,
        col,
        constant,
        terms,
    })
}

fn parse_affine_terms(
    lines: &[&str],
    cursor: &mut usize,
    count: usize,
) -> Result<Vec<(usize, BigRational)>, CertIoError> {
    let mut terms = Vec::new();
    terms
        .try_reserve_exact(count)
        .map_err(|_| affine_error(*cursor, "affine terms allocation failed"))?;
    for _ in 0..count {
        let fields: Vec<&str> = lines
            .get(*cursor)
            .ok_or_else(|| affine_error(*cursor, "truncated affine term list"))?
            .split_whitespace()
            .collect();
        if fields.len() != 3 || fields[0] != "term" {
            return Err(affine_error(*cursor, "malformed affine term"));
        }
        terms.push((
            fields[1]
                .parse()
                .map_err(|_| affine_error(*cursor, "malformed affine term column"))?,
            parse_affine_rat(fields[2])
                .ok_or_else(|| affine_error(*cursor, "malformed affine term coefficient"))?,
        ));
        *cursor += 1;
    }
    Ok(terms)
}

fn parse_objective_delta(lines: &[&str], cursor: &mut usize) -> Result<BigRational, CertIoError> {
    let delta_fields: Vec<&str> = lines
        .get(*cursor)
        .ok_or_else(|| affine_error(*cursor, "missing affine objective delta"))?
        .split_whitespace()
        .collect();
    if delta_fields.len() != 2 || delta_fields[0] != "objective-delta" {
        return Err(affine_error(*cursor, "malformed affine objective delta"));
    }
    let objective_delta = parse_affine_rat(delta_fields[1])
        .ok_or_else(|| affine_error(*cursor, "malformed affine objective delta value"))?;
    *cursor += 1;
    Ok(objective_delta)
}

fn parse_affine_claim(
    lines: &[&str],
    cursor: &mut usize,
) -> Result<AffineAggregationClaim, CertIoError> {
    let claim_fields: Vec<&str> = lines
        .get(*cursor)
        .ok_or_else(|| affine_error(*cursor, "missing affine claim"))?
        .split_whitespace()
        .collect();
    let claim = match claim_fields.as_slice() {
        ["claim", "feasible"] => AffineAggregationClaim::Feasible,
        ["claim", "infeasible"] => AffineAggregationClaim::Infeasible,
        ["claim", "optimal", value] => AffineAggregationClaim::Optimal {
            value: value
                .strip_prefix("value=")
                .and_then(parse_affine_rat)
                .ok_or_else(|| affine_error(*cursor, "malformed affine optimal value"))?,
        },
        _ => return Err(affine_error(*cursor, "malformed affine claim")),
    };
    *cursor += 1;
    Ok(claim)
}

fn parse_affine_primals(
    lines: &[&str],
    cursor: &mut usize,
) -> Result<(Option<Vec<BigRational>>, Option<Vec<BigRational>>), CertIoError> {
    let mut reduced_primal = None;
    let mut source_primal = None;
    loop {
        match lines
            .get(*cursor)
            .map(|line| line.split_whitespace().next())
        {
            Some(Some("reduced-primal")) if reduced_primal.is_none() => {
                let (point, next) = parse_affine_primal(lines, *cursor, "reduced-primal")?;
                reduced_primal = Some(point);
                *cursor = next;
            }
            Some(Some("source-primal")) if source_primal.is_none() => {
                let (point, next) = parse_affine_primal(lines, *cursor, "source-primal")?;
                source_primal = Some(point);
                *cursor = next;
            }
            _ => break,
        }
    }
    Ok((reduced_primal, source_primal))
}

pub(super) fn affine_error(line: usize, message: &str) -> CertIoError {
    CertIoError::Malformed {
        line: line + 1,
        msg: message.to_owned(),
    }
}
