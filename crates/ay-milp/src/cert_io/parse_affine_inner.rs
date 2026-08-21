// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

pub(super) fn parse_affine_inner(
    lines: &[&str],
    cursor: &mut usize,
) -> Result<AffineAggregationInnerProof, CertIoError> {
    let inner_fields: Vec<&str> = lines
        .get(*cursor)
        .ok_or_else(|| affine_error(*cursor, "missing affine inner proof"))?
        .split_whitespace()
        .collect();
    let inner_proof = match inner_fields.get(1).copied() {
        Some("unsupported") if inner_fields.len() == 2 && inner_fields[0] == "inner" => {
            *cursor += 1;
            AffineAggregationInnerProof::Unsupported
        }
        Some("farkas") if inner_fields.len() == 3 && inner_fields[0] == "inner" => {
            let expected = kv_usize(&inner_fields, "mults").ok_or_else(|| {
                affine_error(*cursor, "affine Farkas proof has no multiplier count")
            })?;
            if expected > MAX_AFFINE_PROOF_MULTIPLIERS {
                return Err(affine_error(
                    *cursor,
                    "affine Farkas multiplier count exceeds hard cap",
                ));
            }
            let (multipliers, next) =
                parse_mults_mode(lines, *cursor + 1, "endinner", ProofParseMode::Affine)?;
            if multipliers.len() != expected {
                return Err(affine_error(
                    *cursor,
                    "affine Farkas multiplier count mismatch",
                ));
            }
            *cursor = next;
            AffineAggregationInnerProof::Farkas(FarkasCertificate { multipliers })
        }
        Some("optimality") if inner_fields.len() == 6 && inner_fields[0] == "inner" => {
            parse_affine_optimality(lines, cursor, &inner_fields)?
        }
        Some("tree") if inner_fields.len() == 2 && inner_fields[0] == "inner" => {
            let (root, next) =
                parse_tree_until(lines, *cursor + 1, "endinner", ProofParseMode::Affine)?;
            *cursor = next;
            AffineAggregationInnerProof::InfeasibilityTree(MilpInfeasibilityCertificate { root })
        }
        _ => return Err(affine_error(*cursor, "malformed affine inner proof header")),
    };
    Ok(inner_proof)
}

pub(super) fn parse_affine_optimality(
    lines: &[&str],
    cursor: &mut usize,
    fields: &[&str],
) -> Result<AffineAggregationInnerProof, CertIoError> {
    let sense = kv(fields, "sense")
        .and_then(parse_sense)
        .ok_or_else(|| affine_error(*cursor, "malformed affine optimality sense"))?;
    let bound = kv(fields, "bound")
        .and_then(parse_affine_rat)
        .ok_or_else(|| affine_error(*cursor, "malformed affine optimality bound"))?;
    let objective_count = kv_usize(fields, "objective")
        .ok_or_else(|| affine_error(*cursor, "affine optimality has no objective count"))?;
    let multiplier_count = kv_usize(fields, "mults")
        .ok_or_else(|| affine_error(*cursor, "affine optimality has no multiplier count"))?;
    if objective_count > lines.len()
        || objective_count > MAX_ANALYSIS_COLS
        || multiplier_count > MAX_AFFINE_PROOF_MULTIPLIERS
    {
        return Err(affine_error(
            *cursor,
            "affine objective count exceeds certificate lines",
        ));
    }
    *cursor += 1;
    let objective = parse_affine_objective(lines, cursor, objective_count)?;
    let (multipliers, next) = parse_mults_mode(lines, *cursor, "endinner", ProofParseMode::Affine)?;
    if multipliers.len() != multiplier_count {
        return Err(affine_error(
            *cursor,
            "affine optimality multiplier count mismatch",
        ));
    }
    *cursor = next;
    Ok(AffineAggregationInnerProof::Optimality(
        OptimalityCertificate {
            sense,
            objective,
            bound,
            multipliers,
        },
    ))
}

pub(super) fn parse_affine_objective(
    lines: &[&str],
    cursor: &mut usize,
    count: usize,
) -> Result<Vec<(u32, BigRational)>, CertIoError> {
    let mut objective = Vec::new();
    objective
        .try_reserve_exact(count)
        .map_err(|_| affine_error(*cursor, "affine objective allocation failed"))?;
    for _ in 0..count {
        let fields: Vec<&str> = lines
            .get(*cursor)
            .ok_or_else(|| affine_error(*cursor, "truncated affine objective"))?
            .split_whitespace()
            .collect();
        if fields.len() != 3 || fields[0] != "obj" {
            return Err(affine_error(*cursor, "malformed affine objective record"));
        }
        objective.push((
            fields[1]
                .parse()
                .map_err(|_| affine_error(*cursor, "malformed affine objective column"))?,
            parse_affine_rat(fields[2])
                .ok_or_else(|| affine_error(*cursor, "malformed affine objective coefficient"))?,
        ));
        *cursor += 1;
    }
    Ok(objective)
}
