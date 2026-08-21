// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

pub(super) fn affine_bound_token(bound: &Option<BigRational>) -> String {
    bound.as_ref().map_or_else(|| "-".to_owned(), fmt_rat)
}

pub(super) const MAX_AFFINE_WIRE_BYTES: usize = 64 << 20;

pub(super) fn write_affine_line(
    output: &mut String,
    limit: usize,
    arguments: fmt::Arguments<'_>,
) -> Option<()> {
    let before = output.len();
    output.write_fmt(arguments).ok()?;
    output.write_char('\n').ok()?;
    if output.len() > limit {
        output.truncate(before);
        return None;
    }
    Some(())
}

pub(super) fn write_affine_multipliers(
    output: &mut String,
    limit: usize,
    multipliers: &[Multiplier],
) -> Option<()> {
    if multipliers.len() > MAX_AFFINE_PROOF_MULTIPLIERS {
        return None;
    }
    for multiplier in multipliers {
        match multiplier.fact {
            FactRef::RowBound { row, side } => write_affine_line(
                output,
                limit,
                format_args!(
                    "mult row {} {} {}",
                    row.index(),
                    side_token(side),
                    fmt_rat(&multiplier.coeff)
                ),
            )?,
            FactRef::ColBound { col, side } => write_affine_line(
                output,
                limit,
                format_args!(
                    "mult col {} {} {}",
                    col.index(),
                    side_token(side),
                    fmt_rat(&multiplier.coeff)
                ),
            )?,
        }
    }
    Some(())
}

pub(super) fn write_affine_tree(
    output: &mut String,
    limit: usize,
    proof: &MilpInfeasibilityCertificate,
) -> Option<()> {
    let mut stack = vec![(&proof.root, 0usize)];
    let mut nodes = 0usize;
    let mut multipliers = 0usize;
    while let Some((node, depth)) = stack.pop() {
        nodes = nodes.checked_add(1)?;
        if nodes > MAX_AFFINE_TREE_NODES || depth > MAX_AFFINE_TREE_DEPTH {
            return None;
        }
        match node {
            TreeNode::Split { col, cut, lo, hi } => {
                write_affine_line(
                    output,
                    limit,
                    format_args!("split {} {}", col.index(), fmt_rat(cut)),
                )?;
                let child_depth = depth.checked_add(1)?;
                stack.push((hi, child_depth));
                stack.push((lo, child_depth));
            }
            TreeNode::Leaf { farkas } => {
                multipliers = multipliers.checked_add(farkas.multipliers.len())?;
                if multipliers > MAX_AFFINE_PROOF_MULTIPLIERS {
                    return None;
                }
                write_affine_line(output, limit, format_args!("leaf"))?;
                write_affine_multipliers(output, limit, &farkas.multipliers)?;
                write_affine_line(output, limit, format_args!("endleaf"))?;
            }
        }
    }
    write_affine_line(output, limit, format_args!("endinner"))
}

pub(super) fn write_affine_primal(
    output: &mut String,
    limit: usize,
    name: &str,
    point: &[BigRational],
) -> Option<()> {
    if point.len() > MAX_ANALYSIS_COLS {
        return None;
    }
    write_affine_line(output, limit, format_args!("{name} values={}", point.len()))?;
    for (column, value) in point.iter().enumerate() {
        write_affine_line(
            output,
            limit,
            format_args!("point {column} {}", fmt_rat(value)),
        )?;
    }
    write_affine_line(output, limit, format_args!("end-{name}"))
}

pub(super) fn affine_aggregation_block(
    certificate: &AffineAggregationCertificate,
    byte_limit: usize,
) -> Option<String> {
    let analysis = &certificate.analysis;
    let caps = &analysis.caps;
    let limit = byte_limit.min(MAX_AFFINE_WIRE_BYTES);
    if analysis.bounds.len() != caps.source_cols
        || analysis.bounds.len() > MAX_ANALYSIS_COLS
        || caps.source_rows > MAX_ANALYSIS_ROWS
        || analysis.steps.len() > MAX_ELIMINATIONS
        || validate_certificate_payload_caps(certificate, caps.source_cols).is_err()
    {
        return None;
    }
    let mut s = String::new();
    write_affine_header(&mut s, limit, analysis)?;
    write_affine_analysis(&mut s, limit, analysis)?;
    write_affine_claim(&mut s, limit, certificate)?;
    write_affine_inner(&mut s, limit, &certificate.inner_proof)?;
    write_affine_line(&mut s, limit, format_args!("end-affine-aggregation"))?;
    Some(s)
}

fn write_affine_header(
    output: &mut String,
    limit: usize,
    analysis: &AffineAggregationAnalysis,
) -> Option<()> {
    let caps = &analysis.caps;
    write_affine_line(
        output,
        limit,
        format_args!(
            "affine-aggregation version={} source=sha256:{} reduced=sha256:{} bounds={} steps={} \
         source_cols={} source_rows={} input_nnz={} nnz_cap={} max_eliminations={} \
         max_row_terms={} max_total_terms={} max_recovery_terms={} max_rational_bits={} \
         analysis_rounds={} analysis_term_visits={}",
            caps.version,
            analysis.source_digest,
            analysis.reduced_digest,
            analysis.bounds.len(),
            analysis.steps.len(),
            caps.source_cols,
            caps.source_rows,
            caps.input_nnz,
            caps.nnz_cap,
            caps.max_eliminations,
            caps.max_row_terms,
            caps.max_total_terms,
            caps.max_recovery_terms,
            caps.max_rational_bits,
            caps.analysis_rounds,
            caps.analysis_term_visits,
        ),
    )
}

fn write_affine_analysis(
    output: &mut String,
    limit: usize,
    analysis: &AffineAggregationAnalysis,
) -> Option<()> {
    for (column, bound) in analysis.bounds.iter().enumerate() {
        write_affine_line(
            output,
            limit,
            format_args!(
                "analysis-bound {column} {} {}",
                affine_bound_token(&bound.lower),
                affine_bound_token(&bound.upper)
            ),
        )?;
    }
    let mut recovery_terms = 0usize;
    for recovery in analysis.steps.iter() {
        match recovery {
            AffineRecovery::Fixed { col, value } => {
                write_affine_line(
                    output,
                    limit,
                    format_args!("recover fixed {col} {}", fmt_rat(value)),
                )?;
            }
            AffineRecovery::Equality {
                row,
                col,
                constant,
                terms,
            } => {
                recovery_terms = recovery_terms.checked_add(terms.len())?;
                if terms.len() > MAX_ROW_TERMS || recovery_terms > MAX_RECOVERY_TERMS {
                    return None;
                }
                write_affine_line(
                    output,
                    limit,
                    format_args!(
                        "recover equality {row} {col} {} terms={}",
                        fmt_rat(constant),
                        terms.len()
                    ),
                )?;
                for (column, coefficient) in terms {
                    write_affine_line(
                        output,
                        limit,
                        format_args!("term {column} {}", fmt_rat(coefficient)),
                    )?;
                }
            }
        }
    }
    write_affine_line(
        output,
        limit,
        format_args!("objective-delta {}", fmt_rat(&analysis.objective_delta)),
    )
}

fn write_affine_claim(
    output: &mut String,
    limit: usize,
    certificate: &AffineAggregationCertificate,
) -> Option<()> {
    match &certificate.claim {
        AffineAggregationClaim::Feasible => {
            write_affine_line(output, limit, format_args!("claim feasible"))?;
        }
        AffineAggregationClaim::Optimal { value } => {
            write_affine_line(
                output,
                limit,
                format_args!("claim optimal value={}", fmt_rat(value)),
            )?;
        }
        AffineAggregationClaim::Infeasible => {
            write_affine_line(output, limit, format_args!("claim infeasible"))?;
        }
    }
    if let Some(point) = &certificate.reduced_primal {
        write_affine_primal(output, limit, "reduced-primal", point)?;
    }
    if let Some(point) = &certificate.source_primal {
        write_affine_primal(output, limit, "source-primal", point)?;
    }
    Some(())
}

fn write_affine_inner(
    output: &mut String,
    limit: usize,
    proof: &AffineAggregationInnerProof,
) -> Option<()> {
    match proof {
        AffineAggregationInnerProof::Unsupported => {
            write_affine_line(output, limit, format_args!("inner unsupported"))?;
        }
        AffineAggregationInnerProof::Farkas(proof) => {
            write_affine_line(
                output,
                limit,
                format_args!("inner farkas mults={}", proof.multipliers.len()),
            )?;
            write_affine_multipliers(output, limit, &proof.multipliers)?;
            write_affine_line(output, limit, format_args!("endinner"))?;
        }
        AffineAggregationInnerProof::Optimality(proof) => {
            if proof.objective.len() > MAX_ANALYSIS_COLS {
                return None;
            }
            write_affine_line(
                output,
                limit,
                format_args!(
                    "inner optimality sense={} bound={} objective={} mults={}",
                    sense_token(proof.sense),
                    fmt_rat(&proof.bound),
                    proof.objective.len(),
                    proof.multipliers.len()
                ),
            )?;
            for (column, coefficient) in &proof.objective {
                write_affine_line(
                    output,
                    limit,
                    format_args!("obj {column} {}", fmt_rat(coefficient)),
                )?;
            }
            write_affine_multipliers(output, limit, &proof.multipliers)?;
            write_affine_line(output, limit, format_args!("endinner"))?;
        }
        AffineAggregationInnerProof::InfeasibilityTree(proof) => {
            write_affine_line(output, limit, format_args!("inner tree"))?;
            write_affine_tree(output, limit, proof)?;
        }
    }
    Some(())
}
