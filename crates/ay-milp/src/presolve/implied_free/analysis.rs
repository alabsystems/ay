// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

pub(super) fn validate_analysis_caps(
    source: &Model,
    analysis: &AffineAggregationAnalysis,
) -> Result<(), AffineAggregationCertificateError> {
    let caps = &analysis.caps;
    let mut input_nnz = 0usize;
    let mut max_row_nnz = 0usize;
    for row in 0..source.num_rows() {
        let len = source.row(Row(row as u32)).0.len();
        input_nnz = input_nnz
            .checked_add(len)
            .ok_or(AffineAggregationCertificateError::Caps)?;
        max_row_nnz = max_row_nnz.max(len);
    }
    let expected_nnz_cap = input_nnz
        .checked_add(input_nnz / 2 + 1_024)
        .ok_or(AffineAggregationCertificateError::Caps)?
        .min(MAX_TOTAL_TERMS);
    let recovery_terms = analysis.steps.iter().try_fold(0usize, |total, step| {
        total.checked_add(match step {
            AffineRecovery::Fixed { .. } => 0,
            AffineRecovery::Equality { terms, .. } => terms.len(),
        })
    });
    if caps.version != ANALYSIS_VERSION
        || caps.source_cols != source.num_cols()
        || caps.source_rows != source.num_rows()
        || caps.input_nnz != input_nnz
        || caps.nnz_cap != expected_nnz_cap
        || caps.max_eliminations != MAX_ELIMINATIONS
        || caps.max_row_terms != MAX_ROW_TERMS
        || caps.max_total_terms != MAX_TOTAL_TERMS
        || caps.max_recovery_terms != MAX_RECOVERY_TERMS
        || caps.max_rational_bits != MAX_RATIONAL_BITS
        || caps.analysis_rounds != MAX_ANALYSIS_ROUNDS
        || caps.analysis_term_visits != MAX_ANALYSIS_TERM_VISITS
        || source.num_cols() > MAX_ANALYSIS_COLS
        || source.num_rows() > MAX_ANALYSIS_ROWS
        || input_nnz > MAX_TOTAL_TERMS
        || max_row_nnz > MAX_ROW_TERMS
        || analysis.bounds.len() != source.num_cols()
        || analysis.steps.is_empty()
        || analysis.steps.len() > MAX_ELIMINATIONS
        || recovery_terms.is_none_or(|terms| terms > expected_nnz_cap.min(MAX_RECOVERY_TERMS))
    {
        return Err(AffineAggregationCertificateError::Caps);
    }
    Ok(())
}

pub(super) fn tighten_analysis_bound(
    bounds: &mut AnalysisBound,
    candidate: BigRational,
    lower_side: bool,
    integral: bool,
) -> Result<bool, AffineAggregationCertificateError> {
    if !rational_fits(&candidate) {
        return Err(AffineAggregationCertificateError::Caps);
    }
    let candidate = if integral {
        let integer = if lower_side {
            candidate.numer().div_ceil(candidate.denom())
        } else {
            candidate.numer().div_floor(candidate.denom())
        };
        BigRational::from_integer(integer)
    } else {
        candidate
    };
    let side = if lower_side {
        &mut bounds.lower
    } else {
        &mut bounds.upper
    };
    let improves = side.as_ref().is_none_or(|current| {
        if lower_side {
            &candidate > current
        } else {
            &candidate < current
        }
    });
    if improves {
        *side = Some(candidate);
    }
    Ok(improves)
}

pub(super) fn validate_analysis_box(
    source: &Model,
    closure: &[AnalysisBound],
    claimed: &[AnalysisBound],
) -> Result<(), AffineAggregationCertificateError> {
    let column_count = source.num_cols();
    if closure.len() != column_count || claimed.len() != column_count {
        return Err(AffineAggregationCertificateError::AnalysisBox);
    }
    for column in 0..column_count {
        let (source_lower, source_upper) = source.col_bounds(Col(column as u32));
        let source_lower = exact(source_lower);
        let source_upper = exact(source_upper);
        let claim = &claimed[column];
        if claim
            .lower
            .as_ref()
            .zip(claim.upper.as_ref())
            .is_some_and(|(lower, upper)| lower > upper)
            || claim
                .lower
                .as_ref()
                .is_some_and(|value| !rational_fits(value) || exact_f64(value).is_none())
            || claim
                .upper
                .as_ref()
                .is_some_and(|value| !rational_fits(value) || exact_f64(value).is_none())
        {
            return Err(AffineAggregationCertificateError::AnalysisBox);
        }
        let lower_inside_source = match (&source_lower, &claim.lower) {
            (Some(source), Some(claim)) => claim >= source,
            (None, _) => true,
            (Some(_), None) => false,
        };
        let upper_inside_source = match (&source_upper, &claim.upper) {
            (Some(source), Some(claim)) => claim <= source,
            (None, _) => true,
            (Some(_), None) => false,
        };
        let lower_licensed = claim.lower == source_lower
            || match (&closure[column].lower, &claim.lower) {
                (Some(derived), Some(claim)) => derived >= claim,
                _ => false,
            };
        let upper_licensed = claim.upper == source_upper
            || match (&closure[column].upper, &claim.upper) {
                (Some(derived), Some(claim)) => derived <= claim,
                _ => false,
            };
        if !lower_inside_source || !upper_inside_source || !lower_licensed || !upper_licensed {
            return Err(AffineAggregationCertificateError::AnalysisBox);
        }
    }
    Ok(())
}
