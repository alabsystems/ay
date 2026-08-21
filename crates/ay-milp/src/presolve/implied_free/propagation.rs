// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

struct RowRange {
    minimum: BigRational,
    maximum: BigRational,
    minimum_infinite: usize,
    maximum_infinite: usize,
}

pub(super) fn threshold_free_propagation_box(
    source: &Model,
    caps: &AffineAggregationCaps,
) -> Result<Vec<AnalysisBound>, AffineAggregationCertificateError> {
    let planned = source
        .num_cols()
        .checked_mul(
            size_of::<AnalysisBound>()
                .checked_add(ESTIMATED_BYTES_PER_EXACT_VALUE * 2)
                .ok_or(AffineAggregationCertificateError::Caps)?,
        )
        .and_then(|bytes| bytes.checked_mul(2))
        .ok_or(AffineAggregationCertificateError::Caps)?;
    let guard =
        ResourceGuard::new(None, None, planned).ok_or(AffineAggregationCertificateError::Caps)?;
    let mut bounds = initial_bounds(source, &guard)?;
    let mut term_visits = 0usize;
    for _round in 0..caps.analysis_rounds {
        let mut changed = false;
        for row_index in 0..source.num_rows() {
            if row_index.is_multiple_of(128) && guard.stopped() {
                return Err(AffineAggregationCertificateError::Caps);
            }
            changed |= propagate_row(
                source,
                row_index,
                &mut bounds,
                &mut term_visits,
                caps,
                &guard,
            )?;
        }
        if !changed {
            return Ok(bounds);
        }
    }
    Err(AffineAggregationCertificateError::Caps)
}

fn initial_bounds(
    source: &Model,
    guard: &ResourceGuard,
) -> Result<Vec<AnalysisBound>, AffineAggregationCertificateError> {
    let mut bounds = Vec::new();
    bounds
        .try_reserve_exact(source.num_cols())
        .map_err(|_| AffineAggregationCertificateError::Caps)?;
    for column in 0..source.num_cols() {
        if column.is_multiple_of(256) && guard.stopped() {
            return Err(AffineAggregationCertificateError::Caps);
        }
        let (lower, upper) = source.col_bounds(Col(column as u32));
        bounds.push(AnalysisBound {
            lower: exact(lower),
            upper: exact(upper),
        });
    }
    Ok(bounds)
}

fn propagate_row(
    source: &Model,
    row_index: usize,
    bounds: &mut [AnalysisBound],
    term_visits: &mut usize,
    caps: &AffineAggregationCaps,
    guard: &ResourceGuard,
) -> Result<bool, AffineAggregationCertificateError> {
    let (coefficients, row_lower, row_upper) = source.row(Row(row_index as u32));
    let row_lower = exact(row_lower);
    let row_upper = exact(row_upper);
    if row_lower.is_none() && row_upper.is_none() {
        return Ok(false);
    }
    let range = row_range(coefficients, bounds, term_visits, caps, guard)?;
    if range.minimum_infinite > 1 && range.maximum_infinite > 1 {
        return Ok(false);
    }
    tighten_row(
        source,
        coefficients,
        row_lower.as_ref(),
        row_upper.as_ref(),
        &range,
        bounds,
        term_visits,
        caps,
        guard,
    )
}

fn row_range(
    coefficients: &[(u32, f64)],
    bounds: &[AnalysisBound],
    term_visits: &mut usize,
    caps: &AffineAggregationCaps,
    guard: &ResourceGuard,
) -> Result<RowRange, AffineAggregationCertificateError> {
    let mut range = RowRange {
        minimum: BigRational::zero(),
        maximum: BigRational::zero(),
        minimum_infinite: 0,
        maximum_infinite: 0,
    };
    for &(column, coefficient) in coefficients {
        let coefficient = visit_coefficient(coefficient, term_visits, caps, guard)?;
        let column = column as usize;
        let (at_minimum, at_maximum) = if coefficient.is_positive() {
            (&bounds[column].lower, &bounds[column].upper)
        } else {
            (&bounds[column].upper, &bounds[column].lower)
        };
        accumulate_range(
            &mut range.minimum,
            &mut range.minimum_infinite,
            &coefficient,
            at_minimum,
        )?;
        accumulate_range(
            &mut range.maximum,
            &mut range.maximum_infinite,
            &coefficient,
            at_maximum,
        )?;
    }
    Ok(range)
}

fn accumulate_range(
    total: &mut BigRational,
    infinite: &mut usize,
    coefficient: &BigRational,
    bound: &Option<BigRational>,
) -> Result<(), AffineAggregationCertificateError> {
    if let Some(bound) = bound {
        *total += coefficient * bound;
        if !rational_fits(total) {
            return Err(AffineAggregationCertificateError::Caps);
        }
    } else {
        *infinite += 1;
    }
    Ok(())
}

fn tighten_row(
    source: &Model,
    coefficients: &[(u32, f64)],
    row_lower: Option<&BigRational>,
    row_upper: Option<&BigRational>,
    range: &RowRange,
    bounds: &mut [AnalysisBound],
    term_visits: &mut usize,
    caps: &AffineAggregationCaps,
    guard: &ResourceGuard,
) -> Result<bool, AffineAggregationCertificateError> {
    let mut changed = false;
    for &(column, coefficient) in coefficients {
        let coefficient = visit_coefficient(coefficient, term_visits, caps, guard)?;
        if coefficient.is_zero() {
            continue;
        }
        let column = column as usize;
        let (at_minimum, at_maximum) = if coefficient.is_positive() {
            (bounds[column].lower.clone(), bounds[column].upper.clone())
        } else {
            (bounds[column].upper.clone(), bounds[column].lower.clone())
        };
        let rest_minimum = remove_term(
            range.minimum_infinite,
            &range.minimum,
            &coefficient,
            at_minimum,
        );
        let rest_maximum = remove_term(
            range.maximum_infinite,
            &range.maximum,
            &coefficient,
            at_maximum,
        );
        let integral = source.col_kind(Col(column as u32)).is_integral();
        if let (Some(upper), Some(rest)) = (row_upper, rest_minimum) {
            changed |= tighten_analysis_bound(
                &mut bounds[column],
                (upper - rest) / &coefficient,
                coefficient.is_negative(),
                integral,
            )?;
        }
        if let (Some(lower), Some(rest)) = (row_lower, rest_maximum) {
            changed |= tighten_analysis_bound(
                &mut bounds[column],
                (lower - rest) / &coefficient,
                coefficient.is_positive(),
                integral,
            )?;
        }
        if bounds[column]
            .lower
            .as_ref()
            .zip(bounds[column].upper.as_ref())
            .is_some_and(|(lower, upper)| lower > upper)
        {
            return Err(AffineAggregationCertificateError::AnalysisBox);
        }
    }
    Ok(changed)
}

fn remove_term(
    infinite: usize,
    total: &BigRational,
    coefficient: &BigRational,
    bound: Option<BigRational>,
) -> Option<BigRational> {
    match (infinite, bound) {
        (0, Some(bound)) => Some(total - coefficient * bound),
        (1, None) => Some(total.clone()),
        _ => None,
    }
}

fn visit_coefficient(
    coefficient: f64,
    term_visits: &mut usize,
    caps: &AffineAggregationCaps,
    guard: &ResourceGuard,
) -> Result<BigRational, AffineAggregationCertificateError> {
    *term_visits = (*term_visits)
        .checked_add(1)
        .ok_or(AffineAggregationCertificateError::Caps)?;
    if *term_visits > caps.analysis_term_visits
        || ((*term_visits).is_multiple_of(1_024) && guard.stopped())
    {
        return Err(AffineAggregationCertificateError::Caps);
    }
    exact(coefficient)
        .filter(rational_fits)
        .ok_or(AffineAggregationCertificateError::AnalysisBox)
}
