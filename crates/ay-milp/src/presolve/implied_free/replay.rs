// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

pub(super) fn replay_analysis(
    source: &Model,
    analysis: &AffineAggregationAnalysis,
) -> Result<(Model, AffineAggregationPostsolve), AffineAggregationCertificateError> {
    let caps = &analysis.caps;
    let guard = replay_guard(source, caps)?;
    let analysis_model = analysis_model(source, &analysis.bounds)?;
    let mut work = replay_work(source, &analysis.bounds, caps, &guard)?;
    replay_steps(&mut work, &analysis.steps, &guard)?;
    if !material_reduction(source.num_cols(), work.recover.len()) {
        return Err(AffineAggregationCertificateError::Replay);
    }
    if work.const_delta != analysis.objective_delta {
        return Err(AffineAggregationCertificateError::ObjectiveDelta);
    }
    emit(
        source,
        &analysis_model,
        work,
        analysis.bounds.to_vec(),
        caps.clone(),
        &guard,
    )
    .ok_or(AffineAggregationCertificateError::Replay)
}

fn replay_guard(
    source: &Model,
    caps: &AffineAggregationCaps,
) -> Result<ResourceGuard, AffineAggregationCertificateError> {
    let max_row_nnz = (0..source.num_rows())
        .map(|row| source.row(Row(row as u32)).0.len())
        .max()
        .unwrap_or(0);
    let planned = planned_transform_bytes(
        source.num_cols(),
        source.num_rows(),
        caps.input_nnz,
        caps.nnz_cap,
        max_row_nnz,
    )
    .ok_or(AffineAggregationCertificateError::Caps)?;
    ResourceGuard::new(None, None, planned).ok_or(AffineAggregationCertificateError::Caps)
}

fn analysis_model(
    source: &Model,
    bounds: &[AnalysisBound],
) -> Result<Model, AffineAggregationCertificateError> {
    let mut analysis_model = source.clone();
    for (column, bounds) in bounds.iter().enumerate() {
        let lower =
            bound_f64(&bounds.lower, true).ok_or(AffineAggregationCertificateError::AnalysisBox)?;
        let upper = bound_f64(&bounds.upper, false)
            .ok_or(AffineAggregationCertificateError::AnalysisBox)?;
        analysis_model.set_col_bounds(Col(column as u32), lower, upper);
    }
    Ok(analysis_model)
}

fn replay_work(
    source: &Model,
    bounds: &[AnalysisBound],
    caps: &AffineAggregationCaps,
    guard: &ResourceGuard,
) -> Result<Work, AffineAggregationCertificateError> {
    let (cols, objective) = replay_columns(source, bounds, guard)?;
    let rows = replay_rows(source, caps.input_nnz, guard)?;
    Ok(Work {
        cols,
        rows,
        objective,
        input_nnz: caps.input_nnz,
        active_nnz: caps.input_nnz,
        nnz_cap: caps.nnz_cap,
        recovery_term_cap: caps.nnz_cap.min(MAX_RECOVERY_TERMS),
        const_delta: BigRational::zero(),
        recover: Vec::new(),
        recovery_terms: 0,
    })
}

fn replay_columns(
    source: &Model,
    bounds: &[AnalysisBound],
    guard: &ResourceGuard,
) -> Result<(Vec<WorkCol>, Vec<BigRational>), AffineAggregationCertificateError> {
    let mut cols = Vec::new();
    let mut objective = Vec::new();
    cols.try_reserve_exact(source.num_cols())
        .map_err(|_| AffineAggregationCertificateError::Caps)?;
    objective
        .try_reserve_exact(source.num_cols())
        .map_err(|_| AffineAggregationCertificateError::Caps)?;
    for (column, bounds) in bounds.iter().enumerate() {
        if column.is_multiple_of(256) && guard.stopped() {
            return Err(AffineAggregationCertificateError::Caps);
        }
        cols.push(WorkCol {
            active: true,
            lower: bounds.lower.clone(),
            upper: bounds.upper.clone(),
            kind: source.col_kind(Col(column as u32)),
        });
        objective.push(
            exact(source.obj_coeff(Col(column as u32)))
                .ok_or(AffineAggregationCertificateError::Replay)?,
        );
    }
    Ok((cols, objective))
}

fn replay_rows(
    source: &Model,
    expected_terms: usize,
    guard: &ResourceGuard,
) -> Result<Vec<WorkRow>, AffineAggregationCertificateError> {
    let mut rows = Vec::new();
    rows.try_reserve_exact(source.num_rows())
        .map_err(|_| AffineAggregationCertificateError::Caps)?;
    let mut terms_seen = 0usize;
    for row_index in 0..source.num_rows() {
        if row_index.is_multiple_of(128) && guard.stopped() {
            return Err(AffineAggregationCertificateError::Caps);
        }
        let (coefficients, lower, upper) = source.row(Row(row_index as u32));
        let mut exact_coefficients = Vec::new();
        exact_coefficients
            .try_reserve_exact(coefficients.len())
            .map_err(|_| AffineAggregationCertificateError::Caps)?;
        for &(column, coefficient) in coefficients {
            terms_seen = terms_seen
                .checked_add(1)
                .ok_or(AffineAggregationCertificateError::Caps)?;
            if terms_seen.is_multiple_of(1_024) && guard.stopped() {
                return Err(AffineAggregationCertificateError::Caps);
            }
            let coefficient = exact(coefficient)
                .filter(rational_fits)
                .ok_or(AffineAggregationCertificateError::Replay)?;
            if !coefficient.is_zero() {
                exact_coefficients.push((column as usize, coefficient));
            }
        }
        rows.push(WorkRow {
            active: true,
            lower: exact(lower),
            upper: exact(upper),
            coeffs: exact_coefficients,
        });
    }
    if terms_seen != expected_terms {
        return Err(AffineAggregationCertificateError::Caps);
    }
    Ok(rows)
}

fn replay_steps(
    work: &mut Work,
    steps: &[AffineRecovery],
    guard: &ResourceGuard,
) -> Result<(), AffineAggregationCertificateError> {
    project_fixed_columns(work, guard).ok_or(AffineAggregationCertificateError::Replay)?;
    let fixed_count = work.recover.len();
    if fixed_count > steps.len()
        || work.recover.as_slice() != &steps[..fixed_count]
        || steps[fixed_count..]
            .iter()
            .any(|step| matches!(step, AffineRecovery::Fixed { .. }))
    {
        return Err(AffineAggregationCertificateError::Replay);
    }
    for step in &steps[fixed_count..] {
        if guard.stopped() {
            return Err(AffineAggregationCertificateError::Caps);
        }
        let candidate =
            replay_candidate(&work, step).ok_or(AffineAggregationCertificateError::Replay)?;
        apply_candidate(work, candidate, guard).ok_or(AffineAggregationCertificateError::Replay)?;
        if work.recover.last() != Some(step) {
            return Err(AffineAggregationCertificateError::Replay);
        }
    }
    Ok(())
}

pub(super) fn replay_candidate(work: &Work, step: &AffineRecovery) -> Option<Candidate> {
    let AffineRecovery::Equality {
        row,
        col: pivot,
        constant: recorded_constant,
        terms: recorded_terms,
    } = step
    else {
        return None;
    };
    let row_spec = work.rows.get(*row)?;
    if !row_spec.active || !work.cols.get(*pivot)?.active {
        return None;
    }
    let rhs = equality_rhs(row_spec)?;
    let pivot_coefficient = &row_spec
        .coeffs
        .iter()
        .find(|(column, _)| column == pivot)?
        .1;
    let constant = rhs / pivot_coefficient;
    let mut terms = Vec::new();
    terms
        .try_reserve_exact(row_spec.coeffs.len().saturating_sub(1))
        .ok()?;
    for (column, coefficient) in &row_spec.coeffs {
        if column != pivot {
            terms.push((*column, -coefficient / pivot_coefficient));
        }
    }
    if &constant != recorded_constant
        || &terms != recorded_terms
        || !rational_fits(&constant)
        || terms.iter().any(|(_, value)| !rational_fits(value))
        || !integrality_preserved(work, *pivot, &constant, &terms)
        || !expression_inside_box(work, *pivot, &constant, &terms)
    {
        return None;
    }
    Some(Candidate {
        row: *row,
        pivot: *pivot,
        constant,
        terms,
        key: (false, 0, 0, *row, *pivot),
    })
}
