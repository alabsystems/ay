// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

pub(super) fn emit(
    source: &Model,
    original: &Model,
    work: Work,
    analysis_bounds: Vec<AnalysisBound>,
    caps: AffineAggregationCaps,
    guard: &ResourceGuard,
) -> Option<(Model, AffineAggregationPostsolve)> {
    let (mut reduced, map) = emit_columns(original, &work, guard)?;
    emit_rows(&mut reduced, &work, &map, guard)?;
    emit_objective(&mut reduced, original, &work, &map, guard)?;

    if trace_enabled() {
        eprintln!(
            "--trace presolve: equality aggregation eliminated {} columns; model {}r/{}c/{}nz -> {}r/{}c/{}nz",
            work.recover.len(),
            original.num_rows(),
            original.num_cols(),
            work.input_nnz,
            reduced.num_rows(),
            reduced.num_cols(),
            work.active_nnz,
        );
    }
    let recover: Arc<[AffineRecovery]> = work.recover.into();
    let analysis = AffineAggregationAnalysis {
        source_digest: crate::cert_io::canonical_digest(source),
        reduced_digest: crate::cert_io::canonical_digest(&reduced),
        bounds: analysis_bounds.into(),
        steps: Arc::clone(&recover),
        objective_delta: work.const_delta.clone(),
        caps,
    };
    let postsolve = AffineAggregationPostsolve {
        n_orig: original.num_cols(),
        n_reduced: map.iter().filter(|entry| entry.is_some()).count(),
        map,
        recover,
        recovery_terms: work.recovery_terms,
        const_delta: work.const_delta,
        analysis,
    };
    Some((reduced, postsolve))
}

fn emit_columns(
    original: &Model,
    work: &Work,
    guard: &ResourceGuard,
) -> Option<(Model, Vec<Option<Col>>)> {
    let mut reduced = Model::new();
    reduced.inherit_ft_adoption_solve_latch(original);
    let mut map = vec![None; work.cols.len()];
    for (column, spec) in work.cols.iter().enumerate() {
        if column.is_multiple_of(256) && guard.stopped() {
            return None;
        }
        if !spec.active {
            continue;
        }
        let lower = bound_f64(&spec.lower, true)?;
        let upper = bound_f64(&spec.upper, false)?;
        let new_column = match spec.kind {
            ColKind::Continuous => reduced.add_col(lower, upper),
            ColKind::Binary => reduced.add_binary_col(),
            ColKind::Integer => reduced.add_int_col(lower, upper),
        };
        // `add_binary_col` starts at 0/1, so preserve tightened boxes too.
        reduced.cols[new_column.index()].lb = lower;
        reduced.cols[new_column.index()].ub = upper;
        map[column] = Some(new_column);
    }
    Some((reduced, map))
}

fn emit_rows(
    reduced: &mut Model,
    work: &Work,
    map: &[Option<Col>],
    guard: &ResourceGuard,
) -> Option<()> {
    for (row_index, row) in work.rows.iter().enumerate() {
        if row_index.is_multiple_of(128) && guard.stopped() {
            return None;
        }
        if !row.active {
            continue;
        }
        let mut coefficients = Vec::new();
        coefficients.try_reserve_exact(row.coeffs.len()).ok()?;
        for (term_index, (column, value)) in row.coeffs.iter().enumerate() {
            if term_index.is_multiple_of(1_024) && guard.stopped() {
                return None;
            }
            coefficients.push((map[*column]?.0, exact_f64(value)?));
        }
        reduced.add_row_sorted_unique(
            bound_f64(&row.lower, true)?,
            bound_f64(&row.upper, false)?,
            coefficients,
        );
    }
    Some(())
}

fn emit_objective(
    reduced: &mut Model,
    original: &Model,
    work: &Work,
    map: &[Option<Col>],
    guard: &ResourceGuard,
) -> Option<()> {
    if !original.has_objective() {
        return Some(());
    }
    let mut objective = Vec::new();
    for (column, value) in work.objective.iter().enumerate() {
        if column.is_multiple_of(256) && guard.stopped() {
            return None;
        }
        if value.is_zero() {
            continue;
        }
        objective.try_reserve(1).ok()?;
        objective.push((map[column]?, exact_f64(value)?));
    }
    reduced.set_objective(&objective, original.sense());
    // `set_objective_offset` marks a model as objective-bearing, so only call
    // it on the same branch as the original implementation.
    reduced.set_objective_offset(original.objective_offset());
    Some(())
}
