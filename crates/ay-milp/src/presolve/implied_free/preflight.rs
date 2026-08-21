// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

pub(super) fn structural_preflight(
    model: &Model,
    deadline: Option<Instant>,
    memory_budget: Option<usize>,
) -> Option<StructuralPreflight> {
    if memory_budget == Some(0) || preflight_stopped(deadline) {
        return None;
    }
    let n = model.num_cols();
    if n == 0 {
        return None;
    }
    let mut fixed = 0usize;
    for column in 0..n {
        if column.is_multiple_of(512) && preflight_stopped(deadline) {
            return None;
        }
        let (lower, upper) = model.col_bounds(Col(column as u32));
        if lower.is_finite() && lower == upper {
            fixed = fixed.checked_add(1)?;
        }
    }

    let mut input_nnz = 0usize;
    let mut max_row_nnz = 0usize;
    let mut equality_candidates = 0usize;
    for row_index in 0..model.num_rows() {
        if row_index.is_multiple_of(256) && preflight_stopped(deadline) {
            return None;
        }
        let (coefficients, lower, upper) = model.row(Row(row_index as u32));
        input_nnz = input_nnz.checked_add(coefficients.len())?;
        max_row_nnz = max_row_nnz.max(coefficients.len());
        if !lower.is_finite() || lower != upper || coefficients.is_empty() {
            continue;
        }
        // A cheap upper bound, deliberately: exact divisibility, implied-box,
        // and fill tests belong to the exact pass.  Here we only establish that
        // a row has some non-fixed pivot, without allocating a candidate list.
        let mut has_live_pivot = false;
        for (term_index, &(column, coefficient)) in coefficients.iter().enumerate() {
            if term_index.is_multiple_of(1_024) && preflight_stopped(deadline) {
                return None;
            }
            if coefficient == 0.0 {
                continue;
            }
            let (col_lower, col_upper) = model.col_bounds(Col(column));
            if !col_lower.is_finite() || col_lower != col_upper {
                has_live_pivot = true;
                break;
            }
        }
        if has_live_pivot {
            equality_candidates = equality_candidates.checked_add(1)?;
        }
    }
    let potential = fixed
        .checked_add(equality_candidates)?
        .min(n)
        .min(MAX_ELIMINATIONS);
    if potential == 0 || !material_reduction(n, potential) || preflight_stopped(deadline) {
        return None;
    }
    Some(StructuralPreflight {
        input_nnz,
        max_row_nnz,
    })
}

pub(super) fn same_literal_model_except_bounds(source: &Model, analyzed: &Model) -> bool {
    if source.num_cols() != analyzed.num_cols()
        || source.num_rows() != analyzed.num_rows()
        || source.has_objective() != analyzed.has_objective()
        || source.sense() != analyzed.sense()
        || source.objective_offset().to_bits() != analyzed.objective_offset().to_bits()
        || source.margin_row() != analyzed.margin_row()
    {
        return false;
    }
    for column in 0..source.num_cols() {
        let handle = Col(column as u32);
        if source.col_kind(handle) != analyzed.col_kind(handle)
            || source.obj_coeff(handle).to_bits() != analyzed.obj_coeff(handle).to_bits()
        {
            return false;
        }
        let (source_lower, source_upper) = source.col_bounds(handle);
        let (analysis_lower, analysis_upper) = analyzed.col_bounds(handle);
        if analysis_lower < source_lower
            || analysis_upper > source_upper
            || analysis_lower > analysis_upper
        {
            return false;
        }
    }
    for row in 0..source.num_rows() {
        let handle = Row(row as u32);
        let (source_coeffs, source_lower, source_upper) = source.row(handle);
        let (analysis_coeffs, analysis_lower, analysis_upper) = analyzed.row(handle);
        if source_lower.to_bits() != analysis_lower.to_bits()
            || source_upper.to_bits() != analysis_upper.to_bits()
            || source_coeffs.len() != analysis_coeffs.len()
            || source_coeffs.iter().zip(analysis_coeffs).any(
                |(&(source_column, source_value), &(analysis_column, analysis_value))| {
                    source_column != analysis_column
                        || source_value.to_bits() != analysis_value.to_bits()
                },
            )
        {
            return false;
        }
    }
    true
}

pub(super) fn material_reduction(columns: usize, removed: usize) -> bool {
    columns <= 32 || removed >= 8 || removed.saturating_mul(20) >= columns
}

pub(super) fn checked_charge(total: &mut usize, count: usize, bytes_each: usize) -> Option<()> {
    *total = total.checked_add(count.checked_mul(bytes_each)?)?;
    Some(())
}

/// Conservative peak for every simultaneously live owner in the transform.
/// This deliberately charges the same sparse term several times: the exact
/// work model, incidence, a full trial row-update batch, recovery, reduced
/// model, and postsolve coexist at emission.  The final factor covers bigint
/// limb allocator slack and `BTreeMap` nodes, whose exact sizes are platform
/// dependent.
pub(super) fn planned_transform_bytes(
    columns: usize,
    rows: usize,
    input_nnz: usize,
    nnz_cap: usize,
    max_row_nnz: usize,
) -> Option<usize> {
    let mut bytes = 0usize;

    // Exact work columns, their two bounds, and the dense exact objective.
    checked_charge(&mut bytes, columns, size_of::<WorkCol>())?;
    checked_charge(
        &mut bytes,
        columns.checked_mul(3)?,
        ESTIMATED_BYTES_PER_EXACT_VALUE,
    )?;
    // Exact work rows, row-bound values, and the primary coefficient store.
    checked_charge(&mut bytes, rows, size_of::<WorkRow>())?;
    checked_charge(
        &mut bytes,
        rows.checked_mul(2)?,
        ESTIMATED_BYTES_PER_EXACT_VALUE,
    )?;
    checked_charge(&mut bytes, input_nnz, ESTIMATED_BYTES_PER_EXACT_TERM)?;

    // Per-round incidence and candidate/blocked ordering state.
    checked_charge(&mut bytes, columns, size_of::<Vec<usize>>())?;
    checked_charge(&mut bytes, nnz_cap, size_of::<usize>())?;
    checked_charge(
        &mut bytes,
        max_row_nnz.min(MAX_ROW_TERMS),
        ESTIMATED_BYTES_PER_EXACT_TERM,
    )?;
    checked_charge(
        &mut bytes,
        MAX_CANDIDATES_PER_ROUND,
        size_of::<(usize, usize)>() * 3,
    )?;

    // One atomic substitution keeps every affected rebuilt row until commit.
    // Charge both its vector terms and a second term-sized allowance for the
    // temporary ordered-map nodes used while each row is merged.
    checked_charge(&mut bytes, rows, size_of::<(usize, WorkRow)>())?;
    checked_charge(
        &mut bytes,
        nnz_cap.checked_mul(2)?,
        ESTIMATED_BYTES_PER_EXACT_TERM,
    )?;

    // Reverse recovery plus the reduced Model and its postsolve mapping remain
    // live together when the speculative transform returns.
    checked_charge(&mut bytes, columns, size_of::<AffineRecovery>())?;
    checked_charge(&mut bytes, columns, ESTIMATED_BYTES_PER_EXACT_VALUE)?;
    checked_charge(&mut bytes, nnz_cap, ESTIMATED_BYTES_PER_EXACT_TERM)?;
    checked_charge(&mut bytes, columns, size_of::<Option<Col>>())?;
    checked_charge(&mut bytes, columns, ESTIMATED_MODEL_COL_BYTES)?;
    checked_charge(&mut bytes, rows, ESTIMATED_MODEL_ROW_BYTES)?;
    checked_charge(&mut bytes, nnz_cap, ESTIMATED_MODEL_TERM_BYTES)?;

    // The source-licensed propagation box survives in the replay artifact.
    // It is distinct from the WorkCol bounds and therefore must be charged as
    // another exact owner, not treated as metadata-only bookkeeping.
    checked_charge(&mut bytes, columns, size_of::<AnalysisBound>())?;
    checked_charge(
        &mut bytes,
        columns.checked_mul(2)?,
        ESTIMATED_BYTES_PER_EXACT_VALUE,
    )?;

    // The eventual caller-frame point and arithmetic temporaries are part of
    // the retained plan too, rather than an unbudgeted postsolve afterthought.
    checked_charge(&mut bytes, columns, ESTIMATED_BYTES_PER_EXACT_VALUE)?;
    bytes.checked_mul(2)
}

pub(super) fn planned_widen_bytes(columns: usize, recovery_terms: usize) -> Option<usize> {
    let mut bytes = 0usize;
    checked_charge(&mut bytes, columns, ESTIMATED_BYTES_PER_EXACT_VALUE)?;
    checked_charge(&mut bytes, recovery_terms, ESTIMATED_BYTES_PER_EXACT_VALUE)?;
    bytes.checked_mul(2)
}

pub(super) fn current_process_bytes() -> usize {
    let live = ay_sys::current_live_bytes();
    let footprint = ay_sys::current_footprint_bytes();
    let physical = if footprint == 0 {
        ay_sys::current_rss_bytes()
    } else {
        footprint
    };
    live.max(physical)
}

pub(super) fn preflight_stopped(deadline: Option<Instant>) -> bool {
    expired(deadline) || ay_sys::live_bytes_exceeded_at_percent(PROCESS_MEMORY_PERCENT)
}
