// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// Project exact fixed columns, then aggregate equality pivots whose recovered
/// value is implied to remain in its box.
///
/// `memory_budget` is the solve's retained-memory envelope. This pass reserves
/// at most one sixteenth of it for exact sparse work; a model that does not fit
/// simply stays on the original path. `None` still has a hard 512 MiB planning
/// envelope, so an unlimited solve cannot create an unlimited presolve.
pub(crate) fn aggregate_implied_free_equalities(
    model: &Model,
    deadline: Option<Instant>,
    memory_budget: Option<usize>,
) -> Option<(Model, AffineAggregationPostsolve)> {
    aggregate_implied_free_equalities_from_source(model, model, deadline, memory_budget)
}

/// Source-bound variant used after row-preserving exact propagation. `source`
/// is the caller frame the artifact binds to; `model` may differ only in its
/// column box. The independent verifier re-derives a threshold-free closure
/// from `source` before licensing that analysis box.
fn aggregate_implied_free_equalities_from_source(
    source: &Model,
    model: &Model,
    deadline: Option<Instant>,
    memory_budget: Option<usize>,
) -> Option<(Model, AffineAggregationPostsolve)> {
    if expired(deadline)
        || memory_budget == Some(0)
        || model.has_inexact_coeffs()
        || source.has_inexact_coeffs()
        || model.margin_row().is_some()
        || !same_literal_model_except_bounds(source, model)
    {
        return None;
    }

    let n = model.num_cols();
    let nr = model.num_rows();
    // This scan is intentionally f64/metadata-only.  Most integral MIPs do not
    // have fixed columns or equality pivots, and must decline before allocating
    // a single `BigRational` or sparse work vector.
    let preflight = structural_preflight(model, deadline, memory_budget)?;
    let growth_allowance = preflight.input_nnz / 2 + 1_024;
    let nnz_cap = preflight
        .input_nnz
        .checked_add(growth_allowance)?
        .min(MAX_TOTAL_TERMS);
    let planned =
        planned_transform_bytes(n, nr, preflight.input_nnz, nnz_cap, preflight.max_row_nnz)?;
    let guard = ResourceGuard::new(deadline, memory_budget, planned)?;
    let (mut work, analysis_bounds) = initial_work(model, &preflight, nnz_cap, &guard)?;
    project_fixed_columns(&mut work, &guard)?;
    aggregate_candidates(&mut work, &guard)?;
    if work.recover.is_empty()
        || !material_reduction(model.num_cols(), work.recover.len())
        || guard.stopped()
    {
        return None;
    }
    let caps = transform_caps(source, &preflight, nnz_cap);
    emit(source, model, work, analysis_bounds, caps, &guard)
}

fn initial_work(
    model: &Model,
    preflight: &StructuralPreflight,
    nnz_cap: usize,
    guard: &ResourceGuard,
) -> Option<(Work, Vec<AnalysisBound>)> {
    let (cols, objective, analysis_bounds) = initial_columns(model, guard)?;
    let rows = initial_rows(model, guard)?;
    let work = Work {
        cols,
        rows,
        objective,
        input_nnz: preflight.input_nnz,
        active_nnz: preflight.input_nnz,
        nnz_cap,
        recovery_term_cap: nnz_cap.min(MAX_RECOVERY_TERMS),
        const_delta: BigRational::zero(),
        recover: Vec::new(),
        recovery_terms: 0,
    };
    Some((work, analysis_bounds))
}

fn initial_columns(
    model: &Model,
    guard: &ResourceGuard,
) -> Option<(Vec<WorkCol>, Vec<BigRational>, Vec<AnalysisBound>)> {
    let n = model.num_cols();
    let mut cols = Vec::new();
    let mut objective = Vec::new();
    let mut analysis_bounds = Vec::new();
    cols.try_reserve_exact(n).ok()?;
    objective.try_reserve_exact(n).ok()?;
    analysis_bounds.try_reserve_exact(n).ok()?;
    for column in 0..n {
        if column.is_multiple_of(256) && guard.stopped() {
            return None;
        }
        let handle = Col(column as u32);
        let (lower, upper) = model.col_bounds(handle);
        cols.push(WorkCol {
            active: true,
            lower: exact(lower),
            upper: exact(upper),
            kind: model.col_kind(handle),
        });
        analysis_bounds.push(AnalysisBound {
            lower: exact(lower),
            upper: exact(upper),
        });
        objective.push(exact(model.obj_coeff(handle))?);
    }
    Some((cols, objective, analysis_bounds))
}

fn initial_rows(model: &Model, guard: &ResourceGuard) -> Option<Vec<WorkRow>> {
    let nr = model.num_rows();
    let mut rows = Vec::new();
    rows.try_reserve_exact(nr).ok()?;
    let mut terms_seen = 0usize;
    for row_index in 0..nr {
        if row_index.is_multiple_of(256) && guard.stopped() {
            return None;
        }
        let (coefficients, lower, upper) = model.row(Row(row_index as u32));
        let mut exact_coefficients = Vec::new();
        exact_coefficients
            .try_reserve_exact(coefficients.len())
            .ok()?;
        for &(column, coefficient) in coefficients {
            terms_seen = terms_seen.checked_add(1)?;
            if terms_seen.is_multiple_of(1_024) && guard.stopped() {
                return None;
            }
            let value = exact(coefficient)?;
            if !rational_fits(&value) {
                return None;
            }
            if !value.is_zero() {
                exact_coefficients.push((column as usize, value));
            }
        }
        rows.push(WorkRow {
            active: true,
            lower: exact(lower),
            upper: exact(upper),
            coeffs: exact_coefficients,
        });
    }
    Some(rows)
}

fn aggregate_candidates(work: &mut Work, guard: &ResourceGuard) -> Option<()> {
    let mut blocked = HashSet::new();
    while work.recover.len() < MAX_ELIMINATIONS && !guard.stopped() {
        let Some(candidate) = choose_candidate(work, &blocked, guard)? else {
            break;
        };
        let rejected = (candidate.row, candidate.pivot);
        if apply_candidate(work, candidate, guard).is_some() {
            blocked.clear();
        } else {
            blocked.insert(rejected);
        }
    }
    Some(())
}

fn transform_caps(
    source: &Model,
    preflight: &StructuralPreflight,
    nnz_cap: usize,
) -> AffineAggregationCaps {
    AffineAggregationCaps {
        version: ANALYSIS_VERSION,
        source_cols: source.num_cols(),
        source_rows: source.num_rows(),
        input_nnz: preflight.input_nnz,
        nnz_cap,
        max_eliminations: MAX_ELIMINATIONS,
        max_row_terms: MAX_ROW_TERMS,
        max_total_terms: MAX_TOTAL_TERMS,
        max_recovery_terms: MAX_RECOVERY_TERMS,
        max_rational_bits: MAX_RATIONAL_BITS,
        analysis_rounds: MAX_ANALYSIS_ROUNDS,
        analysis_term_visits: MAX_ANALYSIS_TERM_VISITS,
    }
}

pub(super) fn project_fixed_columns(work: &mut Work, guard: &ResourceGuard) -> Option<()> {
    for column in 0..work.cols.len() {
        if column.is_multiple_of(128) && guard.stopped() {
            return None;
        }
        if work.recover.len() >= MAX_ELIMINATIONS {
            break;
        }
        let Some(value) = work.cols[column]
            .lower
            .as_ref()
            .zip(work.cols[column].upper.as_ref())
            .filter(|(lower, upper)| lower == upper)
            .map(|(value, _)| value.clone())
        else {
            continue;
        };
        if work.cols[column].kind.is_integral() && !value.is_integer() {
            // The caller's model is integer-infeasible, but this transformer
            // has no certificate to export.  Leave diagnosis to the old path.
            return None;
        }
        if !rational_fits(&value) {
            return None;
        }

        for row_index in 0..work.rows.len() {
            if row_index.is_multiple_of(128) && guard.stopped() {
                return None;
            }
            if !work.rows[row_index].active {
                continue;
            }
            let Some(position) = work.rows[row_index]
                .coeffs
                .iter()
                .position(|&(candidate, _)| candidate == column)
            else {
                continue;
            };
            let coefficient = work.rows[row_index].coeffs[position].1.clone();
            let shift = coefficient * &value;
            if !rational_fits(&shift) {
                return None;
            }
            shift_bound(&mut work.rows[row_index].lower, &shift)?;
            shift_bound(&mut work.rows[row_index].upper, &shift)?;
            work.rows[row_index].coeffs.remove(position);
            work.active_nnz = work.active_nnz.checked_sub(1)?;
            if work.rows[row_index].coeffs.is_empty() {
                if !zero_satisfies(&work.rows[row_index].lower, &work.rows[row_index].upper) {
                    return None;
                }
                work.rows[row_index].active = false;
            }
        }

        let delta = &work.objective[column] * &value;
        let next_delta = &work.const_delta + delta;
        if !rational_fits(&next_delta) {
            return None;
        }
        work.const_delta = next_delta;
        work.objective[column] = BigRational::zero();
        work.cols[column].active = false;
        work.recover
            .push(AffineRecovery::Fixed { col: column, value });
    }
    Some(())
}

pub(super) fn choose_candidate(
    work: &Work,
    blocked: &HashSet<(usize, usize)>,
    guard: &ResourceGuard,
) -> Option<Option<Candidate>> {
    let incidence = build_incidence(work, guard)?;
    let mut best: Option<Candidate> = None;
    let mut candidates_seen = 0usize;
    for (row_index, row) in work.rows.iter().enumerate() {
        if row_index.is_multiple_of(128) && guard.stopped() {
            return None;
        }
        if !row.active || row.coeffs.is_empty() || row.coeffs.len() > MAX_ROW_TERMS {
            continue;
        }
        let Some(rhs) = equality_rhs(row) else {
            continue;
        };
        for &(pivot, ref pivot_coefficient) in &row.coeffs {
            candidates_seen = candidates_seen.checked_add(1)?;
            if candidates_seen > MAX_CANDIDATES_PER_ROUND {
                return Some(best);
            }
            if candidates_seen.is_multiple_of(64) && guard.stopped() {
                return None;
            }
            let Some(candidate) = candidate_for_pivot(
                work,
                blocked,
                &incidence,
                row_index,
                row,
                rhs,
                pivot,
                pivot_coefficient,
                guard,
            )?
            else {
                continue;
            };
            if best
                .as_ref()
                .is_none_or(|current| candidate.key < current.key)
            {
                best = Some(candidate);
            }
        }
    }
    Some(best)
}

fn build_incidence(work: &Work, guard: &ResourceGuard) -> Option<Vec<Vec<usize>>> {
    let mut incidence = Vec::new();
    incidence.try_reserve_exact(work.cols.len()).ok()?;
    incidence.resize_with(work.cols.len(), Vec::new);
    let mut incidence_terms = 0usize;
    for (row_index, row) in work.rows.iter().enumerate() {
        if row_index.is_multiple_of(256) && guard.stopped() {
            return None;
        }
        if !row.active {
            continue;
        }
        for &(column, _) in &row.coeffs {
            incidence_terms = incidence_terms.checked_add(1)?;
            if incidence_terms.is_multiple_of(1_024) && guard.stopped() {
                return None;
            }
            incidence[column].try_reserve(1).ok()?;
            incidence[column].push(row_index);
        }
    }
    Some(incidence)
}

fn candidate_for_pivot(
    work: &Work,
    blocked: &HashSet<(usize, usize)>,
    incidence: &[Vec<usize>],
    row_index: usize,
    row: &WorkRow,
    rhs: &BigRational,
    pivot: usize,
    pivot_coefficient: &BigRational,
    guard: &ResourceGuard,
) -> Option<Option<Candidate>> {
    if blocked.contains(&(row_index, pivot)) || !work.cols[pivot].active {
        return Some(None);
    }
    let constant = rhs / pivot_coefficient;
    if !rational_fits(&constant) {
        return Some(None);
    }
    let mut terms = Vec::new();
    terms
        .try_reserve_exact(row.coeffs.len().saturating_sub(1))
        .ok()?;
    for (term_index, &(column, ref coefficient)) in row.coeffs.iter().enumerate() {
        if term_index.is_multiple_of(256) && guard.stopped() {
            return None;
        }
        if column != pivot {
            let recovered = -coefficient / pivot_coefficient;
            if !rational_fits(&recovered) {
                return Some(None);
            }
            terms.push((column, recovered));
        }
    }
    if !integrality_preserved(work, pivot, &constant, &terms)
        || !expression_inside_box(work, pivot, &constant, &terms)
    {
        return Some(None);
    }
    let fill = predicted_fill(work, &incidence[pivot], row_index, pivot, &terms, guard)?;
    let markowitz = row
        .coeffs
        .len()
        .saturating_sub(1)
        .saturating_mul(incidence[pivot].len().saturating_sub(1));
    let key = (
        !(row.coeffs.len() == 2 || incidence[pivot].len() == 2),
        fill,
        markowitz,
        row_index,
        pivot,
    );
    Some(Some(Candidate {
        row: row_index,
        pivot,
        constant,
        terms,
        key,
    }))
}

pub(super) fn integrality_preserved(
    work: &Work,
    pivot: usize,
    constant: &BigRational,
    terms: &[(usize, BigRational)],
) -> bool {
    if !work.cols[pivot].kind.is_integral() {
        return true;
    }
    constant.is_integer()
        && terms.iter().all(|(column, coefficient)| {
            work.cols[*column].kind.is_integral() && coefficient.is_integer()
        })
}

pub(super) fn expression_inside_box(
    work: &Work,
    pivot: usize,
    constant: &BigRational,
    terms: &[(usize, BigRational)],
) -> bool {
    let mut minimum = Some(constant.clone());
    let mut maximum = Some(constant.clone());
    for (column, coefficient) in terms {
        let bounds = &work.cols[*column];
        let (at_minimum, at_maximum) = if coefficient.is_positive() {
            (&bounds.lower, &bounds.upper)
        } else {
            (&bounds.upper, &bounds.lower)
        };
        minimum = match (minimum, at_minimum) {
            (Some(value), Some(bound)) => Some(value + coefficient * bound),
            _ => None,
        };
        maximum = match (maximum, at_maximum) {
            (Some(value), Some(bound)) => Some(value + coefficient * bound),
            _ => None,
        };
        if minimum.as_ref().is_some_and(|value| !rational_fits(value))
            || maximum.as_ref().is_some_and(|value| !rational_fits(value))
        {
            return false;
        }
    }
    let lower_ok = work.cols[pivot]
        .lower
        .as_ref()
        .is_none_or(|lower| minimum.as_ref().is_some_and(|value| value >= lower));
    let upper_ok = work.cols[pivot]
        .upper
        .as_ref()
        .is_none_or(|upper| maximum.as_ref().is_some_and(|value| value <= upper));
    lower_ok && upper_ok
}

pub(super) fn predicted_fill(
    work: &Work,
    incidence: &[usize],
    defining_row: usize,
    pivot: usize,
    terms: &[(usize, BigRational)],
    guard: &ResourceGuard,
) -> Option<usize> {
    let survivor_columns: Vec<usize> = terms.iter().map(|&(column, _)| column).collect();
    let mut fill = 0usize;
    for (position, &row_index) in incidence.iter().enumerate() {
        if position.is_multiple_of(128) && guard.stopped() {
            return None;
        }
        let row = &work.rows[row_index];
        if !row.active || row_index == defining_row {
            continue;
        }
        if row
            .coeffs
            .binary_search_by_key(&pivot, |&(column, _)| column)
            .is_err()
        {
            continue;
        }
        let missing = survivor_columns
            .iter()
            .filter(|&&column| {
                row.coeffs
                    .binary_search_by_key(&column, |&(candidate, _)| candidate)
                    .is_err()
            })
            .count();
        fill = fill.checked_add(missing)?;
    }
    Some(fill)
}
