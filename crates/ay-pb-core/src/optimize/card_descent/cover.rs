// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The APPLICABILITY GATE and the normalized covering view it produces.
//!
//! [`build_cover_view`] is the single place that decides whether an instance is
//! a UNICOST COVERING program (see the crate-module docs in `super`); it either
//! returns the advisory [`CoverView`] the search runs on, or `None`, in which
//! case the whole arm does nothing.
//!
//! The view is ADVISORY ONLY: it steers move selection and never decides what
//! is reported, so a normalization bug here can lose a solution but can never
//! produce a wrong one — every candidate is re-verified against the ORIGINAL
//! constraints in `super::record`.

use crate::types::{PbConstraint, PbInstance, PbObjective, PbRel};

/// Variable cap. Above this the per-swap bookkeeping stops paying for itself
/// against the general SLS arms; decline rather than crowd them out.
const MAX_CARD_VARS: usize = 100_000;

/// Cap on total constraint occurrences (sum of row lengths) for the two CSR
/// indexes this module builds.
const MAX_CARD_OCCURRENCES: usize = 4_000_000;

/// The normalized monotone covering view: rows `sum_v c_v x_v >= d` with every
/// `c_v > 0` and `d > 0`, in both row-major and variable-major CSR form.
pub(super) struct CoverView {
    pub(super) num_vars: usize,
    pub(super) row_start: Vec<u32>,
    pub(super) row_var: Vec<u32>,
    pub(super) row_coeff: Vec<i64>,
    pub(super) rhs: Vec<i64>,
    pub(super) var_start: Vec<u32>,
    pub(super) var_row: Vec<u32>,
    pub(super) var_coeff: Vec<i64>,
    /// Selectable variables: the objective support restricted to variables that
    /// occur in at least one kept row. Everything else stays false.
    pub(super) ground: Vec<u32>,
}

impl CoverView {
    pub(super) fn num_rows(&self) -> usize {
        self.rhs.len()
    }

    pub(super) fn row_entries(&self, row: usize) -> impl Iterator<Item = (u32, i64)> + '_ {
        let lo = self.row_start[row] as usize;
        let hi = self.row_start[row + 1] as usize;
        self.row_var[lo..hi]
            .iter()
            .copied()
            .zip(self.row_coeff[lo..hi].iter().copied())
    }

    pub(super) fn var_entries(&self, var: usize) -> impl Iterator<Item = (u32, i64)> + '_ {
        let lo = self.var_start[var] as usize;
        let hi = self.var_start[var + 1] as usize;
        self.var_row[lo..hi]
            .iter()
            .copied()
            .zip(self.var_coeff[lo..hi].iter().copied())
    }
}

/// One normalized row, or a verdict about it.
enum NormRow {
    /// `sum (var, coeff) x >= rhs`, every coeff > 0, rhs > 0.
    Keep(Vec<(u32, i64)>, i64),
    /// `rhs <= 0` after normalization: satisfied by every assignment.
    Trivial,
    /// Outside the covering fragment, or unsatisfiable: decline the instance.
    Reject,
}

/// Normalizes one constraint into the monotone covering fragment.
///
/// `acc` is a scratch coefficient accumulator of length `num_vars` that this
/// function leaves ZEROED on every exit path.
fn normalize_row(constraint: &PbConstraint, num_vars: usize, acc: &mut [i128]) -> NormRow {
    if constraint.rel != PbRel::Ge {
        return NormRow::Reject;
    }
    let mut rhs: i128 = constraint.rhs;
    let mut touched: Vec<u32> = Vec::with_capacity(constraint.terms.len());
    let mut rejected = false;
    for term in &constraint.terms {
        let Some(lit) = term.lits.first().filter(|_| term.lits.len() == 1) else {
            rejected = true;
            break;
        };
        let Some(var) = (lit.var as usize).checked_sub(1).filter(|v| *v < num_vars) else {
            rejected = true;
            break;
        };
        if acc[var] == 0 {
            touched.push(var as u32);
        }
        if lit.negated {
            acc[var] -= term.coeff;
            rhs -= term.coeff;
        } else {
            acc[var] += term.coeff;
        }
    }
    let outcome = if rejected {
        NormRow::Reject
    } else {
        collect_normalized(&touched, acc, rhs)
    };
    for &var in &touched {
        acc[var as usize] = 0;
    }
    outcome
}

/// Turns the accumulated coefficients into a [`NormRow`]. Split out of
/// [`normalize_row`] so the accumulator is always zeroed on one path.
fn collect_normalized(touched: &[u32], acc: &[i128], rhs: i128) -> NormRow {
    // MONOTONICITY FIRST, triviality second. A negative normalized
    // coefficient puts the row outside the monotone covering fragment no
    // matter the rhs: an at-most-one row (`-x1 - x2 >= -1`) or an implication
    // row (`-x1 + x2 >= 0`) normalizes to `rhs <= 0` yet is NOT trivially
    // true. The old order dropped such rows as "trivial", leaving the
    // advisory view a strict relaxation; that stayed SOUND (the first greedy
    // candidate failed `record`'s original-constraint re-verification and the
    // arm declined fail-closed) but the decline was accidental and paid for a
    // full view build + greedy + doomed verification — measured 47ms on
    // `primes-dimacs-cnf/ii16d2` and 99us on `routing/s4-4-3-1pb`, against
    // the microsecond structural declines this gate promises. Rejecting here
    // makes the same verdict structural and O(row).
    if touched.iter().any(|&var| acc[var as usize] < 0) {
        return NormRow::Reject;
    }
    if rhs <= 0 {
        return NormRow::Trivial;
    }
    let Ok(rhs) = i64::try_from(rhs) else {
        return NormRow::Reject;
    };
    let mut entries: Vec<(u32, i64)> = Vec::with_capacity(touched.len());
    let mut reach: i64 = 0;
    for &var in touched {
        let coeff = acc[var as usize];
        debug_assert!(coeff >= 0, "negative coefficients were rejected above");
        if coeff == 0 {
            continue;
        }
        let Ok(coeff) = i64::try_from(coeff) else {
            return NormRow::Reject;
        };
        let Some(next) = reach.checked_add(coeff) else {
            return NormRow::Reject;
        };
        reach = next;
        entries.push((var, coeff));
    }
    if reach < rhs {
        // Unsatisfiable row: the instance is infeasible, which a primal
        // heuristic cannot help with. Decline rather than spin.
        return NormRow::Reject;
    }
    NormRow::Keep(entries, rhs)
}

/// Returns the objective support mask, or `None` when the objective is not
/// `min c * sum x_v` for one positive `c` over DISTINCT non-negated variables.
fn unicost_support(objective: &PbObjective, num_vars: usize) -> Option<Vec<bool>> {
    if objective.terms.is_empty() {
        return None;
    }
    let mut priced = vec![false; num_vars];
    let unit = objective.terms.first()?.coeff;
    if unit <= 0 {
        return None;
    }
    for term in &objective.terms {
        if term.coeff != unit || term.lits.len() != 1 {
            return None;
        }
        let lit = term.lits[0];
        if lit.negated {
            return None;
        }
        let var = (lit.var as usize)
            .checked_sub(1)
            .filter(|v| *v < num_vars)?;
        if priced[var] {
            return None;
        }
        priced[var] = true;
    }
    Some(priced)
}

/// Builds the advisory [`CoverView`], or returns `None` when the instance is
/// outside the unicost-covering fragment (see the `super` applicability note).
pub(super) fn build_cover_view(
    instance: &PbInstance,
    objective: &PbObjective,
) -> Option<CoverView> {
    let num_vars = usize::try_from(instance.num_vars).ok()?;
    if num_vars == 0 || num_vars > MAX_CARD_VARS {
        return None;
    }
    let priced = unicost_support(objective, num_vars)?;

    let mut acc = vec![0i128; num_vars];
    let mut row_start: Vec<u32> = vec![0];
    let mut row_var: Vec<u32> = Vec::new();
    let mut row_coeff: Vec<i64> = Vec::new();
    let mut rhs: Vec<i64> = Vec::new();
    let mut in_ground = vec![false; num_vars];
    for constraint in &instance.constraints {
        match normalize_row(constraint, num_vars, &mut acc) {
            NormRow::Reject => return None,
            NormRow::Trivial => {}
            NormRow::Keep(entries, bound) => {
                if row_var.len().saturating_add(entries.len()) > MAX_CARD_OCCURRENCES {
                    return None;
                }
                for (var, coeff) in entries {
                    if !priced[var as usize] {
                        // A constrained but unpriced variable breaks
                        // `objective == unit * |S|`.
                        return None;
                    }
                    in_ground[var as usize] = true;
                    row_var.push(var);
                    row_coeff.push(coeff);
                }
                rhs.push(bound);
                row_start.push(u32::try_from(row_var.len()).ok()?);
            }
        }
    }
    if rhs.is_empty() {
        return None;
    }
    let ground: Vec<u32> = (0..num_vars)
        .filter(|v| in_ground[*v])
        .map(|v| v as u32)
        .collect();
    let (var_start, var_row, var_coeff) = transpose(num_vars, &row_start, &row_var, &row_coeff);
    Some(CoverView {
        num_vars,
        row_start,
        row_var,
        row_coeff,
        rhs,
        var_start,
        var_row,
        var_coeff,
        ground,
    })
}

/// Row-major CSR -> variable-major CSR (counting sort).
fn transpose(
    num_vars: usize,
    row_start: &[u32],
    row_var: &[u32],
    row_coeff: &[i64],
) -> (Vec<u32>, Vec<u32>, Vec<i64>) {
    let mut var_start = vec![0u32; num_vars + 1];
    for &var in row_var {
        var_start[var as usize + 1] += 1;
    }
    for index in 0..num_vars {
        var_start[index + 1] += var_start[index];
    }
    let mut cursor = var_start.clone();
    let mut var_row = vec![0u32; row_var.len()];
    let mut var_coeff = vec![0i64; row_var.len()];
    for row in 0..row_start.len() - 1 {
        let lo = row_start[row] as usize;
        let hi = row_start[row + 1] as usize;
        for slot in lo..hi {
            let var = row_var[slot] as usize;
            let at = cursor[var] as usize;
            var_row[at] = row as u32;
            var_coeff[at] = row_coeff[slot];
            cursor[var] += 1;
        }
    }
    (var_start, var_row, var_coeff)
}
