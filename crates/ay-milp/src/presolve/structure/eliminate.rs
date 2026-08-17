// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::time::Instant;

use num_rational::BigRational;
use num_traits::{Signed, Zero};

use super::super::{as_exact_f64, tighten_bounds_opt, Presolved};
use super::{trace_enabled, FixedRecovery, StructurePostsolve};
use crate::model::{exact, Col, ColKind, Model, Row};

type ExactRow = Vec<(usize, f64, BigRational)>;
type ExactBounds = Vec<Option<BigRational>>;

struct Reduction {
    model: Model,
    lower: ExactBounds,
    upper: ExactBounds,
    fixed: ExactBounds,
    rows: Vec<ExactRow>,
    row_lower: ExactBounds,
    row_upper: ExactBounds,
    shift: Vec<BigRational>,
    drop_row: Vec<bool>,
}

impl Reduction {
    fn prepare(model: &Model, deadline: Option<Instant>) -> Option<Self> {
        // The box every decision below is taken under, AND the box the reduced
        // model will carry. Those must be the same box or the redundancy
        // argument is circular.
        //
        // Coefficient tightening is OFF, so every kept row is the caller's row
        // VERBATIM. This also preserves the row identity needed by a future
        // certificate lift.
        let tightened = match tighten_bounds_opt(model, deadline, false) {
            Presolved::Infeasible => return None,
            Presolved::Tightened(model) => *model,
        };
        let (lower, upper) = exact_bounds(&tightened)?;
        let fixed = fixed_columns(&tightened, &lower, &upper)?;
        let (rows, row_lower, row_upper) = exact_rows(&tightened, deadline)?;
        let nr = tightened.num_rows();
        Some(Self {
            model: tightened,
            lower,
            upper,
            fixed,
            rows,
            row_lower,
            row_upper,
            shift: vec![BigRational::zero(); nr],
            drop_row: Vec::new(),
        })
    }

    fn stabilize_shifts(&mut self, deadline: Option<Instant>) -> Option<()> {
        let n = self.model.num_cols();
        let nr = self.model.num_rows();
        // A shifted finite side that no `f64` denotes exactly cannot be emitted.
        // Un-fix every fixed column in that row and recompute to a monotone
        // fixpoint instead of rounding the bound.
        for _pass in 0..(n + 2) {
            let mut changed = false;
            for r in 0..nr {
                if r % 256 == 0 && expired(deadline) {
                    return None;
                }
                let shift = row_shift(&self.rows[r], &self.fixed);
                let exact_lower = self.row_lower[r]
                    .as_ref()
                    .is_none_or(|bound| as_exact_f64(&(bound - &shift)).is_some());
                let exact_upper = self.row_upper[r]
                    .as_ref()
                    .is_none_or(|bound| as_exact_f64(&(bound - &shift)).is_some());
                if exact_lower && exact_upper {
                    self.shift[r] = shift;
                } else {
                    for (column, _, _) in &self.rows[r] {
                        if self.fixed[*column].take().is_some() {
                            changed = true;
                        }
                    }
                }
            }
            if !changed {
                break;
            }
        }
        // Re-derive under the final fixed set, independent of which pass ended
        // the loop.
        for r in 0..nr {
            self.shift[r] = row_shift(&self.rows[r], &self.fixed);
        }
        Some(())
    }

    fn classify_rows(&mut self, deadline: Option<Instant>) -> Option<()> {
        self.drop_row = vec![false; self.model.num_rows()];
        for r in 0..self.model.num_rows() {
            if r % 256 == 0 && expired(deadline) {
                return None;
            }
            let survivors: Vec<(usize, BigRational)> = self.rows[r]
                .iter()
                .filter(|(column, _, _)| self.fixed[*column].is_none())
                .map(|(column, _, coefficient)| (*column, coefficient.clone()))
                .collect();
            let lower = self.row_lower[r].as_ref().map(|b| b - &self.shift[r]);
            let upper = self.row_upper[r].as_ref().map(|b| b - &self.shift[r]);
            if survivors.is_empty() {
                let satisfied = lower
                    .as_ref()
                    .is_none_or(|bound| bound <= &BigRational::zero())
                    && upper
                        .as_ref()
                        .is_none_or(|bound| bound >= &BigRational::zero());
                if !satisfied {
                    return None;
                }
                self.drop_row[r] = true;
                continue;
            }
            let (minimum, maximum) = activity(&survivors, &self.lower, &self.upper);
            let lower_implied = match (&lower, &minimum) {
                (None, _) => true,
                (Some(_), None) => false,
                (Some(bound), Some(minimum)) => minimum >= bound,
            };
            let upper_implied = match (&upper, &maximum) {
                (None, _) => true,
                (Some(_), None) => false,
                (Some(bound), Some(maximum)) => maximum <= bound,
            };
            self.drop_row[r] = lower_implied && upper_implied;
        }
        Some(())
    }

    fn reduction_counts(&self) -> Option<(usize, usize)> {
        let n = self.model.num_cols();
        let nr = self.model.num_rows();
        let n_fixed = self.fixed.iter().filter(|entry| entry.is_some()).count();
        let n_dropped = self.drop_row.iter().filter(|drop| **drop).count();
        if trace_enabled() {
            eprintln!(
                "--trace struct-elim: fixed-cols {n_fixed} redundant-rows {n_dropped}; \
                 model {nr}r/{n}c -> {}r/{}c",
                nr - n_dropped,
                n - n_fixed,
            );
        }
        (n_fixed != 0 || n_dropped != 0).then_some((n_fixed, n_dropped))
    }

    fn build_columns(
        &self,
        original: &Model,
        n_fixed: usize,
    ) -> Option<(Model, Vec<Option<Col>>, Vec<FixedRecovery>, BigRational)> {
        let n = self.model.num_cols();
        let mut reduced = Model::new();
        reduced.inherit_ft_adoption_solve_latch(original);
        let mut map = vec![None; n];
        let mut recover = Vec::with_capacity(n_fixed);
        let mut const_delta = BigRational::zero();
        for j in 0..n {
            let column = Col(j as u32);
            if let Some(value) = self.fixed[j].as_ref() {
                let objective = exact(self.model.obj_coeff(column))?;
                if !objective.is_zero() {
                    const_delta += &objective * value;
                }
                recover.push(FixedRecovery {
                    col: j,
                    value: value.clone(),
                });
                continue;
            }
            let (lower, upper) = self.model.col_bounds(column);
            let reduced_column = match self.model.col_kind(column) {
                ColKind::Continuous => reduced.add_col(lower, upper),
                ColKind::Binary => reduced.add_binary_col(),
                ColKind::Integer => reduced.add_int_col(lower, upper),
            };
            // The binary constructor ignores bounds and the integer constructor
            // may round; copy the tightened box verbatim.
            reduced.cols[reduced_column.index()].lb = lower;
            reduced.cols[reduced_column.index()].ub = upper;
            map[j] = Some(reduced_column);
        }
        Some((reduced, map, recover, const_delta))
    }

    fn emit_rows(
        &self,
        reduced: &mut Model,
        map: &[Option<Col>],
        n_dropped: usize,
    ) -> Option<Vec<usize>> {
        let mut row_origin = Vec::with_capacity(self.model.num_rows() - n_dropped);
        for r in 0..self.model.num_rows() {
            if self.drop_row[r] {
                continue;
            }
            let lower = match self.row_lower[r].as_ref() {
                None => f64::NEG_INFINITY,
                Some(bound) => as_exact_f64(&(bound - &self.shift[r]))?,
            };
            let upper = match self.row_upper[r].as_ref() {
                None => f64::INFINITY,
                Some(bound) => as_exact_f64(&(bound - &self.shift[r]))?,
            };
            let mut terms = Vec::with_capacity(self.rows[r].len());
            for (column, coefficient, _) in &self.rows[r] {
                if self.fixed[*column].is_none() {
                    terms.push((map[*column]?, *coefficient));
                }
            }
            reduced.add_row(lower, upper, &terms);
            debug_assert_eq!(
                row_origin.len() + 1,
                reduced.num_rows(),
                "row_origin must be indexed by REDUCED row"
            );
            row_origin.push(r);
        }
        Some(row_origin)
    }

    fn emit_objective(&self, reduced: &mut Model, map: &[Option<Col>]) {
        // Calling either setter changes the model from a feasibility problem to
        // an optimization problem. Preserve that verdict-shaping distinction.
        if !self.model.has_objective() {
            return;
        }
        let objective: Vec<(Col, f64)> = (0..self.model.num_cols())
            .filter_map(|j| {
                map[j].and_then(|column| {
                    let coefficient = self.model.obj_coeff(Col(j as u32));
                    (coefficient != 0.0).then_some((column, coefficient))
                })
            })
            .collect();
        reduced.set_objective(&objective, self.model.sense());
        reduced.set_objective_offset(self.model.objective_offset());
    }
}

fn exact_bounds(model: &Model) -> Option<(ExactBounds, ExactBounds)> {
    let mut lower = Vec::with_capacity(model.num_cols());
    let mut upper = Vec::with_capacity(model.num_cols());
    for j in 0..model.num_cols() {
        let (lo, up) = model.col_bounds(Col(j as u32));
        lower.push(if lo.is_finite() {
            Some(exact(lo)?)
        } else {
            None
        });
        upper.push(if up.is_finite() {
            Some(exact(up)?)
        } else {
            None
        });
    }
    Some((lower, upper))
}

fn fixed_columns(model: &Model, lower: &ExactBounds, upper: &ExactBounds) -> Option<ExactBounds> {
    let mut fixed = vec![None; model.num_cols()];
    for j in 0..model.num_cols() {
        if let (Some(lo), Some(up)) = (lower[j].as_ref(), upper[j].as_ref()) {
            if lo == up {
                if model.col_kind(Col(j as u32)).is_integral() && !lo.is_integer() {
                    return None;
                }
                fixed[j] = Some(lo.clone());
            }
        }
    }
    // The downstream engine has no useful all-fixed model shape. Decline and
    // let the caller solve that point directly.
    (!fixed.iter().all(Option::is_some)).then_some(fixed)
}

fn exact_rows(
    model: &Model,
    deadline: Option<Instant>,
) -> Option<(Vec<ExactRow>, ExactBounds, ExactBounds)> {
    let mut rows = Vec::with_capacity(model.num_rows());
    let mut lower = Vec::with_capacity(model.num_rows());
    let mut upper = Vec::with_capacity(model.num_rows());
    for r in 0..model.num_rows() {
        if r % 256 == 0 && expired(deadline) {
            return None;
        }
        let (coefficients, lo, up) = model.row(Row(r as u32));
        let mut terms = Vec::with_capacity(coefficients.len());
        for &(column, coefficient) in coefficients {
            terms.push((column as usize, coefficient, exact(coefficient)?));
        }
        rows.push(terms);
        lower.push(if lo.is_finite() {
            Some(exact(lo)?)
        } else {
            None
        });
        upper.push(if up.is_finite() {
            Some(exact(up)?)
        } else {
            None
        });
    }
    Some((rows, lower, upper))
}

fn row_shift(row: &ExactRow, fixed: &ExactBounds) -> BigRational {
    let mut shift = BigRational::zero();
    for (column, _, coefficient) in row {
        if let Some(value) = fixed[*column].as_ref() {
            shift += coefficient * value;
        }
    }
    shift
}

fn activity(
    terms: &[(usize, BigRational)],
    lower: &ExactBounds,
    upper: &ExactBounds,
) -> (Option<BigRational>, Option<BigRational>) {
    let mut minimum = Some(BigRational::zero());
    let mut maximum = Some(BigRational::zero());
    for (column, coefficient) in terms {
        let (for_minimum, for_maximum) = if coefficient.is_positive() {
            (lower[*column].as_ref(), upper[*column].as_ref())
        } else {
            (upper[*column].as_ref(), lower[*column].as_ref())
        };
        minimum = match (minimum, for_minimum) {
            (Some(current), Some(bound)) => Some(current + coefficient * bound),
            _ => None,
        };
        maximum = match (maximum, for_maximum) {
            (Some(current), Some(bound)) => Some(current + coefficient * bound),
            _ => None,
        };
    }
    (minimum, maximum)
}

fn expired(deadline: Option<Instant>) -> bool {
    deadline.is_some_and(|deadline| Instant::now() >= deadline)
}

/// Delete fixed columns and redundant rows. `None` = nothing eliminated, or any
/// doubt; the caller then solves its own model untouched.
pub(crate) fn eliminate_structure(
    model: &Model,
    deadline: Option<Instant>,
) -> Option<(Model, StructurePostsolve)> {
    if model.has_inexact_coeffs()
        || model.has_inexact_objective_coeffs()
        || model.margin_row().is_some()
        || expired(deadline)
    {
        return None;
    }
    let mut reduction = Reduction::prepare(model, deadline)?;
    reduction.stabilize_shifts(deadline)?;
    reduction.classify_rows(deadline)?;
    let (n_fixed, n_dropped) = reduction.reduction_counts()?;
    let (mut reduced, map, recover, const_delta) = reduction.build_columns(model, n_fixed)?;
    let row_origin = reduction.emit_rows(&mut reduced, &map, n_dropped)?;
    reduction.emit_objective(&mut reduced, &map);
    let postsolve = StructurePostsolve {
        n_orig: reduction.model.num_cols(),
        map,
        recover,
        row_origin,
        const_delta,
    };
    debug_assert_eq!(postsolve.row_origin.len(), reduced.num_rows());
    Some((reduced, postsolve))
}
