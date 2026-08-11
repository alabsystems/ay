// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Exact handling for structurally open general-integer domains.
//!
//! Two different equivalences live here and are deliberately kept distinct.
//!
//! 1. [`MonotoneProjection`] removes an open integer that occurs only in
//!    one-sided rows which moving farther into its open direction can only
//!    satisfy.  Those rows are existentially true for every assignment of the
//!    retained columns.  A residual feasible point is lifted by choosing finite
//!    integer values large enough to satisfy the removed rows.  This preserves
//!    **feasibility**, including infeasibility, without an incumbent.
//! 2. [`ObjectiveCapPlan`] starts from an exact, original-model-checked
//!    incumbent.  The incumbent objective is installed as a propagation-only
//!    cutoff, and exact interval propagation derives finite representative
//!    domains.  Such caps preserve every point at least as good as the
//!    incumbent, hence preserve the optimum, but they do **not** preserve all
//!    suboptimal feasible points.  In particular, cutoff infeasibility proves
//!    optimality, never original infeasibility.
//!
//! Neither construction recognizes names or dimensions.  Exact row/objective
//! side stores are authoritative, every derived integer endpoint is installed
//! only when exactly representable by the model's `f64` column-bound surface,
//! and all returned points are checked against the original model.

use std::time::Instant;

use num_bigint::BigInt;
use num_integer::Integer;
use num_rational::BigRational;
use num_traits::{One, Signed, ToPrimitive, Zero};

use crate::model::{exact, Col, ColKind, Model, Row, Sense};

const MAX_COLUMNS: usize = 8_192;
const MAX_ROWS: usize = 8_192;
const MAX_TERMS: usize = 250_000;
const MAX_TERMS_PER_ROW: usize = 8_192;
const MAX_SWEEPS: usize = 16;
const MAX_RATIONAL_BITS: u64 = 4_096;
const MAX_LIFTED_INTEGER_BITS: u64 = 16_384;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum OpenDomainDecline {
    Deadline,
    InvalidModel,
    ResourceLimit,
    NoOpenInteger,
    NonMonotoneOpenInteger,
    InvalidIncumbent,
    NoObjectiveCap,
    AdviceRange,
    ExactCheck,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum OpenDirection {
    Increase,
    Decrease,
}

impl OpenDirection {
    fn sign(self) -> BigRational {
        match self {
            Self::Increase => BigRational::one(),
            Self::Decrease => -BigRational::one(),
        }
    }

    fn apply(self, anchor: &BigInt, step: &BigInt) -> BigInt {
        match self {
            Self::Increase => anchor + step,
            Self::Decrease => anchor - step,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct EliminatedColumn {
    source: Col,
    anchor: BigInt,
    direction: OpenDirection,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum LiftSide {
    Lower,
    Upper,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct LiftRow {
    source: Row,
    driver: Col,
    direction: OpenDirection,
    side: LiftSide,
    help: BigRational,
}

/// Exact existential projection of monotone open integer columns.
///
/// The residual model is a feasibility model even when the source optimizes.
/// Residual infeasibility is equivalent to source infeasibility.  Residual
/// feasibility must go through [`Self::checked_lift`] before it is used as an
/// incumbent for the source optimization problem.
pub(crate) struct MonotoneProjection {
    residual: Model,
    source_to_residual: Vec<Option<Col>>,
    eliminated: Vec<EliminatedColumn>,
    lift_rows: Vec<LiftRow>,
}

impl MonotoneProjection {
    pub(crate) fn try_build<F>(
        source: &Model,
        deadline: Option<Instant>,
        mut should_stop: F,
    ) -> Result<Self, OpenDomainDecline>
    where
        F: FnMut() -> bool,
    {
        source
            .validate()
            .map_err(|_| OpenDomainDecline::InvalidModel)?;
        preflight(source, deadline, &mut should_stop)?;

        let mut eliminated = Vec::new();
        let mut by_column = vec![None; source.num_cols()];
        for column in 0..source.num_cols() {
            if column & 0x3ff == 0 && stopped(deadline, &mut should_stop) {
                return Err(OpenDomainDecline::Deadline);
            }
            let col = Col(column as u32);
            if !matches!(source.col_kind(col), ColKind::Integer) {
                continue;
            }
            let (lb, ub) = source.col_bounds(col);
            let lower = exact(lb);
            let upper = exact(ub);
            let (anchor, direction) = match (lower, upper) {
                (Some(lower), None) => (
                    lower.numer().div_ceil(lower.denom()),
                    OpenDirection::Increase,
                ),
                (None, Some(upper)) => (
                    upper.numer().div_floor(upper.denom()),
                    OpenDirection::Decrease,
                ),
                (None, None) => return Err(OpenDomainDecline::NonMonotoneOpenInteger),
                (Some(_), Some(_)) => continue,
            };
            if anchor.bits() > MAX_LIFTED_INTEGER_BITS {
                return Err(OpenDomainDecline::ResourceLimit);
            }
            by_column[column] = Some(eliminated.len());
            eliminated.push(EliminatedColumn {
                source: col,
                anchor,
                direction,
            });
        }
        if eliminated.is_empty() {
            return Err(OpenDomainDecline::NoOpenInteger);
        }

        let mut lift_rows = Vec::new();
        let mut dropped = vec![false; source.num_rows()];
        for row_index in 0..source.num_rows() {
            if row_index & 0xff == 0 && stopped(deadline, &mut should_stop) {
                return Err(OpenDomainDecline::Deadline);
            }
            let (terms, lb, ub) = source.row(Row(row_index as u32));
            let lower = source.row_lb_exact(row_index, lb);
            let upper = source.row_ub_exact(row_index, ub);
            let mut best: Option<(usize, BigRational)> = None;
            for &(column, advice) in terms {
                let Some(eliminated_index) = by_column[column as usize] else {
                    continue;
                };
                let coefficient = source.row_coeff_exact(row_index, column, advice);
                let effective = coefficient * eliminated[eliminated_index].direction.sign();
                let favorable = match (&lower, &upper) {
                    (Some(_), None) => effective.is_positive(),
                    (None, Some(_)) => effective.is_negative(),
                    _ => false,
                };
                if !favorable {
                    return Err(OpenDomainDecline::NonMonotoneOpenInteger);
                }
                let help = effective.abs();
                if !rational_fits(&help) {
                    return Err(OpenDomainDecline::ResourceLimit);
                }
                if best.as_ref().is_none_or(|(_, old)| &help > old) {
                    best = Some((eliminated_index, help));
                }
            }
            let Some((driver, help)) = best else {
                continue;
            };
            dropped[row_index] = true;
            lift_rows.push(LiftRow {
                source: Row(row_index as u32),
                driver: eliminated[driver].source,
                direction: eliminated[driver].direction,
                side: if lower.is_some() {
                    LiftSide::Lower
                } else {
                    LiftSide::Upper
                },
                help,
            });
        }

        // A column with no row occurrence is also existentially removable: its
        // finite anchor is a witness.  Every column with an occurrence was
        // checked above, so no harmful occurrence can hide in a retained row.
        let mut residual = Model::new();
        residual.inherit_ft_adoption_solve_latch(source);
        let mut source_to_residual = vec![None; source.num_cols()];
        for column in 0..source.num_cols() {
            if by_column[column].is_some() {
                continue;
            }
            let source_col = Col(column as u32);
            let (lb, ub) = source.col_bounds(source_col);
            let target = match source.col_kind(source_col) {
                ColKind::Continuous => residual.add_col(lb, ub),
                ColKind::Integer => residual.add_int_col(lb, ub),
                ColKind::Binary => {
                    let target = residual.add_binary_col();
                    residual.set_col_bounds(target, lb, ub);
                    target
                }
            };
            source_to_residual[column] = Some(target);
        }

        for (row_index, &is_dropped) in dropped.iter().enumerate() {
            if is_dropped {
                continue;
            }
            if row_index & 0xff == 0 && stopped(deadline, &mut should_stop) {
                return Err(OpenDomainDecline::Deadline);
            }
            copy_exact_row(source, row_index, &source_to_residual, &mut residual)?;
        }

        let projection = Self {
            residual,
            source_to_residual,
            eliminated,
            lift_rows,
        };
        projection.check_shape(source)?;
        Ok(projection)
    }

    pub(crate) fn residual(&self) -> &Model {
        &self.residual
    }

    /// Lift and independently check a residual feasible point.
    pub(crate) fn checked_lift<F>(
        &self,
        source: &Model,
        residual_values: &[BigRational],
        deadline: Option<Instant>,
        mut should_stop: F,
    ) -> Option<Vec<BigRational>>
    where
        F: FnMut() -> bool,
    {
        self.residual.check_point(residual_values).ok()?;
        if residual_values.len() != self.residual.num_cols() {
            return None;
        }
        let mut values = vec![BigRational::zero(); source.num_cols()];
        for (column, target) in self.source_to_residual.iter().enumerate() {
            if let Some(target) = target {
                values[column] = residual_values.get(target.index())?.clone();
            }
        }
        for eliminated in &self.eliminated {
            values[eliminated.source.index()] =
                BigRational::from_integer(eliminated.anchor.clone());
        }

        for (row_number, lift) in self.lift_rows.iter().enumerate() {
            if row_number & 0xff == 0 && stopped(deadline, &mut should_stop) {
                return None;
            }
            let activity = row_activity(source, lift.source, &values)?;
            let (_, lb, ub) = source.row(lift.source);
            let required = match lift.side {
                LiftSide::Lower => {
                    let lower = source.row_lb_exact(lift.source.index(), lb)?;
                    if activity >= lower {
                        continue;
                    }
                    lower - activity
                }
                LiftSide::Upper => {
                    let upper = source.row_ub_exact(lift.source.index(), ub)?;
                    if activity <= upper {
                        continue;
                    }
                    activity - upper
                }
            };
            let quotient = &required / &lift.help;
            let step = quotient.numer().div_ceil(quotient.denom());
            if step.is_negative() || step.bits() > MAX_LIFTED_INTEGER_BITS {
                return None;
            }
            let current = values[lift.driver.index()].to_integer();
            let updated = lift.direction.apply(&current, &step);
            if updated.bits() > MAX_LIFTED_INTEGER_BITS {
                return None;
            }
            values[lift.driver.index()] = BigRational::from_integer(updated);
        }

        source.check_point(&values).ok()?;
        Some(values)
    }

    /// Re-run recognition before promoting a residual infeasibility verdict.
    pub(crate) fn revalidate<F>(
        &self,
        source: &Model,
        deadline: Option<Instant>,
        should_stop: F,
    ) -> bool
    where
        F: FnMut() -> bool,
    {
        let Ok(other) = Self::try_build(source, deadline, should_stop) else {
            return false;
        };
        self.source_to_residual == other.source_to_residual
            && self.eliminated == other.eliminated
            && self.lift_rows == other.lift_rows
            && exact_models_equal(&self.residual, &other.residual)
    }

    fn check_shape(&self, source: &Model) -> Result<(), OpenDomainDecline> {
        if self.source_to_residual.len() != source.num_cols()
            || self.eliminated.is_empty()
            || self.residual.has_objective()
        {
            return Err(OpenDomainDecline::ExactCheck);
        }
        for eliminated in &self.eliminated {
            if self.source_to_residual[eliminated.source.index()].is_some() {
                return Err(OpenDomainDecline::ExactCheck);
            }
        }
        for column in 0..self.residual.num_cols() {
            let col = Col(column as u32);
            if self.residual.col_kind(col).is_integral() {
                let (lb, ub) = self.residual.col_bounds(col);
                if !lb.is_finite() || !ub.is_finite() {
                    return Err(OpenDomainDecline::ExactCheck);
                }
            }
        }
        Ok(())
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct InstalledCap {
    column: Col,
    lower: BigInt,
    upper: BigInt,
}

/// A clone of the original model with exact finite domains on every originally
/// open integer, derived under a checked incumbent objective cutoff.
pub(crate) struct ObjectiveCapPlan {
    bounded: Model,
    incumbent: Vec<BigRational>,
    incumbent_objective: BigRational,
    caps: Vec<InstalledCap>,
}

impl ObjectiveCapPlan {
    pub(crate) fn try_build<F>(
        source: &Model,
        incumbent: &[BigRational],
        deadline: Option<Instant>,
        mut should_stop: F,
    ) -> Result<Self, OpenDomainDecline>
    where
        F: FnMut() -> bool,
    {
        source
            .validate()
            .map_err(|_| OpenDomainDecline::InvalidModel)?;
        preflight(source, deadline, &mut should_stop)?;
        if !source.has_objective()
            || incumbent.len() != source.num_cols()
            || source.check_point(incumbent).is_err()
        {
            return Err(OpenDomainDecline::InvalidIncumbent);
        }
        let incumbent_objective = source.objective_value_at(incumbent);
        if !rational_fits(&incumbent_objective) {
            return Err(OpenDomainDecline::ResourceLimit);
        }

        let initial_open: Vec<usize> = (0..source.num_cols())
            .filter(|&column| {
                let col = Col(column as u32);
                source.col_kind(col).is_integral() && {
                    let (lb, ub) = source.col_bounds(col);
                    !lb.is_finite() || !ub.is_finite()
                }
            })
            .collect();
        if initial_open.is_empty() {
            return Err(OpenDomainDecline::NoOpenInteger);
        }

        let propagated =
            propagate_with_cutoff(source, &incumbent_objective, deadline, &mut should_stop)?;
        let mut bounded = source.clone();
        let mut caps = Vec::with_capacity(initial_open.len());
        for column in initial_open {
            let exact_lower = propagated.lower[column]
                .as_ref()
                .ok_or(OpenDomainDecline::NoObjectiveCap)?;
            let exact_upper = propagated.upper[column]
                .as_ref()
                .ok_or(OpenDomainDecline::NoObjectiveCap)?;
            let lower = exact_lower.numer().div_ceil(exact_lower.denom());
            let upper = exact_upper.numer().div_floor(exact_upper.denom());
            if lower > upper {
                return Err(OpenDomainDecline::ExactCheck);
            }
            let lower_advice = integer_advice(&lower).ok_or(OpenDomainDecline::AdviceRange)?;
            let upper_advice = integer_advice(&upper).ok_or(OpenDomainDecline::AdviceRange)?;
            bounded.set_col_bounds(Col(column as u32), lower_advice, upper_advice);
            caps.push(InstalledCap {
                column: Col(column as u32),
                lower,
                upper,
            });
        }
        if bounded.check_point(incumbent).is_err()
            || bounded.objective_value_at(incumbent) != incumbent_objective
        {
            return Err(OpenDomainDecline::ExactCheck);
        }
        Ok(Self {
            bounded,
            incumbent: incumbent.to_vec(),
            incumbent_objective,
            caps,
        })
    }

    pub(crate) fn bounded(&self) -> &Model {
        &self.bounded
    }

    pub(crate) fn incumbent(&self) -> &[BigRational] {
        &self.incumbent
    }

    /// Validate any bounded-model point in the original model and rederive its
    /// exact objective.  This is required before returning an incumbent.
    pub(crate) fn checked_original_point(
        &self,
        source: &Model,
        values: &[BigRational],
    ) -> Option<BigRational> {
        self.bounded.check_point(values).ok()?;
        source.check_point(values).ok()?;
        let bounded_value = self.bounded.objective_value_at(values);
        let source_value = source.objective_value_at(values);
        (bounded_value == source_value).then_some(source_value)
    }

    /// Re-derive every cap before promoting transformed optimality.
    pub(crate) fn revalidate<F>(
        &self,
        source: &Model,
        deadline: Option<Instant>,
        should_stop: F,
    ) -> bool
    where
        F: FnMut() -> bool,
    {
        let Ok(other) = Self::try_build(source, &self.incumbent, deadline, should_stop) else {
            return false;
        };
        self.incumbent_objective == other.incumbent_objective
            && self.caps == other.caps
            && exact_models_equal(&self.bounded, &other.bounded)
    }
}

struct PropagatedBounds {
    lower: Vec<Option<BigRational>>,
    upper: Vec<Option<BigRational>>,
}

#[derive(Clone)]
struct ExactConstraint {
    terms: Vec<(usize, BigRational)>,
    lower: Option<BigRational>,
    upper: Option<BigRational>,
}

fn propagate_with_cutoff<F>(
    model: &Model,
    incumbent_objective: &BigRational,
    deadline: Option<Instant>,
    should_stop: &mut F,
) -> Result<PropagatedBounds, OpenDomainDecline>
where
    F: FnMut() -> bool,
{
    let integral: Vec<bool> = (0..model.num_cols())
        .map(|column| model.col_kind(Col(column as u32)).is_integral())
        .collect();
    let mut lower = Vec::with_capacity(model.num_cols());
    let mut upper = Vec::with_capacity(model.num_cols());
    for (column, &is_integral) in integral.iter().enumerate() {
        let (lb, ub) = model.col_bounds(Col(column as u32));
        let mut lo = exact(lb);
        let mut hi = exact(ub);
        if is_integral {
            lo = lo.map(|value| BigRational::from_integer(value.numer().div_ceil(value.denom())));
            hi = hi.map(|value| BigRational::from_integer(value.numer().div_floor(value.denom())));
        }
        if lo.as_ref().is_some_and(|v| !rational_fits(v))
            || hi.as_ref().is_some_and(|v| !rational_fits(v))
            || matches!((&lo, &hi), (Some(lo), Some(hi)) if lo > hi)
        {
            return Err(OpenDomainDecline::ResourceLimit);
        }
        lower.push(lo);
        upper.push(hi);
    }

    let mut constraints = Vec::with_capacity(model.num_rows() + 1);
    for row_index in 0..model.num_rows() {
        let (terms, lb, ub) = model.row(Row(row_index as u32));
        let mut exact_terms = Vec::with_capacity(terms.len());
        for &(column, advice) in terms {
            let coefficient = model.row_coeff_exact(row_index, column, advice);
            if !rational_fits(&coefficient) {
                return Err(OpenDomainDecline::ResourceLimit);
            }
            if !coefficient.is_zero() {
                exact_terms.push((column as usize, coefficient));
            }
        }
        constraints.push(ExactConstraint {
            terms: exact_terms,
            lower: model.row_lb_exact(row_index, lb),
            upper: model.row_ub_exact(row_index, ub),
        });
    }
    let mut objective_terms = Vec::new();
    for column in 0..model.num_cols() {
        let col = Col(column as u32);
        let coefficient = model.obj_coeff_exact_at(column as u32, model.obj_coeff(col));
        if !rational_fits(&coefficient) {
            return Err(OpenDomainDecline::ResourceLimit);
        }
        if !coefficient.is_zero() {
            objective_terms.push((column, coefficient));
        }
    }
    let cutoff = incumbent_objective - model.obj_offset_exact();
    if !rational_fits(&cutoff) {
        return Err(OpenDomainDecline::ResourceLimit);
    }
    constraints.push(match model.sense() {
        Sense::Minimize => ExactConstraint {
            terms: objective_terms,
            lower: None,
            upper: Some(cutoff),
        },
        Sense::Maximize => ExactConstraint {
            terms: objective_terms,
            lower: Some(cutoff),
            upper: None,
        },
    });

    for _ in 0..MAX_SWEEPS {
        let mut changed = false;
        for (constraint_index, constraint) in constraints.iter().enumerate() {
            if constraint_index & 0xff == 0 && stopped(deadline, should_stop) {
                return Err(OpenDomainDecline::Deadline);
            }
            let (min_activity, min_open) =
                activity_bound(&constraint.terms, &lower, &upper, ActivitySide::Minimum)?;
            let (max_activity, max_open) =
                activity_bound(&constraint.terms, &lower, &upper, ActivitySide::Maximum)?;
            for (term_index, &(column, ref coefficient)) in constraint.terms.iter().enumerate() {
                if term_index & 0x3ff == 0 && stopped(deadline, should_stop) {
                    return Err(OpenDomainDecline::Deadline);
                }
                let at_min = if coefficient.is_positive() {
                    &lower[column]
                } else {
                    &upper[column]
                };
                let at_max = if coefficient.is_positive() {
                    &upper[column]
                } else {
                    &lower[column]
                };
                let rest_min = remove_activity(&min_activity, min_open, at_min, coefficient)?;
                let rest_max = remove_activity(&max_activity, max_open, at_max, coefficient)?;
                if let (Some(side), Some(rest)) = (&constraint.upper, rest_min) {
                    let candidate = checked_ratio(side - rest, coefficient)?;
                    changed |= if coefficient.is_positive() {
                        tighten_bound(&mut upper[column], candidate, false, integral[column])?
                    } else {
                        tighten_bound(&mut lower[column], candidate, true, integral[column])?
                    };
                }
                if let (Some(side), Some(rest)) = (&constraint.lower, rest_max) {
                    let candidate = checked_ratio(side - rest, coefficient)?;
                    changed |= if coefficient.is_positive() {
                        tighten_bound(&mut lower[column], candidate, true, integral[column])?
                    } else {
                        tighten_bound(&mut upper[column], candidate, false, integral[column])?
                    };
                }
                if matches!((&lower[column], &upper[column]), (Some(lo), Some(hi)) if lo > hi) {
                    return Err(OpenDomainDecline::ExactCheck);
                }
            }
        }
        if !changed {
            break;
        }
    }
    Ok(PropagatedBounds { lower, upper })
}

#[derive(Clone, Copy)]
enum ActivitySide {
    Minimum,
    Maximum,
}

fn activity_bound(
    terms: &[(usize, BigRational)],
    lower: &[Option<BigRational>],
    upper: &[Option<BigRational>],
    side: ActivitySide,
) -> Result<(BigRational, usize), OpenDomainDecline> {
    let mut activity = BigRational::zero();
    let mut open = 0usize;
    for &(column, ref coefficient) in terms {
        let bound = match (side, coefficient.is_positive()) {
            (ActivitySide::Minimum, true) | (ActivitySide::Maximum, false) => &lower[column],
            (ActivitySide::Minimum, false) | (ActivitySide::Maximum, true) => &upper[column],
        };
        if let Some(bound) = bound {
            activity += coefficient * bound;
            if !rational_fits(&activity) {
                return Err(OpenDomainDecline::ResourceLimit);
            }
        } else {
            open = open
                .checked_add(1)
                .ok_or(OpenDomainDecline::ResourceLimit)?;
        }
    }
    Ok((activity, open))
}

fn remove_activity(
    activity: &BigRational,
    open: usize,
    own_bound: &Option<BigRational>,
    coefficient: &BigRational,
) -> Result<Option<BigRational>, OpenDomainDecline> {
    match (open, own_bound) {
        (0, Some(bound)) => {
            checked_ratio(activity - coefficient * bound, &BigRational::one()).map(Some)
        }
        (1, None) => Ok(Some(activity.clone())),
        _ => Ok(None),
    }
}

fn tighten_bound(
    side: &mut Option<BigRational>,
    candidate: BigRational,
    lower: bool,
    integral: bool,
) -> Result<bool, OpenDomainDecline> {
    let candidate = if integral {
        let value = if lower {
            candidate.numer().div_ceil(candidate.denom())
        } else {
            candidate.numer().div_floor(candidate.denom())
        };
        BigRational::from_integer(value)
    } else {
        candidate
    };
    if !rational_fits(&candidate) {
        return Err(OpenDomainDecline::ResourceLimit);
    }
    let better = side.as_ref().is_none_or(|old| {
        if lower {
            &candidate > old
        } else {
            &candidate < old
        }
    });
    if better {
        *side = Some(candidate);
    }
    Ok(better)
}

fn copy_exact_row(
    source: &Model,
    row_index: usize,
    map: &[Option<Col>],
    target: &mut Model,
) -> Result<(), OpenDomainDecline> {
    let (terms, lb, ub) = source.row(Row(row_index as u32));
    let mut stored = Vec::with_capacity(terms.len());
    let mut exact_terms = Vec::with_capacity(terms.len());
    for &(column, advice) in terms {
        let target_column = map[column as usize].ok_or(OpenDomainDecline::ExactCheck)?;
        stored.push((target_column, advice));
        exact_terms.push((
            target_column.0,
            source.row_coeff_exact(row_index, column, advice),
            advice,
        ));
    }
    let row = target.add_row(lb, ub, &stored);
    for (column, value, advice) in exact_terms {
        if exact(advice).as_ref() != Some(&value) {
            target.record_inexact_row_coeff(row, column, value);
        }
    }
    if let Some(value) = source.row_lb_exact(row_index, lb) {
        if exact(lb).as_ref() != Some(&value) {
            target.record_inexact_row_bound(row, true, value);
        }
    }
    if let Some(value) = source.row_ub_exact(row_index, ub) {
        if exact(ub).as_ref() != Some(&value) {
            target.record_inexact_row_bound(row, false, value);
        }
    }
    Ok(())
}

fn row_activity(model: &Model, row: Row, values: &[BigRational]) -> Option<BigRational> {
    let (terms, _, _) = model.row(row);
    let mut activity = BigRational::zero();
    for &(column, advice) in terms {
        activity += model.row_coeff_exact(row.index(), column, advice) * &values[column as usize];
        if !rational_fits_lift(&activity) {
            return None;
        }
    }
    Some(activity)
}

fn preflight<F>(
    model: &Model,
    deadline: Option<Instant>,
    should_stop: &mut F,
) -> Result<(), OpenDomainDecline>
where
    F: FnMut() -> bool,
{
    if stopped(deadline, should_stop) {
        return Err(OpenDomainDecline::Deadline);
    }
    if model.num_cols() > MAX_COLUMNS || model.num_rows() > MAX_ROWS {
        return Err(OpenDomainDecline::ResourceLimit);
    }
    let terms = model.rows.iter().try_fold(0usize, |total, row| {
        (row.coeffs.len() <= MAX_TERMS_PER_ROW)
            .then(|| total.checked_add(row.coeffs.len()))
            .flatten()
    });
    if terms.is_none_or(|terms| terms > MAX_TERMS) {
        return Err(OpenDomainDecline::ResourceLimit);
    }
    Ok(())
}

fn exact_models_equal(left: &Model, right: &Model) -> bool {
    if left.num_cols() != right.num_cols()
        || left.num_rows() != right.num_rows()
        || left.has_objective() != right.has_objective()
        || left.sense() != right.sense()
        || left.obj_offset_exact() != right.obj_offset_exact()
    {
        return false;
    }
    for column in 0..left.num_cols() {
        let col = Col(column as u32);
        let left_objective = left.obj_coeff_exact_at(column as u32, left.obj_coeff(col));
        let right_objective = right.obj_coeff_exact_at(column as u32, right.obj_coeff(col));
        if left.col_kind(col) != right.col_kind(col)
            || left.col_bounds(col) != right.col_bounds(col)
            || left_objective != right_objective
        {
            return false;
        }
    }
    for row_index in 0..left.num_rows() {
        let row = Row(row_index as u32);
        let (left_terms, left_lb, left_ub) = left.row(row);
        let (right_terms, right_lb, right_ub) = right.row(row);
        let left_lower = left.row_lb_exact(row_index, left_lb);
        let right_lower = right.row_lb_exact(row_index, right_lb);
        let left_upper = left.row_ub_exact(row_index, left_ub);
        let right_upper = right.row_ub_exact(row_index, right_ub);
        if left_terms.len() != right_terms.len()
            || left_lower != right_lower
            || left_upper != right_upper
        {
            return false;
        }
        for (&(lc, la), &(rc, ra)) in left_terms.iter().zip(right_terms) {
            if lc != rc
                || left.row_coeff_exact(row_index, lc, la)
                    != right.row_coeff_exact(row_index, rc, ra)
            {
                return false;
            }
        }
    }
    true
}

fn checked_ratio(
    numerator: BigRational,
    denominator: &BigRational,
) -> Result<BigRational, OpenDomainDecline> {
    if denominator.is_zero() {
        return Err(OpenDomainDecline::ExactCheck);
    }
    let value = numerator / denominator;
    if rational_fits(&value) {
        Ok(value)
    } else {
        Err(OpenDomainDecline::ResourceLimit)
    }
}

fn integer_advice(value: &BigInt) -> Option<f64> {
    let advice = value.to_f64()?;
    if !advice.is_finite() {
        return None;
    }
    (exact(advice)? == BigRational::from_integer(value.clone())).then_some(advice)
}

fn rational_fits(value: &BigRational) -> bool {
    value.numer().bits() <= MAX_RATIONAL_BITS && value.denom().bits() <= MAX_RATIONAL_BITS
}

fn rational_fits_lift(value: &BigRational) -> bool {
    value.numer().bits() <= MAX_LIFTED_INTEGER_BITS && value.denom().bits() <= MAX_RATIONAL_BITS
}

fn stopped<F>(deadline: Option<Instant>, should_stop: &mut F) -> bool
where
    F: FnMut() -> bool,
{
    should_stop() || deadline.is_some_and(|deadline| Instant::now() >= deadline)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn i(value: i64) -> BigRational {
        BigRational::from_integer(value.into())
    }

    #[test]
    fn monotone_lower_cover_projects_and_lifts_exactly() {
        let mut model = Model::new();
        let choose = model.add_binary_col();
        let fill = model.add_int_col(2.0, f64::INFINITY);
        model.add_row(7.0, f64::INFINITY, &[(choose, 3.0), (fill, 2.0)]);
        model.set_objective(&[(fill, 1.0)], Sense::Minimize);

        let projection = MonotoneProjection::try_build(&model, None, || false).unwrap();
        assert_eq!(projection.residual().num_cols(), 1);
        assert_eq!(projection.residual().num_rows(), 0);
        assert!(!projection.residual().has_objective());
        let lifted = projection
            .checked_lift(&model, &[i(0)], None, || false)
            .expect("finite exact lift");
        assert_eq!(lifted[fill.index()], i(4));
        model.check_point(&lifted).unwrap();
        assert!(projection.revalidate(&model, None, || false));
    }

    #[test]
    fn monotone_upper_row_and_open_lower_are_symmetric() {
        let mut model = Model::new();
        let keep = model.add_binary_col();
        let fill = model.add_int_col(f64::NEG_INFINITY, 5.0);
        // Decreasing fill decreases this upper-row activity and cannot hurt.
        model.add_row(f64::NEG_INFINITY, -3.0, &[(keep, 1.0), (fill, 2.0)]);

        let projection = MonotoneProjection::try_build(&model, None, || false).unwrap();
        let lifted = projection
            .checked_lift(&model, &[i(1)], None, || false)
            .unwrap();
        assert_eq!(lifted[fill.index()], i(-2));
        model.check_point(&lifted).unwrap();
    }

    #[test]
    fn coupled_monotone_rows_never_harm_a_previous_lift() {
        let mut model = Model::new();
        let a = model.add_int_col(0.0, f64::INFINITY);
        let b = model.add_int_col(0.0, f64::INFINITY);
        model.add_row(5.0, f64::INFINITY, &[(a, 1.0), (b, 1.0)]);
        model.add_row(9.0, f64::INFINITY, &[(a, 2.0), (b, 1.0)]);

        let projection = MonotoneProjection::try_build(&model, None, || false).unwrap();
        let lifted = projection
            .checked_lift(&model, &[], None, || false)
            .unwrap();
        model.check_point(&lifted).unwrap();
    }

    #[test]
    fn harmful_or_two_sided_occurrence_declines() {
        let mut harmful = Model::new();
        let x = harmful.add_int_col(0.0, f64::INFINITY);
        harmful.add_row(f64::NEG_INFINITY, 2.0, &[(x, 1.0)]);
        assert!(matches!(
            MonotoneProjection::try_build(&harmful, None, || false),
            Err(OpenDomainDecline::NonMonotoneOpenInteger)
        ));

        let mut ranged = Model::new();
        let x = ranged.add_int_col(0.0, f64::INFINITY);
        ranged.add_row(1.0, 2.0, &[(x, 1.0)]);
        assert!(matches!(
            MonotoneProjection::try_build(&ranged, None, || false),
            Err(OpenDomainDecline::NonMonotoneOpenInteger)
        ));
    }

    #[test]
    fn occurrence_free_open_integer_uses_its_finite_anchor() {
        let mut model = Model::new();
        let x = model.add_int_col(3.2, f64::INFINITY);
        let projection = MonotoneProjection::try_build(&model, None, || false).unwrap();
        let lifted = projection
            .checked_lift(&model, &[], None, || false)
            .unwrap();
        assert_eq!(lifted[x.index()], i(4));
    }

    #[test]
    fn direct_positive_objective_caps_an_open_integer() {
        let mut model = Model::new();
        let x = model.add_int_col(0.0, f64::INFINITY);
        model.set_objective(&[(x, 3.0)], Sense::Minimize);
        let incumbent = vec![i(7)];

        let plan = ObjectiveCapPlan::try_build(&model, &incumbent, None, || false).unwrap();
        assert_eq!(plan.bounded().col_bounds(x), (0.0, 7.0));
        assert_eq!(plan.incumbent(), incumbent);
        assert_eq!(plan.checked_original_point(&model, &incumbent), Some(i(21)));
        assert!(plan.revalidate(&model, None, || false));
    }

    #[test]
    fn objective_cutoff_propagates_through_zero_cost_open_integer() {
        let mut model = Model::new();
        let component = model.add_col(0.0, f64::INFINITY);
        let aggregate_component = model.add_col(f64::NEG_INFINITY, f64::INFINITY);
        let aggregate_integer = model.add_col(f64::NEG_INFINITY, f64::INFINITY);
        let open_integer = model.add_int_col(4.0, f64::INFINITY);
        model.add_row(
            f64::NEG_INFINITY,
            3.0,
            &[(component, -1.0), (open_integer, 1.0)],
        );
        model.add_row(
            f64::NEG_INFINITY,
            0.0,
            &[(component, 1.0), (aggregate_component, -1.0)],
        );
        model.add_row(
            f64::NEG_INFINITY,
            10.0,
            &[(open_integer, 1.0), (aggregate_integer, -1.0)],
        );
        model.set_objective(
            &[(aggregate_component, 1.0), (aggregate_integer, 1.0)],
            Sense::Minimize,
        );
        let incumbent = vec![i(2), i(2), i(-5), i(5)];
        model.check_point(&incumbent).unwrap();

        let plan = ObjectiveCapPlan::try_build(&model, &incumbent, None, || false).unwrap();
        let (_, upper) = plan.bounded().col_bounds(open_integer);
        assert!(upper.is_finite());
        assert!(upper >= 5.0);
    }

    #[test]
    fn maximum_open_lower_cap_is_symmetric() {
        let mut model = Model::new();
        let x = model.add_int_col(f64::NEG_INFINITY, 10.0);
        model.set_objective(&[(x, 2.0)], Sense::Maximize);
        let incumbent = vec![i(3)];

        let plan = ObjectiveCapPlan::try_build(&model, &incumbent, None, || false).unwrap();
        assert_eq!(plan.bounded().col_bounds(x), (3.0, 10.0));
    }

    #[test]
    fn cap_requires_an_original_checked_incumbent() {
        let mut model = Model::new();
        let x = model.add_int_col(0.0, f64::INFINITY);
        model.add_row(2.0, f64::INFINITY, &[(x, 1.0)]);
        model.set_objective(&[(x, 1.0)], Sense::Minimize);
        assert!(matches!(
            ObjectiveCapPlan::try_build(&model, &[i(1)], None, || false),
            Err(OpenDomainDecline::InvalidIncumbent)
        ));
    }

    #[test]
    fn cap_preserves_every_enumerated_point_at_least_as_good_as_incumbent() {
        let mut model = Model::new();
        let x = model.add_int_col(0.0, f64::INFINITY);
        let y = model.add_int_col(0.0, 4.0);
        model.add_row(2.0, f64::INFINITY, &[(x, 1.0), (y, 1.0)]);
        model.set_objective(&[(x, 2.0), (y, 1.0)], Sense::Minimize);
        let incumbent = vec![i(3), i(1)];
        let plan = ObjectiveCapPlan::try_build(&model, &incumbent, None, || false).unwrap();
        let incumbent_value = model.objective_value_at(&incumbent);

        for xv in 0..=12 {
            for yv in 0..=4 {
                let point = vec![i(xv), i(yv)];
                if model.check_point(&point).is_ok()
                    && model.objective_value_at(&point) <= incumbent_value
                {
                    plan.bounded().check_point(&point).unwrap();
                }
            }
        }
    }

    #[test]
    fn exact_side_store_is_copied_to_projected_rows() {
        let mut model = Model::new();
        let kept = model.add_binary_col();
        let open = model.add_int_col(0.0, f64::INFINITY);
        let retained = model.add_row(0.1, f64::INFINITY, &[(kept, 0.1)]);
        model.record_inexact_row_coeff(retained, kept.0, BigRational::new(1.into(), 3.into()));
        model.record_inexact_row_bound(retained, true, BigRational::new(1.into(), 3.into()));
        model.add_row(2.0, f64::INFINITY, &[(open, 1.0)]);

        let projection = MonotoneProjection::try_build(&model, None, || false).unwrap();
        let (terms, lb, _) = projection.residual().row(Row(0));
        assert_eq!(
            projection
                .residual()
                .row_coeff_exact(0, terms[0].0, terms[0].1),
            BigRational::new(1.into(), 3.into())
        );
        assert_eq!(
            projection.residual().row_lb_exact(0, lb),
            Some(BigRational::new(1.into(), 3.into()))
        );
    }
}
