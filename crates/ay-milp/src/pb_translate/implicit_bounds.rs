// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Exact row-implied domains for the bounded MILP-to-PB projection.
//!
//! A finite PB encoding cannot represent a genuinely open general-integer
//! domain.  It may, however, use a finite bound that the original rows already
//! imply.  This module runs the standard interval row propagator on the
//! authoritative exact-rational model:
//!
//! ```text
//!        a_j x_j + rest <= u  and  rest >= rest_min
//!     => a_j x_j <= u - rest_min
//! ```
//!
//! with the analogous lower-row rule and sign reversal for negative `a_j`.
//! At most one open contributor is removable from an activity bound; with two,
//! the row says nothing about either.  General-integer candidates are rounded
//! inward to the integer hull (`ceil` for lower bounds, `floor` for upper
//! bounds).  Every adopted bound is therefore a consequence of original rows,
//! original column boxes, and declared integrality--never of a tolerance or a
//! model name.
//!
//! Only originally-open integral sides are returned to the encoder.  Existing
//! finite domain encodings remain byte-for-byte unchanged even if propagation
//! could tighten them.  The propagated finite sides still participate in later
//! deductions; this is sound because each of them is itself row-implied.

use std::time::Instant;

use num_bigint::BigInt;
use num_integer::Integer;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

use crate::model::{exact, ColKind, Model};

use super::{deadline_reached, PbTranslateDecline};

/// Match the compact generic PB route's hard ownership envelope.  This pass is
/// useful only before that route and must not make translating a declined giant
/// model its own unbounded preprocessing job.
const MAX_COLUMNS: usize = 8_192;
const MAX_ROWS: usize = 8_192;
const MAX_TERMS: usize = 250_000;
const MAX_TERMS_PER_ROW: usize = 8_192;

/// The established MILP interval propagator uses eight monotone sweeps.  A
/// bounded number of sweeps is sufficient for safe deductions; stopping early
/// can only leave a domain open and make this route decline.
const MAX_SWEEPS: usize = 8;

/// Cap exact intermediate growth.  Every operation checks its result before it
/// can feed another operation, so a rational can grow by at most one capped
/// operand between checks.  This is a resource decline, never an approximation.
const MAX_RATIONAL_BITS: u64 = 4_096;

/// Integral domains indexed by original model column.  Continuous entries stay
/// `None`; the bounded translator uses only integral entries.
pub(super) struct IntegralBounds {
    pub(super) lower: Vec<Option<BigInt>>,
    pub(super) upper: Vec<Option<BigInt>>,
}

/// Derive finite sides for otherwise-open integral columns.
///
/// The all-explicit fast path does not inspect any row.  Besides preserving the
/// old plan exactly, that prevents this optional capability from charging
/// existing bounded models rational-propagation work.
pub(super) fn derive(
    model: &Model,
    deadline: Option<Instant>,
) -> Result<IntegralBounds, PbTranslateDecline> {
    let (declared_lower, declared_upper) = declared_integral_bounds(model);
    let needs_inference = model.cols.iter().enumerate().any(|(column, spec)| {
        matches!(spec.kind, ColKind::Integer)
            && (declared_lower[column].is_none() || declared_upper[column].is_none())
    });
    if !needs_inference {
        return Ok(IntegralBounds {
            lower: declared_lower,
            upper: declared_upper,
        });
    }
    if deadline_reached(deadline) {
        return Err(PbTranslateDecline::Deadline);
    }
    if model.cols.len() > MAX_COLUMNS
        || model.rows.len() > MAX_ROWS
        || model
            .rows
            .iter()
            .any(|row| row.coeffs.len() > MAX_TERMS_PER_ROW)
    {
        return Err(PbTranslateDecline::ImpliedBoundsResourceLimit);
    }
    let term_count = model
        .rows
        .iter()
        .try_fold(0usize, |total, row| total.checked_add(row.coeffs.len()));
    if term_count.is_none_or(|terms| terms > MAX_TERMS) {
        return Err(PbTranslateDecline::ImpliedBoundsResourceLimit);
    }

    let integral: Vec<bool> = model
        .cols
        .iter()
        .map(|spec| matches!(spec.kind, ColKind::Binary | ColKind::Integer))
        .collect();
    let mut lower = Vec::with_capacity(model.cols.len());
    let mut upper = Vec::with_capacity(model.cols.len());
    for (column, spec) in model.cols.iter().enumerate() {
        if column & 0x3ff == 0 && deadline_reached(deadline) {
            return Err(PbTranslateDecline::Deadline);
        }
        let mut lo = exact(spec.lb);
        let mut hi = exact(spec.ub);
        if integral[column] {
            lo = lo.map(|value| BigRational::from_integer(value.numer().div_ceil(value.denom())));
            hi = hi.map(|value| BigRational::from_integer(value.numer().div_floor(value.denom())));
        }
        if matches!(spec.kind, ColKind::Binary) {
            if lo.is_some() {
                tighten_without_cap(&mut lo, BigRational::zero(), true);
            }
            if hi.is_some() {
                tighten_without_cap(&mut hi, BigRational::one(), false);
            }
        }
        if lo.as_ref().is_some_and(|value| !rational_fits(value))
            || hi.as_ref().is_some_and(|value| !rational_fits(value))
        {
            return Err(PbTranslateDecline::ImpliedBoundsResourceLimit);
        }
        lower.push(lo);
        upper.push(hi);
    }

    // Preflight every exact coefficient and bound before entering the repeated
    // loop.  The f64 matrix is only advice when an exact side-store override is
    // present, so all resource and sign decisions use the authoritative value.
    for (row_index, row) in model.rows.iter().enumerate() {
        if row_index & 0xff == 0 && deadline_reached(deadline) {
            return Err(PbTranslateDecline::Deadline);
        }
        for (term_index, &(column, advice)) in row.coeffs.iter().enumerate() {
            if term_index & 0x3ff == 0 && deadline_reached(deadline) {
                return Err(PbTranslateDecline::Deadline);
            }
            if !rational_fits(&model.row_coeff_exact(row_index, column, advice)) {
                return Err(PbTranslateDecline::ImpliedBoundsResourceLimit);
            }
        }
        if model
            .row_lb_exact(row_index, row.lb)
            .as_ref()
            .is_some_and(|value| !rational_fits(value))
            || model
                .row_ub_exact(row_index, row.ub)
                .as_ref()
                .is_some_and(|value| !rational_fits(value))
        {
            return Err(PbTranslateDecline::ImpliedBoundsResourceLimit);
        }
    }

    'sweeps: for _ in 0..MAX_SWEEPS {
        let mut changed = false;
        for (row_index, row) in model.rows.iter().enumerate() {
            if row_index & 0xff == 0 && deadline_reached(deadline) {
                return Err(PbTranslateDecline::Deadline);
            }
            let row_lower = model.row_lb_exact(row_index, row.lb);
            let row_upper = model.row_ub_exact(row_index, row.ub);
            if row_lower.is_none() && row_upper.is_none() {
                continue;
            }

            let mut terms = Vec::with_capacity(row.coeffs.len());
            let mut min_activity = BigRational::zero();
            let mut max_activity = BigRational::zero();
            let mut min_open = 0usize;
            let mut max_open = 0usize;
            for (term_index, &(column, advice)) in row.coeffs.iter().enumerate() {
                if term_index & 0x3ff == 0 && deadline_reached(deadline) {
                    return Err(PbTranslateDecline::Deadline);
                }
                let coefficient = model.row_coeff_exact(row_index, column, advice);
                if coefficient.is_zero() {
                    continue;
                }
                let column = column as usize;
                let (at_min, at_max) = if coefficient.is_positive() {
                    (&lower[column], &upper[column])
                } else {
                    (&upper[column], &lower[column])
                };
                if let Some(bound) = at_min {
                    add_product(&mut min_activity, &coefficient, bound)?;
                } else {
                    min_open += 1;
                }
                if let Some(bound) = at_max {
                    add_product(&mut max_activity, &coefficient, bound)?;
                } else {
                    max_open += 1;
                }
                terms.push((column, coefficient));
            }
            if min_open > 1 && max_open > 1 {
                continue;
            }

            for (column, coefficient) in terms {
                let (at_min, at_max) = if coefficient.is_positive() {
                    (&lower[column], &upper[column])
                } else {
                    (&upper[column], &lower[column])
                };
                let rest_min = remove_contribution(&min_activity, min_open, at_min, &coefficient)?;
                let rest_max = remove_contribution(&max_activity, max_open, at_max, &coefficient)?;

                // a*x <= upper - rest_min
                if let (Some(row_upper), Some(rest_min)) = (&row_upper, rest_min) {
                    let candidate = divide_difference(row_upper, &rest_min, &coefficient)?;
                    changed |= if coefficient.is_positive() {
                        tighten(&mut upper[column], candidate, false, integral[column])?
                    } else {
                        tighten(&mut lower[column], candidate, true, integral[column])?
                    };
                }
                // a*x >= lower - rest_max
                if let (Some(row_lower), Some(rest_max)) = (&row_lower, rest_max) {
                    let candidate = divide_difference(row_lower, &rest_max, &coefficient)?;
                    changed |= if coefficient.is_positive() {
                        tighten(&mut lower[column], candidate, true, integral[column])?
                    } else {
                        tighten(&mut upper[column], candidate, false, integral[column])?
                    };
                }

                // A crossed box proves the original model infeasible.  Stop
                // arithmetic immediately; the integral encoder will retain a
                // crossed originally-open side (or otherwise safely decline).
                if matches!((&lower[column], &upper[column]), (Some(lo), Some(hi)) if lo > hi) {
                    break 'sweeps;
                }
            }
        }
        if !changed {
            break;
        }
    }

    // Keep every declared finite side exactly as the old encoder saw it.  Only
    // fill holes; propagated tightening of a finite side remains an internal
    // premise for sound cascades but does not perturb existing radix layouts.
    let mut inferred_lower = declared_lower;
    let mut inferred_upper = declared_upper;
    for (column, spec) in model.cols.iter().enumerate() {
        if !matches!(spec.kind, ColKind::Binary | ColKind::Integer) {
            continue;
        }
        if inferred_lower[column].is_none() {
            inferred_lower[column] = lower[column]
                .as_ref()
                .map(|value| value.numer().div_ceil(value.denom()));
        }
        if inferred_upper[column].is_none() {
            inferred_upper[column] = upper[column]
                .as_ref()
                .map(|value| value.numer().div_floor(value.denom()));
        }
    }
    Ok(IntegralBounds {
        lower: inferred_lower,
        upper: inferred_upper,
    })
}

fn declared_integral_bounds(model: &Model) -> (Vec<Option<BigInt>>, Vec<Option<BigInt>>) {
    let mut lower = vec![None; model.cols.len()];
    let mut upper = vec![None; model.cols.len()];
    for (column, spec) in model.cols.iter().enumerate() {
        if !matches!(spec.kind, ColKind::Binary | ColKind::Integer) {
            continue;
        }
        lower[column] = exact(spec.lb).map(|value| value.numer().div_ceil(value.denom()));
        upper[column] = exact(spec.ub).map(|value| value.numer().div_floor(value.denom()));
        if matches!(spec.kind, ColKind::Binary) {
            let zero = BigInt::zero();
            let one = BigInt::one();
            if lower[column].as_ref().is_some_and(|value| value < &zero) {
                lower[column] = Some(zero);
            }
            if upper[column].as_ref().is_some_and(|value| value > &one) {
                upper[column] = Some(one);
            }
        }
    }
    (lower, upper)
}

fn remove_contribution(
    activity: &BigRational,
    open: usize,
    bound: &Option<BigRational>,
    coefficient: &BigRational,
) -> Result<Option<BigRational>, PbTranslateDecline> {
    match (open, bound) {
        (0, Some(bound)) => {
            let product = checked_product(coefficient, bound)?;
            checked_difference(activity, &product).map(Some)
        }
        (1, None) => Ok(Some(activity.clone())),
        _ => Ok(None),
    }
}

fn divide_difference(
    side: &BigRational,
    rest: &BigRational,
    coefficient: &BigRational,
) -> Result<BigRational, PbTranslateDecline> {
    let difference = checked_difference(side, rest)?;
    let value = difference / coefficient;
    ensure_fits(value)
}

fn add_product(
    activity: &mut BigRational,
    coefficient: &BigRational,
    bound: &BigRational,
) -> Result<(), PbTranslateDecline> {
    let product = checked_product(coefficient, bound)?;
    *activity += product;
    if !rational_fits(activity) {
        return Err(PbTranslateDecline::ImpliedBoundsResourceLimit);
    }
    Ok(())
}

fn checked_product(
    left: &BigRational,
    right: &BigRational,
) -> Result<BigRational, PbTranslateDecline> {
    ensure_fits(left * right)
}

fn checked_difference(
    left: &BigRational,
    right: &BigRational,
) -> Result<BigRational, PbTranslateDecline> {
    ensure_fits(left - right)
}

fn tighten(
    side: &mut Option<BigRational>,
    candidate: BigRational,
    lower: bool,
    integral: bool,
) -> Result<bool, PbTranslateDecline> {
    let candidate = if integral {
        let integer = if lower {
            candidate.numer().div_ceil(candidate.denom())
        } else {
            candidate.numer().div_floor(candidate.denom())
        };
        BigRational::from_integer(integer)
    } else {
        candidate
    };
    if !rational_fits(&candidate) {
        return Err(PbTranslateDecline::ImpliedBoundsResourceLimit);
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

fn tighten_without_cap(side: &mut Option<BigRational>, candidate: BigRational, lower: bool) {
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
}

fn ensure_fits(value: BigRational) -> Result<BigRational, PbTranslateDecline> {
    if rational_fits(&value) {
        Ok(value)
    } else {
        Err(PbTranslateDecline::ImpliedBoundsResourceLimit)
    }
}

fn rational_fits(value: &BigRational) -> bool {
    value.numer().bits() <= MAX_RATIONAL_BITS && value.denom().bits() <= MAX_RATIONAL_BITS
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Model;

    fn bounds(model: &Model) -> IntegralBounds {
        derive(model, None).expect("exact implied-bound propagation")
    }

    #[test]
    fn row_closes_an_open_integer_upper_with_integer_rounding() {
        let mut model = Model::new();
        let x = model.add_int_col(0.0, f64::INFINITY);
        let y = model.add_binary_col();
        model.add_row(f64::NEG_INFINITY, 7.0, &[(x, 2.0), (y, 1.0)]);

        let result = bounds(&model);
        assert_eq!(result.lower[x.index()], Some(0.into()));
        assert_eq!(result.upper[x.index()], Some(3.into()));
    }

    #[test]
    fn exact_fractional_lower_side_rounds_inward() {
        let mut model = Model::new();
        let x = model.add_int_col(f64::NEG_INFINITY, 10.0);
        let y = model.add_binary_col();
        let row = model.add_row(0.1, f64::INFINITY, &[(x, 2.0), (y, -1.0)]);
        model.record_inexact_row_bound(row, true, BigRational::new(1.into(), 3.into()));

        let result = bounds(&model);
        assert_eq!(result.lower[x.index()], Some(1.into()));
        assert_eq!(result.upper[x.index()], Some(10.into()));
    }

    #[test]
    fn fixed_point_cascade_uses_row_implied_intermediate_bound() {
        let mut model = Model::new();
        let x = model.add_int_col(0.0, f64::INFINITY);
        let y = model.add_int_col(0.0, f64::INFINITY);
        // Deliberately order the dependent row first: x's ceiling appears only
        // after y is bounded and a second exact sweep revisits this row.
        model.add_row(f64::NEG_INFINITY, 1.0, &[(x, 1.0), (y, -2.0)]);
        model.add_row(f64::NEG_INFINITY, 3.0, &[(y, 1.0)]);

        let result = bounds(&model);
        assert_eq!(result.upper[y.index()], Some(3.into()));
        assert_eq!(result.upper[x.index()], Some(7.into()));
    }

    #[test]
    fn two_open_contributors_decline_to_invent_a_bound() {
        let mut model = Model::new();
        let x = model.add_int_col(0.0, f64::INFINITY);
        let y = model.add_int_col(f64::NEG_INFINITY, 0.0);
        // x - y >= 0 has two contributors open in the activity direction
        // needed to upper-bound x.  Neither variable is actually bounded.
        model.add_row(0.0, f64::INFINITY, &[(x, 1.0), (y, -1.0)]);

        let result = bounds(&model);
        assert_eq!(result.upper[x.index()], None);
        assert_eq!(result.lower[y.index()], None);
    }

    #[test]
    fn finite_declared_sides_are_not_replaced_by_tighter_implied_sides() {
        let mut model = Model::new();
        let x = model.add_int_col(0.0, f64::INFINITY);
        let y = model.add_int_col(0.0, 100.0);
        model.add_row(f64::NEG_INFINITY, 3.0, &[(y, 1.0)]);
        model.add_row(f64::NEG_INFINITY, 5.0, &[(x, 1.0), (y, -1.0)]);

        let result = bounds(&model);
        assert_eq!(result.upper[y.index()], Some(100.into()));
        assert_eq!(result.upper[x.index()], Some(8.into()));
    }

    #[test]
    fn exact_growth_cap_declines_without_approximation() {
        let mut model = Model::new();
        let x = model.add_int_col(0.0, f64::INFINITY);
        let row = model.add_row(f64::NEG_INFINITY, 1.0, &[(x, 1.0)]);
        let huge = BigRational::from_integer(
            BigInt::one() << usize::try_from(MAX_RATIONAL_BITS + 1).expect("small test cap"),
        );
        model.record_inexact_row_coeff(row, x.0, huge);

        assert!(matches!(
            derive(&model, None),
            Err(PbTranslateDecline::ImpliedBoundsResourceLimit)
        ));
    }

    #[test]
    fn all_explicit_domain_fast_path_ignores_large_irrelevant_matrix() {
        let mut model = Model::new();
        let x = model.add_int_col(0.0, 2.0);
        for _ in 0..=MAX_ROWS {
            model.add_row(f64::NEG_INFINITY, 1.0, &[(x, 1.0)]);
        }

        let result = bounds(&model);
        assert_eq!(result.lower[x.index()], Some(0.into()));
        assert_eq!(result.upper[x.index()], Some(2.into()));
    }

    #[test]
    fn deadline_is_polled_before_open_domain_work() {
        let mut model = Model::new();
        model.add_int_col(0.0, f64::INFINITY);
        assert!(matches!(
            derive(&model, Some(Instant::now())),
            Err(PbTranslateDecline::Deadline)
        ));
    }
}
