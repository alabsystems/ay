// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Exact bounded-integer projection with objective-singleton elimination.
//!
//! Every finite integral domain is represented by a checked binary radix.  A
//! domain side may be explicit or supplied by the exact row-interval propagator
//! in [`super::implicit_bounds`]; a genuinely open side still declines.
//!
//! ```text
//! x = ceil(lb) + b0 + 2*b1 + 4*b2 + ...
//! ```
//!
//! plus the exact code-range row when the width is not `2^k - 1`.  Continuous
//! columns are accepted only when each is the sole continuous column in one
//! exact equality and occurs nowhere else.  Solving that equality expresses
//! the column as an exact affine form of the integer radix bits; its original
//! bounds become PB rows and its objective contribution is substituted.  The
//! defining equality is then redundant by construction.  No model name,
//! coefficient tolerance, or result-dependent condition participates.
//!
//! The singleton algebra intentionally matches
//! `presolve::substitute_singletons`/`SingletonPostsolve`: recover
//! `y = (b - sum(a_j*x_j))/a_y`, retain `y`'s box as a forcing range, and fold
//! `c_y*y` into the surviving objective.  This PB-local form does not rebuild
//! an `f64` model, so exact side-store rationals remain exact and no rounding
//! guard is necessary.

use std::collections::BTreeMap;
use std::time::Instant;

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, ToPrimitive, Zero};

use crate::model::{exact, ColKind, Model, Sense};

use super::{
    deadline_reached, integralize_terms, pb_core_row_range_fits, reduce_row_gcd, scaled_ceil,
    PbAffine, PbInequality, PbObjectiveMap, PbObjectivePlan, PbRoutePlan, PbTranslateDecline,
};

/// A single domain may not create an effectively unbounded PB expansion.
/// 126 bits keeps every individual radix weight below `i128::MAX`; the later
/// row/objective preflights still reject sums and scaled coefficients that do
/// not fit the PB core's exact arithmetic envelope.
const MAX_RADIX_BITS_PER_COLUMN: usize = 126;

#[derive(Default)]
struct AffineBuilder {
    constant: BigRational,
    terms: BTreeMap<u32, BigRational>,
}

impl AffineBuilder {
    fn from_constant(constant: BigRational) -> Self {
        Self {
            constant,
            terms: BTreeMap::new(),
        }
    }

    fn add_scaled(&mut self, scale: &BigRational, expression: &PbAffine) {
        if scale.is_zero() {
            return;
        }
        self.constant += scale * &expression.constant;
        for &(variable, ref coefficient) in &expression.terms {
            let entry = self.terms.entry(variable).or_insert_with(BigRational::zero);
            *entry += scale * coefficient;
        }
    }

    fn finish(self) -> PbAffine {
        PbAffine {
            constant: self.constant,
            terms: self
                .terms
                .into_iter()
                .filter(|(_, coefficient)| !coefficient.is_zero())
                .collect(),
        }
    }
}

pub(super) fn translate(
    model: &Model,
    deadline: Option<Instant>,
) -> Result<PbRoutePlan, PbTranslateDecline> {
    if deadline_reached(deadline) {
        return Err(PbTranslateDecline::Deadline);
    }

    let mut constraints = Vec::with_capacity(model.rows.len().saturating_mul(2));
    let mut lifts: Vec<Option<PbAffine>> = vec![None; model.cols.len()];
    let mut next_variable = 0u32;
    let mut encoded_general_integers = 0usize;
    let integral_bounds = super::implicit_bounds::derive(model, deadline)?;

    // Build the exact radix representation for every integral column first.
    // Singleton expressions below may then compose them without recursion.
    for (column, spec) in model.cols.iter().enumerate() {
        if column & 0x3ff == 0 && deadline_reached(deadline) {
            return Err(PbTranslateDecline::Deadline);
        }
        if !matches!(spec.kind, ColKind::Binary | ColKind::Integer) {
            continue;
        }
        encoded_general_integers += usize::from(matches!(spec.kind, ColKind::Integer));

        let Some(lo) = integral_bounds.lower[column].clone() else {
            return Err(PbTranslateDecline::NonBooleanDomain { column });
        };
        let Some(hi) = integral_bounds.upper[column].clone() else {
            return Err(PbTranslateDecline::NonBooleanDomain { column });
        };

        if lo > hi {
            constraints.push(PbInequality {
                terms: Vec::new(),
                rhs: 1,
            });
            // The plan is already contradictory, so this value can never be
            // lifted from a solver model.  Keeping a total expression makes
            // every later exact substitution deterministic nonetheless.
            lifts[column] = Some(PbAffine {
                constant: BigRational::zero(),
                terms: Vec::new(),
            });
            continue;
        }

        let width = &hi - &lo;
        let mut code = AffineBuilder::default();
        let mut weight = BigInt::one();
        let mut bits = 0usize;
        while &weight <= &width {
            if bits >= MAX_RADIX_BITS_PER_COLUMN || next_variable >= i32::MAX as u32 {
                return Err(PbTranslateDecline::IntegerEncodingTooWide { column });
            }
            code.terms
                .insert(next_variable, BigRational::from_integer(weight.clone()));
            next_variable += 1;
            bits += 1;
            weight <<= 1usize;
        }
        let code = code.finish();

        // `code <= width` removes the unused high binary codes.  It is
        // tautological exactly when width is `2^bits - 1`; emitting it anyway
        // is harmless, but avoiding the row saves propagation state on the
        // common power-of-two domain.
        let full_width = &weight - BigInt::one();
        if width < full_width {
            emit_upper(
                &mut constraints,
                &code,
                &BigRational::from_integer(width.clone()),
                column,
                deadline,
            )?;
        }

        let mut value = AffineBuilder::from_constant(BigRational::from_integer(lo));
        value.add_scaled(&BigRational::one(), &code);
        lifts[column] = Some(value.finish());
    }

    // Locate exact continuous singletons.  A defining row must have exactly
    // one continuous column; accepting two simultaneous unknowns would turn a
    // definition into an underdetermined projection.
    let mut occurrences: Vec<Vec<(usize, BigRational)>> = vec![Vec::new(); model.cols.len()];
    let mut continuous_per_row = vec![0usize; model.rows.len()];
    for (row_index, row) in model.rows.iter().enumerate() {
        for &(column, advice) in &row.coeffs {
            let coefficient = model.row_coeff_exact(row_index, column, advice);
            if coefficient.is_zero() {
                continue;
            }
            if matches!(model.cols[column as usize].kind, ColKind::Continuous) {
                occurrences[column as usize].push((row_index, coefficient));
                continuous_per_row[row_index] += 1;
            }
        }
    }

    let mut defining_rows = vec![false; model.rows.len()];
    let mut eliminated_continuous = 0usize;
    for (column, spec) in model.cols.iter().enumerate() {
        if !matches!(spec.kind, ColKind::Continuous) {
            continue;
        }
        if deadline_reached(deadline) {
            return Err(PbTranslateDecline::Deadline);
        }
        let [(row_index, coefficient)] = occurrences[column].as_slice() else {
            return Err(PbTranslateDecline::ContinuousNotSingleton { column });
        };
        if continuous_per_row[*row_index] != 1 {
            return Err(PbTranslateDecline::SingletonRowHasContinuousPeer {
                column,
                row: *row_index,
            });
        }
        let row = &model.rows[*row_index];
        let Some(lb) = model.row_lb_exact(*row_index, row.lb) else {
            return Err(PbTranslateDecline::SingletonRowNotEquality {
                column,
                row: *row_index,
            });
        };
        let Some(ub) = model.row_ub_exact(*row_index, row.ub) else {
            return Err(PbTranslateDecline::SingletonRowNotEquality {
                column,
                row: *row_index,
            });
        };
        if lb != ub || coefficient.is_zero() {
            return Err(PbTranslateDecline::SingletonRowNotEquality {
                column,
                row: *row_index,
            });
        }

        // a_y*y + sum(a_j*x_j) = b
        // y = b/a_y - sum((a_j/a_y)*x_j), all exactly.
        let mut expression = AffineBuilder::from_constant(&lb / coefficient);
        for &(other, advice) in &row.coeffs {
            if other as usize == column {
                continue;
            }
            let a = model.row_coeff_exact(*row_index, other, advice);
            if a.is_zero() {
                continue;
            }
            let Some(other_expression) = &lifts[other as usize] else {
                return Err(PbTranslateDecline::SingletonRowHasContinuousPeer {
                    column,
                    row: *row_index,
                });
            };
            expression.add_scaled(&(-a / coefficient), other_expression);
        }
        lifts[column] = Some(expression.finish());
        defining_rows[*row_index] = true;
        eliminated_continuous += 1;
    }

    let lifts = lifts
        .into_iter()
        .enumerate()
        .map(|(column, expression)| {
            expression.ok_or(PbTranslateDecline::ContinuousNotSingleton { column })
        })
        .collect::<Result<Vec<_>, _>>()?;

    // A removed column's ORIGINAL bounds remain semantic constraints on its
    // reconstructed affine value.
    for (column, spec) in model.cols.iter().enumerate() {
        if !matches!(spec.kind, ColKind::Continuous) {
            continue;
        }
        let source_row = occurrences[column][0].0;
        if let Some(lb) = exact(spec.lb) {
            emit_lower(&mut constraints, &lifts[column], &lb, source_row, deadline)?;
        }
        if let Some(ub) = exact(spec.ub) {
            emit_upper(&mut constraints, &lifts[column], &ub, source_row, deadline)?;
        }
    }

    // Project every non-defining original row through the exact affine map.
    // Defining equalities hold identically after reconstruction and are not
    // duplicated in the PB instance.
    for (row_index, row) in model.rows.iter().enumerate() {
        if defining_rows[row_index] {
            continue;
        }
        if row_index & 0x3ff == 0 && deadline_reached(deadline) {
            return Err(PbTranslateDecline::Deadline);
        }
        let mut projected = AffineBuilder::default();
        for &(column, advice) in &row.coeffs {
            let coefficient = model.row_coeff_exact(row_index, column, advice);
            projected.add_scaled(&coefficient, &lifts[column as usize]);
        }
        let projected = projected.finish();
        if let Some(lb) = model.row_lb_exact(row_index, row.lb) {
            emit_lower(&mut constraints, &projected, &lb, row_index, deadline)?;
        }
        if let Some(ub) = model.row_ub_exact(row_index, row.ub) {
            emit_upper(&mut constraints, &projected, &ub, row_index, deadline)?;
        }
    }

    let objective = model
        .has_objective
        .then(|| translate_objective(model, &lifts, deadline))
        .transpose()?;
    let num_constraints =
        u32::try_from(constraints.len()).map_err(|_| PbTranslateDecline::TooManyConstraints)?;

    Ok(PbRoutePlan {
        num_vars: next_variable,
        num_constraints,
        constraints,
        objective,
        column_lifts: Some(lifts),
        eliminated_continuous,
        encoded_general_integers,
    })
}

fn project_objective(model: &Model, lifts: &[PbAffine]) -> PbAffine {
    let mut projected = AffineBuilder::from_constant(model.obj_offset_exact());
    for (column, spec) in model.cols.iter().enumerate() {
        let coefficient = model.obj_coeff_exact_at(column as u32, spec.obj);
        projected.add_scaled(&coefficient, &lifts[column]);
    }
    projected.finish()
}

fn translate_objective(
    model: &Model,
    lifts: &[PbAffine],
    deadline: Option<Instant>,
) -> Result<PbObjectivePlan, PbTranslateDecline> {
    let projected = project_objective(model, lifts);
    let (mut terms, denominator) = integralize_terms(&projected.terms, deadline)?
        .ok_or(PbTranslateDecline::ObjectiveCoefficientOverflow)?;
    let direction = match model.sense {
        Sense::Minimize => 1,
        Sense::Maximize => {
            for (_, coefficient) in &mut terms {
                *coefficient = coefficient
                    .checked_neg()
                    .ok_or(PbTranslateDecline::ObjectiveCoefficientOverflow)?;
            }
            -1
        }
    };

    let mut minimum = 0i128;
    let mut maximum = 0i128;
    for &(_, coefficient) in &terms {
        if coefficient == i128::MIN {
            return Err(PbTranslateDecline::ObjectiveCoefficientOverflow);
        }
        if coefficient < 0 {
            minimum = minimum
                .checked_add(coefficient)
                .ok_or(PbTranslateDecline::ObjectiveRangeOverflow)?;
        } else {
            maximum = maximum
                .checked_add(coefficient)
                .ok_or(PbTranslateDecline::ObjectiveRangeOverflow)?;
        }
    }

    Ok(PbObjectivePlan {
        terms,
        map: PbObjectiveMap {
            denominator,
            direction,
            offset: projected.constant,
        },
    })
}

fn emit_lower(
    constraints: &mut Vec<PbInequality>,
    expression: &PbAffine,
    lower: &BigRational,
    source_row: usize,
    deadline: Option<Instant>,
) -> Result<(), PbTranslateDecline> {
    emit_ge(
        constraints,
        expression.terms.clone(),
        lower - &expression.constant,
        source_row,
        deadline,
    )
}

fn emit_upper(
    constraints: &mut Vec<PbInequality>,
    expression: &PbAffine,
    upper: &BigRational,
    source_row: usize,
    deadline: Option<Instant>,
) -> Result<(), PbTranslateDecline> {
    emit_ge(
        constraints,
        expression
            .terms
            .iter()
            .map(|&(variable, ref coefficient)| (variable, -coefficient))
            .collect(),
        &expression.constant - upper,
        source_row,
        deadline,
    )
}

fn emit_ge(
    constraints: &mut Vec<PbInequality>,
    terms: Vec<(u32, BigRational)>,
    rhs: BigRational,
    source_row: usize,
    deadline: Option<Instant>,
) -> Result<(), PbTranslateDecline> {
    let (terms, denominator) = integralize_terms(&terms, deadline)?
        .ok_or(PbTranslateDecline::RowCoefficientOverflow { row: source_row })?;
    let rhs = scaled_ceil(&rhs, &denominator)
        .and_then(|value| value.to_i128())
        .ok_or(PbTranslateDecline::RowBoundOverflow { row: source_row })?;
    let inequality = reduce_row_gcd(PbInequality { terms, rhs })
        .ok_or(PbTranslateDecline::RowNormalizationOverflow { row: source_row })?;
    if !pb_core_row_range_fits(&inequality) {
        return Err(PbTranslateDecline::RowNormalizationOverflow { row: source_row });
    }
    constraints.push(inequality);
    Ok(())
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use super::*;
    use crate::Model;

    fn br(n: i64, d: i64) -> BigRational {
        BigRational::new(n.into(), d.into())
    }

    fn assignments(n: usize) -> impl Iterator<Item = Vec<bool>> {
        (0usize..(1usize << n))
            .map(move |mask| (0..n).map(|bit| mask & (1usize << bit) != 0).collect())
    }

    #[test]
    fn radix_domain_is_exact_for_non_power_of_two_width() {
        let mut model = Model::new();
        let x = model.add_int_col(-1.2, 2.8); // effective integers -1..=2, full two-bit width
        let z = model.add_int_col(0.0, 2.0); // two bits, code 3 forbidden
        model.add_row(0.0, 2.0, &[(x, 1.0), (z, 1.0)]);

        let plan = translate(&model, None).expect("bounded integer projection");
        assert_eq!(plan.num_vars, 4);
        assert_eq!(plan.encoded_general_integers, 2);
        for assignment in assignments(plan.num_vars as usize) {
            let accepted = plan.satisfies(&assignment);
            let point = plan.lift(&assignment).expect("total affine lift");
            let original = model.check_point(&point).is_ok();
            assert_eq!(
                accepted, original,
                "assignment={assignment:?}, point={point:?}"
            );
        }
    }

    #[test]
    fn row_implied_open_integer_domain_is_encoded_exactly() {
        let mut model = Model::new();
        let x = model.add_int_col(0.0, f64::INFINITY);
        let y = model.add_binary_col();
        // 2*x + y <= 7 implies x <= 3 over the declared nonnegative box.
        model.add_row(f64::NEG_INFINITY, 7.0, &[(x, 2.0), (y, 1.0)]);

        let plan = translate(&model, None).expect("row-implied finite integer domain");
        assert_eq!(plan.num_vars, 3, "two radix bits for x and one for y");
        for assignment in assignments(plan.num_vars as usize) {
            let accepted = plan.satisfies(&assignment);
            let point = plan.lift(&assignment).expect("total affine lift");
            assert_eq!(
                accepted,
                model.check_point(&point).is_ok(),
                "assignment={assignment:?}, point={point:?}"
            );
        }
    }

    #[test]
    fn genuinely_open_integer_domain_still_declines() {
        let mut model = Model::new();
        let x = model.add_int_col(0.0, f64::INFINITY);
        let y = model.add_int_col(f64::NEG_INFINITY, 0.0);
        model.add_row(0.0, f64::INFINITY, &[(x, 1.0), (y, -1.0)]);

        assert_eq!(
            translate(&model, None),
            Err(PbTranslateDecline::NonBooleanDomain { column: x.index() })
        );
    }

    #[test]
    fn exhaustive_signed_row_implied_domains_match_original_integer_points() {
        for coefficient in [-3i64, -2, -1, 1, 2, 3] {
            for rhs_numerator in -7i64..=7 {
                let mut model = Model::new();
                // For positive a, a*x+y<=b closes x above; for negative a it
                // closes x below.  Leave exactly that side open.
                let x = if coefficient > 0 {
                    model.add_int_col(-2.0, f64::INFINITY)
                } else {
                    model.add_int_col(f64::NEG_INFINITY, 2.0)
                };
                let y = model.add_binary_col();
                let rhs = rhs_numerator as f64 / 2.0;
                model.add_row(f64::NEG_INFINITY, rhs, &[(x, coefficient as f64), (y, 1.0)]);

                let plan = translate(&model, None).expect("one row closes the open side");
                let actual = assignments(plan.num_vars as usize)
                    .filter(|assignment| plan.satisfies(assignment))
                    .map(|assignment| {
                        let point = plan.lift(&assignment).expect("total radix lift");
                        model
                            .check_point(&point)
                            .expect("translated point revalidates");
                        assert!(point[x.index()].is_integer());
                        assert!(point[y.index()].is_integer());
                        (point[x.index()].to_integer(), point[y.index()].to_integer())
                    })
                    .collect::<BTreeSet<_>>();

                // The coefficient/rhs ranges imply every feasible x lies in
                // -4..=4; the wider enumeration is an independent guard.
                let mut expected: BTreeSet<(BigInt, BigInt)> = BTreeSet::new();
                for x_value in -16i64..=16 {
                    for y_value in 0i64..=1 {
                        let point = vec![
                            BigRational::from_integer(x_value.into()),
                            BigRational::from_integer(y_value.into()),
                        ];
                        if model.check_point(&point).is_ok() {
                            expected.insert((x_value.into(), y_value.into()));
                        }
                    }
                }
                assert_eq!(actual, expected, "a={coefficient}, rhs={rhs_numerator}/2");
            }
        }
    }

    #[test]
    fn exhaustive_covering_rows_do_not_fake_open_upper_domains() {
        for a in 1i64..=3 {
            for b in 1i64..=3 {
                for rhs in -2i64..=2 {
                    let mut model = Model::new();
                    let x = model.add_int_col(0.0, f64::INFINITY);
                    let y = model.add_int_col(0.0, f64::INFINITY);
                    // A covering lower row may force a larger value, but it
                    // cannot cap either nonnegative variable above.
                    model.add_row(rhs as f64, f64::INFINITY, &[(x, a as f64), (y, b as f64)]);
                    assert_eq!(
                        translate(&model, None),
                        Err(PbTranslateDecline::NonBooleanDomain { column: x.index() }),
                        "a={a}, b={b}, rhs={rhs}"
                    );
                }
            }
        }
    }

    #[test]
    fn exact_singleton_elimination_reconstructs_point_and_objective() {
        let mut model = Model::new();
        let x = model.add_int_col(0.0, 2.0);
        let y = model.add_col(0.0, f64::INFINITY);
        // 2*x - 3*y = -1  =>  y = (1 + 2*x)/3.
        model.add_row(-1.0, -1.0, &[(x, 2.0), (y, -3.0)]);
        model.set_objective(&[(y, 5.0)], Sense::Minimize);
        model.set_objective_offset(1.0 / 7.0);
        model.record_inexact_obj_offset(br(1, 7));

        let plan = translate(&model, None).expect("singleton projection");
        assert_eq!(plan.eliminated_continuous, 1);
        let objective = plan.objective.as_ref().expect("projected objective");
        for assignment in assignments(plan.num_vars as usize) {
            if !plan.satisfies(&assignment) {
                continue;
            }
            let point = plan.lift(&assignment).expect("postsolve");
            model.check_point(&point).expect("original exact model");
            let pb_value = objective.value_at(&assignment).expect("objective range");
            assert_eq!(
                objective.map.model_value(pb_value),
                model.objective_value_at(&point)
            );
        }
    }

    #[test]
    fn singleton_uses_true_rational_row_side_store() {
        let mut model = Model::new();
        let x = model.add_int_col(0.0, 1.0);
        let y = model.add_col(f64::NEG_INFINITY, f64::INFINITY);
        let row = model.add_row(0.1, 0.1, &[(x, 1.0), (y, 1.0)]);
        model.record_inexact_row_bound(row, true, br(1, 3));
        model.record_inexact_row_bound(row, false, br(1, 3));

        let plan = translate(&model, None).expect("true rational equality");
        for assignment in assignments(plan.num_vars as usize) {
            let point = plan.lift(&assignment).expect("postsolve");
            assert_eq!(point[y.index()], br(1, 3) - &point[x.index()]);
            model.check_point(&point).expect("side-store exact point");
        }
    }

    #[test]
    fn singleton_uses_true_rational_coefficient_side_store() {
        let mut model = Model::new();
        let x = model.add_int_col(0.0, 12.0);
        let y = model.add_col(0.0, f64::INFINITY);
        // This is the qnet-style shape: a decimal cost times a bounded integer
        // defines one continuous objective column.  The f64 is only advice;
        // the exact 2651/20 coefficient must drive projection and postsolve.
        let row = model.add_row(0.0, 0.0, &[(x, 132.55), (y, -1.0)]);
        model.record_inexact_row_coeff(row, x.0, br(2_651, 20));
        model.set_objective(&[(y, 1.0)], Sense::Minimize);

        let plan = translate(&model, None).expect("exact decimal singleton");
        let objective = plan.objective.as_ref().expect("projected objective");
        for assignment in assignments(plan.num_vars as usize) {
            if !plan.satisfies(&assignment) {
                continue;
            }
            let point = plan.lift(&assignment).expect("postsolve");
            model.check_point(&point).expect("original exact model");
            assert_eq!(point[y.index()], br(2_651, 20) * &point[x.index()]);
            let claimed = objective.value_at(&assignment).expect("PB objective");
            assert_eq!(
                objective.map.model_value(claimed),
                model.objective_value_at(&point)
            );
        }
    }

    #[test]
    fn singleton_box_becomes_an_exact_forcing_row() {
        let mut model = Model::new();
        let x = model.add_int_col(0.0, 2.0);
        let y = model.add_col(0.0, 1.0);
        // y = 1 - x.  The defining equality alone admits x=2, but y's
        // original lower bound must project to x<=1.
        model.add_row(1.0, 1.0, &[(x, 1.0), (y, 1.0)]);

        let plan = translate(&model, None).expect("bounded singleton projection");
        for assignment in assignments(plan.num_vars as usize) {
            let accepted = plan.satisfies(&assignment);
            let point = plan.lift(&assignment).expect("postsolve");
            assert_eq!(
                accepted,
                model.check_point(&point).is_ok(),
                "assignment={assignment:?}, point={point:?}"
            );
        }
    }

    #[test]
    fn non_singleton_continuous_column_declines() {
        let mut model = Model::new();
        let x = model.add_int_col(0.0, 3.0);
        let y = model.add_col(0.0, 10.0);
        model.add_row(0.0, 0.0, &[(x, 1.0), (y, -1.0)]);
        model.add_row(1.0, f64::INFINITY, &[(y, 1.0)]);
        assert_eq!(
            translate(&model, None),
            Err(PbTranslateDecline::ContinuousNotSingleton { column: 1 })
        );
    }

    #[test]
    fn two_continuous_unknowns_are_not_misread_as_definitions() {
        let mut model = Model::new();
        let x = model.add_int_col(0.0, 3.0);
        let y = model.add_col(0.0, 10.0);
        let z = model.add_col(0.0, 10.0);
        model.add_row(0.0, 0.0, &[(x, 1.0), (y, -1.0), (z, 1.0)]);
        assert!(matches!(
            translate(&model, None),
            Err(PbTranslateDecline::SingletonRowHasContinuousPeer { .. })
        ));
    }

    #[test]
    fn one_sided_singleton_row_declines_fail_closed() {
        let mut model = Model::new();
        let x = model.add_int_col(0.0, 3.0);
        let y = model.add_col(0.0, 10.0);
        model.add_row(0.0, f64::INFINITY, &[(x, 1.0), (y, -1.0)]);
        assert_eq!(
            translate(&model, None),
            Err(PbTranslateDecline::SingletonRowNotEquality { column: 1, row: 0 })
        );
    }

    #[test]
    fn maximization_mapping_survives_radix_offsets() {
        let mut model = Model::new();
        let x = model.add_int_col(-3.0, 2.0);
        model.set_objective(&[(x, 0.5)], Sense::Maximize);
        model.set_objective_offset(0.25);
        let plan = translate(&model, None).expect("bounded max objective");
        let objective = plan.objective.as_ref().expect("objective");
        for assignment in assignments(plan.num_vars as usize) {
            if !plan.satisfies(&assignment) {
                continue;
            }
            let point = plan.lift(&assignment).expect("lift");
            let claimed = objective.value_at(&assignment).expect("PB value");
            assert_eq!(
                objective.map.model_value(claimed),
                model.objective_value_at(&point)
            );
        }
    }

    #[test]
    fn radix_resource_cap_declines_fail_closed() {
        let mut model = Model::new();
        let x = model.add_int_col(0.0, f64::MAX);
        assert_eq!(
            translate(&model, None),
            Err(PbTranslateDecline::IntegerEncodingTooWide { column: x.index() })
        );
    }
}
