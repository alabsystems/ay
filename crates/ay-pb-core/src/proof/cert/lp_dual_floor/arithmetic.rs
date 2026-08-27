// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact reconstruction of a scaled LP-dual certificate.
//!
//! This is the arithmetic soundness boundary. It accepts a plan only when all
//! input/box duals and derived lifts are non-negative, every conversion and
//! operation fits `i128`, and the reconstructed CG-rounded degree is exactly the
//! claimed optimum.

use std::collections::BTreeMap;

use num_bigint::{BigInt, Sign};
use num_rational::BigRational;
use num_traits::ToPrimitive;

use super::super::ceil_div_i128;
use crate::optimize::lp_bound::LpDualRaw;
use crate::types::{PbConstraint, PbObjective, PbRel};

pub(super) type Coefficients = BTreeMap<u32, i128>;
pub(super) type LinearRow = (Coefficients, i128);

/// Largest common denominator admitted for an emitted proof.
///
/// Half- and third-integral duals use scales 2 and 3. The cap prevents a product
/// of unrelated denominators from producing huge `pol` multipliers, proof text,
/// and VeriPB arithmetic. Exceeding it withholds a certificate, never a verdict.
pub(super) const MAX_DUAL_SCALE: i128 = 1 << 20;

pub(super) struct DualPlan {
    pub(super) row_multipliers: Vec<i128>,
    pub(super) box_multipliers: Vec<i128>,
    pub(super) complement: Vec<bool>,
    pub(super) lifts: Vec<i128>,
    pub(super) scale: i128,
}

pub(super) enum PlanError {
    InvalidObjective,
    InvalidRow,
    RowCount,
    Arithmetic,
    NegativeRowDual { row: usize, value: i128 },
    NegativeBoxDual { variable: usize, value: i128 },
    NegativeLift { variable: u32, value: i128 },
    WrongFloor(i128),
    EmptyAggregate,
}

impl PlanError {
    pub(super) fn diagnosis(&self, optimum: i128) -> Option<String> {
        match self {
            Self::RowCount => Some("row-count-mismatch".into()),
            Self::NegativeRowDual { row, value } => {
                Some(format!("negative-row-dual(row{row},y={value})"))
            }
            Self::NegativeBoxDual { variable, value } => {
                Some(format!("negative-box-dual(var{variable},y={value})"))
            }
            Self::NegativeLift { variable, value } => {
                Some(format!("negative-lift(var{variable},l={value})"))
            }
            Self::WrongFloor(floor) => Some(format!("reconstructed-floor={floor}(want {optimum})")),
            Self::EmptyAggregate => {
                Some("empty-aggregate(floor is pure box bound; no row to seed pol)".into())
            }
            Self::InvalidObjective | Self::InvalidRow | Self::Arithmetic => None,
        }
    }
}

pub(super) struct DualScale {
    pub(super) value: BigInt,
    pub(super) capped: bool,
}

fn bigint_gcd(a: &BigInt, b: &BigInt) -> BigInt {
    let mut a = a.clone();
    let mut b = b.clone();
    while b.sign() != Sign::NoSign {
        let remainder = &a % &b;
        a = b;
        b = remainder;
    }
    a
}

pub(super) fn common_dual_scale(duals: &[BigRational]) -> Option<DualScale> {
    // One LCM scales the entire derivation uniformly. Consequently the final
    // division restores every objective coefficient exactly and rounds only the
    // degree, which is the Chvatal-Gomory `ceil(LP*)` step.
    let mut value = BigInt::from(1);
    for dual in duals {
        let denominator = dual.denom();
        if denominator.sign() != Sign::Plus {
            return None;
        }
        let gcd = bigint_gcd(&value, denominator);
        if gcd.sign() == Sign::NoSign {
            return None;
        }
        value = &value / gcd * denominator;
        if value > BigInt::from(MAX_DUAL_SCALE) {
            return Some(DualScale {
                value,
                capped: true,
            });
        }
    }
    Some(DualScale {
        value,
        capped: false,
    })
}

/// Denominator shape of a dual point, for the census.
///
/// EXISTS BECAUSE `scale=>cap` NAMES NO NUMBER. Reading it as "this LP vertex
/// has awkward denominators" is the natural but wrong inference: a dual that
/// came from the f64-certified tier is built with `BigRational::from_float`,
/// which is exact and therefore reproduces the whole BINARY EXPANSION of each
/// f64. Its denominators are powers of two in the 2^50 range whatever the LP
/// looks like. The distinction is the difference between "raise the cap" (which
/// cannot work — the next float would need 2^52) and "re-express the point over
/// a small common denominator" (which does).
pub(super) fn denominator_profile(duals: &[BigRational]) -> String {
    let mut widest = 0u64;
    let mut fractional = 0usize;
    let mut power_of_two = 0usize;
    for dual in duals {
        let denominator = dual.denom();
        if denominator == &BigInt::from(1) {
            continue;
        }
        fractional += 1;
        let bits = denominator.bits();
        widest = widest.max(bits);
        // A power of two has exactly one set bit: `d & (d - 1) == 0`.
        if (denominator & (denominator - BigInt::from(1))).sign() == Sign::NoSign {
            power_of_two += 1;
        }
    }
    format!(
        "maxdenom=2^{widest},frac={fractional},pow2={power_of_two},n={}",
        duals.len()
    )
}

pub(super) fn objective_coefficients(objective: &PbObjective) -> Result<Coefficients, PlanError> {
    let mut coefficients = Coefficients::new();
    for term in &objective.terms {
        let [literal] = term.lits.as_slice() else {
            return Err(PlanError::InvalidObjective);
        };
        if literal.negated || literal.var == 0 {
            return Err(PlanError::InvalidObjective);
        }
        let updated = coefficients
            .get(&literal.var)
            .copied()
            .unwrap_or(0_i128)
            .checked_add(term.coeff)
            .ok_or(PlanError::Arithmetic)?;
        coefficients.insert(literal.var, updated);
    }
    (!coefficients.is_empty())
        .then_some(coefficients)
        .ok_or(PlanError::InvalidObjective)
}

pub(super) fn linear_rows(constraints: &[PbConstraint]) -> Result<Vec<LinearRow>, PlanError> {
    // This order is proof-critical. `Ge` contributes one row. The LP model splits
    // `a*x = b` into `a*x >= b` then `-a*x >= -b`; VeriPB likewise stores an input
    // equality as two consecutive `f` constraints. Thus vector row `r` always maps
    // to `f` id `r + 1`, and each equality half has its own non-negative dual.
    // Negated literals are folded via `~x = 1 - x`, including the RHS shift.
    let mut rows = Vec::new();
    for constraint in constraints {
        let mut coefficients = Coefficients::new();
        let mut rhs = constraint.rhs;
        for term in &constraint.terms {
            let [literal] = term.lits.as_slice() else {
                return Err(PlanError::InvalidRow);
            };
            let old = coefficients.get(&literal.var).copied().unwrap_or(0_i128);
            let updated = if literal.negated {
                rhs = rhs.checked_sub(term.coeff).ok_or(PlanError::Arithmetic)?;
                old.checked_sub(term.coeff)
            } else {
                old.checked_add(term.coeff)
            }
            .ok_or(PlanError::Arithmetic)?;
            coefficients.insert(literal.var, updated);
        }
        match constraint.rel {
            PbRel::Ge => rows.push((coefficients, rhs)),
            PbRel::Eq => {
                let negated = coefficients
                    .iter()
                    .map(|(&variable, &coefficient)| {
                        coefficient
                            .checked_neg()
                            .map(|negated| (variable, negated))
                            .ok_or(PlanError::Arithmetic)
                    })
                    .collect::<Result<Coefficients, _>>()?;
                rows.push((coefficients, rhs));
                rows.push((negated, rhs.checked_neg().ok_or(PlanError::Arithmetic)?));
            }
        }
    }
    Ok(rows)
}

fn scaled_multiplier(dual: &BigRational, scale: &BigInt) -> Result<i128, PlanError> {
    let value = dual * BigRational::from_integer(scale.clone());
    if !value.is_integer() {
        return Err(PlanError::Arithmetic);
    }
    value.to_integer().to_i128().ok_or(PlanError::Arithmetic)
}

fn scaled_multipliers(
    raw: &LpDualRaw,
    num_rows: usize,
    num_vars: usize,
    scale: &BigInt,
) -> Result<(Vec<i128>, Vec<i128>), PlanError> {
    if raw.num_constraint_rows != num_rows
        || raw.duals.len() != num_rows + num_vars
        || raw.complement.len() != num_vars
    {
        return Err(PlanError::RowCount);
    }
    let rows = raw.duals[..num_rows]
        .iter()
        .map(|dual| scaled_multiplier(dual, scale))
        .collect::<Result<Vec<_>, _>>()?;
    let boxes = raw.duals[num_rows..]
        .iter()
        .map(|dual| scaled_multiplier(dual, scale))
        .collect::<Result<Vec<_>, _>>()?;
    // VeriPB `pol` may scale an input row or literal axiom only by a
    // non-negative value, so a negative dual is not emit-able.
    if let Some(row) = rows.iter().position(|&value| value < 0) {
        return Err(PlanError::NegativeRowDual {
            row,
            value: rows[row],
        });
    }
    if let Some(index) = boxes.iter().position(|&value| value < 0) {
        return Err(PlanError::NegativeBoxDual {
            variable: index + 1,
            value: boxes[index],
        });
    }
    Ok((rows, boxes))
}

fn aggregate_rows(rows: &[LinearRow], multipliers: &[i128]) -> Result<LinearRow, PlanError> {
    // At scale `k`: `aggregate[j] = sum_r k*Y_r*A[r,j]` and the degree is
    // `sum_r k*Y_r*b[r]`. All operations are checked before any proof is emitted.
    let mut aggregate = Coefficients::new();
    let mut rhs = 0_i128;
    for ((coefficients, row_rhs), &multiplier) in rows.iter().zip(multipliers) {
        if multiplier == 0 {
            continue;
        }
        rhs = rhs
            .checked_add(
                multiplier
                    .checked_mul(*row_rhs)
                    .ok_or(PlanError::Arithmetic)?,
            )
            .ok_or(PlanError::Arithmetic)?;
        for (&variable, &coefficient) in coefficients {
            let old = aggregate.get(&variable).copied().unwrap_or(0_i128);
            let product = multiplier
                .checked_mul(coefficient)
                .ok_or(PlanError::Arithmetic)?;
            aggregate.insert(
                variable,
                old.checked_add(product).ok_or(PlanError::Arithmetic)?,
            );
        }
    }
    Ok((aggregate, rhs))
}

fn reconstruct_lifts(
    objective: &Coefficients,
    aggregate: &LinearRow,
    boxes: &[i128],
    complement: &[bool],
    scale: i128,
    optimum: i128,
) -> Result<Vec<i128>, PlanError> {
    let mut lifts = Vec::with_capacity(boxes.len());
    let mut final_rhs = aggregate.1;
    for (index, (&box_multiplier, &is_complemented)) in boxes.iter().zip(complement).enumerate() {
        let variable = u32::try_from(index + 1).map_err(|_| PlanError::Arithmetic)?;
        let aggregate_coefficient = aggregate.0.get(&variable).copied().unwrap_or(0_i128);
        let wanted = objective
            .get(&variable)
            .copied()
            .unwrap_or(0_i128)
            .checked_mul(scale)
            .ok_or(PlanError::Arithmetic)?;
        // Let `a` be the aggregate coefficient, `yb` the scaled box dual, `l`
        // the opposite-axiom lift, and `want = k*objective[j]`. Mapping the LP's
        // complemented space back to the original variable requires exactly:
        //
        //   complemented:     want = a + yb - l
        //                       box `x>=0`, lift `~x>=0`
        //   non-complemented: want = a - yb + l
        //                       box `~x>=0`, lift `x>=0`
        //
        // Solving these equations for `l` and requiring `l >= 0` proves that the
        // emitted axioms land on the scaled objective coefficient.
        let lift = if is_complemented {
            aggregate_coefficient
                .checked_add(box_multiplier)
                .and_then(|value| value.checked_sub(wanted))
        } else {
            wanted
                .checked_sub(aggregate_coefficient)
                .and_then(|value| value.checked_add(box_multiplier))
        }
        .ok_or(PlanError::Arithmetic)?;
        if lift < 0 {
            return Err(PlanError::NegativeLift {
                variable,
                value: lift,
            });
        }
        // `x>=0` contributes degree 0; `~x>=0` is `-x>=-1`, so it subtracts its
        // multiplier from the unnormalized RHS.
        final_rhs = final_rhs
            .checked_sub(if is_complemented {
                lift
            } else {
                box_multiplier
            })
            .ok_or(PlanError::Arithmetic)?;
        lifts.push(lift);
    }
    // The plan now entails `sum_j (k*c_j)x_j >= final_rhs`. VeriPB normalizes a
    // negative `c_j` as `|c_j|~x_j` and shifts the degree by `|c_j|`. At scale
    // `k` that shift is divisible by `k`, so CG division yields
    // `ceil(final_rhs/k) + sum_{c_j<0}|c_j|`: exactly the normalized form of
    // `sum_j c_j*x_j >= ceil(final_rhs/k)`. Negative objectives are therefore
    // covered without a sign exception.
    let floor = ceil_div_i128(final_rhs, scale).ok_or(PlanError::Arithmetic)?;
    if floor != optimum {
        return Err(PlanError::WrongFloor(floor));
    }
    Ok(lifts)
}

pub(super) fn prepare_plan(
    objective: &Coefficients,
    rows: &[LinearRow],
    num_vars: usize,
    raw: &LpDualRaw,
    scale: &BigInt,
    optimum: i128,
) -> Result<DualPlan, PlanError> {
    let scale_i128 = scale.to_i128().ok_or(PlanError::Arithmetic)?;
    if scale_i128 < 1 {
        return Err(PlanError::Arithmetic);
    }
    let (row_multipliers, box_multipliers) = scaled_multipliers(raw, rows.len(), num_vars, scale)?;
    let aggregate = aggregate_rows(rows, &row_multipliers)?;
    let lifts = reconstruct_lifts(
        objective,
        &aggregate,
        &box_multipliers,
        &raw.complement,
        scale_i128,
        optimum,
    )?;
    if row_multipliers.iter().all(|&multiplier| multiplier == 0) {
        return Err(PlanError::EmptyAggregate);
    }
    Ok(DualPlan {
        row_multipliers,
        box_multipliers,
        complement: raw.complement.clone(),
        lifts,
        scale: scale_i128,
    })
}
