// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact objective-driven continuous singleton-column substitution.
//!
//! A continuous column that occurs in one row can be eliminated when the
//! objective always pushes it to one finite side of that row and the resulting
//! value lies in its declared box for every survivor assignment.  For example,
//!
//! ```text
//! min s       subject to    rest - s <= b,  s >= 0
//! ```
//!
//! has `s = rest-b` at an optimum whenever the survivors' boxes imply
//! `rest-b >= 0`.  Substitution deletes the row and column and folds
//! `rest-b` into the objective.  This is standard singleton-column dual
//! presolve, but the implementation below keeps its exact postsolve and the
//! positive defining-row multiplier needed to lift an optimality proof.

use std::time::Instant;

use num_rational::BigRational;
use num_traits::{Signed, ToPrimitive, Zero};

use crate::model::{exact, Col, ColKind, Model, Row, Sense};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ObjectiveSingletonSide {
    Lower,
    Upper,
}

pub(crate) struct ObjectiveSingletonRecovery {
    pub(crate) col: usize,
    pub(crate) row: usize,
    pub(crate) side: ObjectiveSingletonSide,
    pub(crate) a: BigRational,
    pub(crate) b: BigRational,
    pub(crate) rest: Vec<(usize, BigRational)>,
    /// The ACTUAL (not sense-signed) objective coefficient at this elimination
    /// step.  Earlier eliminations may have folded cost onto this column.
    pub(crate) objective_coeff: BigRational,
}

pub(crate) struct ObjectiveSingletonPostsolve {
    pub(crate) n_orig: usize,
    pub(crate) map: Vec<Option<Col>>,
    pub(crate) recover: Vec<ObjectiveSingletonRecovery>,
    /// Reduced row -> caller row; surviving rows are copied verbatim.
    pub(crate) row_origin: Vec<usize>,
    pub(crate) const_delta: BigRational,
}

impl ObjectiveSingletonPostsolve {
    pub(crate) fn const_delta(&self) -> &BigRational {
        &self.const_delta
    }

    pub(crate) fn widen(&self, reduced: &[BigRational]) -> Vec<BigRational> {
        let mut full = vec![BigRational::zero(); self.n_orig];
        for (original, slot) in self.map.iter().enumerate() {
            if let Some(reduced_col) = slot {
                if let Some(value) = reduced.get(reduced_col.index()) {
                    full[original] = value.clone();
                }
            }
        }
        // A recovery can reference a column eliminated later.  Reverse order
        // restores that dependency before it is read.
        for recovery in self.recover.iter().rev() {
            let mut value = recovery.b.clone();
            for (column, coefficient) in &recovery.rest {
                value -= coefficient * &full[*column];
            }
            full[recovery.col] = value / &recovery.a;
        }
        full
    }
}

fn target_range(
    model: &Model,
    rest: &[(usize, BigRational)],
    b: &BigRational,
    a: &BigRational,
    deadline: Option<Instant>,
) -> Option<(Option<BigRational>, Option<BigRational>)> {
    let mut rest_min = Some(BigRational::zero());
    let mut rest_max = Some(BigRational::zero());
    for (index, (column, coefficient)) in rest.iter().enumerate() {
        if index % 256 == 0 && deadline_expired(deadline) {
            return None;
        }
        let (lower, upper) = model.col_bounds(Col(*column as u32));
        let lower = exact(lower);
        let upper = exact(upper);
        let (at_min, at_max) = if coefficient.is_positive() {
            (lower, upper)
        } else {
            (upper, lower)
        };
        rest_min = match (rest_min, at_min) {
            (Some(sum), Some(bound)) => Some(sum + coefficient * bound),
            _ => None,
        };
        rest_max = match (rest_max, at_max) {
            (Some(sum), Some(bound)) => Some(sum + coefficient * bound),
            _ => None,
        };
    }
    let from_rest = |rest: Option<BigRational>| rest.map(|value| (b - value) / a);
    Some(if a.is_positive() {
        (from_rest(rest_max), from_rest(rest_min))
    } else {
        (from_rest(rest_min), from_rest(rest_max))
    })
}

fn target_inside_declared_box(
    model: &Model,
    column: usize,
    target_lower: &Option<BigRational>,
    target_upper: &Option<BigRational>,
) -> bool {
    let (lower, upper) = model.col_bounds(Col(column as u32));
    let declared_lower = exact(lower);
    let declared_upper = exact(upper);
    let lower_ok = match declared_lower {
        None => true,
        Some(bound) => target_lower.as_ref().is_some_and(|target| target >= &bound),
    };
    let upper_ok = match declared_upper {
        None => true,
        Some(bound) => target_upper.as_ref().is_some_and(|target| target <= &bound),
    };
    lower_ok && upper_ok
}

/// Eliminate every continuous objective singleton exposed by earlier
/// eliminations, to a deterministic fixpoint.
pub(crate) fn substitute_objective_singletons(
    model: &Model,
) -> Option<(Model, ObjectiveSingletonPostsolve)> {
    substitute_objective_singletons_with_deadline(model, None)
}

/// Deadline-bounded form used by speculative production routes. A deadline
/// expiry is a normal decline: no partial transform is ever returned.
pub(crate) fn substitute_objective_singletons_with_deadline(
    model: &Model,
    deadline: Option<Instant>,
) -> Option<(Model, ObjectiveSingletonPostsolve)> {
    if deadline_expired(deadline) {
        return None;
    }
    if model.margin_row().is_some() || !model.has_objective() {
        return None;
    }
    let n = model.num_cols();
    let nr = model.num_rows();
    let mut active_col = vec![true; n];
    let mut active_row = vec![true; nr];
    let mut objective = Vec::with_capacity(n);
    for j in 0..n {
        if j % 256 == 0 && deadline_expired(deadline) {
            return None;
        }
        let coefficient = model.obj_coeff(Col(j as u32));
        objective.push(model.obj_coeff_exact_at(j as u32, coefficient));
    }
    let mut const_delta = BigRational::zero();
    let mut recover = Vec::new();

    loop {
        if deadline_expired(deadline) {
            return None;
        }
        let mut degree = vec![0u8; n];
        let mut only_row = vec![usize::MAX; n];
        for row_index in 0..nr {
            if deadline_expired(deadline) {
                return None;
            }
            if !active_row[row_index] {
                continue;
            }
            let (coeffs, _, _) = model.row(Row(row_index as u32));
            for (term_index, &(column, _)) in coeffs.iter().enumerate() {
                if term_index % 1024 == 0 && deadline_expired(deadline) {
                    return None;
                }
                let j = column as usize;
                if !active_col[j] {
                    // The degree-one invariant says the eliminated column's
                    // only row was deleted with it.  Any survivor reference is
                    // a transform bug, so fail closed rather than drop a term.
                    return None;
                }
                degree[j] = degree[j].saturating_add(1).min(2);
                only_row[j] = row_index;
            }
        }

        let mut chosen = None;
        for column in 0..n {
            if column % 256 == 0 && deadline_expired(deadline) {
                return None;
            }
            if !active_col[column]
                || degree[column] != 1
                || model.col_kind(Col(column as u32)) != ColKind::Continuous
                || objective[column].is_zero()
            {
                continue;
            }
            let row_index = only_row[column];
            let row = Row(row_index as u32);
            let (coeffs, lb_float, ub_float) = model.row(row);
            let lower = model.row_lb_exact(row_index, lb_float);
            let upper = model.row_ub_exact(row_index, ub_float);
            if lower
                .as_ref()
                .zip(upper.as_ref())
                .is_some_and(|(lo, up)| lo > up)
            {
                continue;
            }
            let a = coeffs
                .iter()
                .find(|&&(candidate, _)| candidate as usize == column)
                .map(|&(candidate, value)| model.row_coeff_exact(row_index, candidate, value))?;
            if a.is_zero() {
                continue;
            }
            let signed_objective = match model.sense() {
                Sense::Minimize => objective[column].clone(),
                Sense::Maximize => -&objective[column],
            };
            let side = if a.is_positive() == signed_objective.is_positive() {
                ObjectiveSingletonSide::Lower
            } else {
                ObjectiveSingletonSide::Upper
            };
            let b = match side {
                ObjectiveSingletonSide::Lower => lower.clone(),
                ObjectiveSingletonSide::Upper => upper.clone(),
            };
            let Some(b) = b else { continue };
            let mut rest = Vec::with_capacity(coeffs.len().saturating_sub(1));
            for (term_index, &(candidate, value)) in coeffs.iter().enumerate() {
                if term_index % 256 == 0 && deadline_expired(deadline) {
                    return None;
                }
                if candidate as usize != column {
                    rest.push((
                        candidate as usize,
                        model.row_coeff_exact(row_index, candidate, value),
                    ));
                }
            }
            let (target_lower, target_upper) = target_range(model, &rest, &b, &a, deadline)?;
            if !target_inside_declared_box(model, column, &target_lower, &target_upper) {
                continue;
            }
            chosen = Some((column, row_index, side, a, b, rest));
            break;
        }

        let Some((column, row, side, a, b, rest)) = chosen else {
            break;
        };
        let c = objective[column].clone();
        for (term_index, (survivor, coefficient)) in rest.iter().enumerate() {
            if term_index % 256 == 0 && deadline_expired(deadline) {
                return None;
            }
            objective[*survivor] -= &(&c * coefficient) / &a;
        }
        const_delta += &(&c * &b) / &a;
        objective[column] = BigRational::zero();
        active_col[column] = false;
        active_row[row] = false;
        recover.push(ObjectiveSingletonRecovery {
            col: column,
            row,
            side,
            a,
            b,
            rest,
            objective_coeff: c,
        });
    }

    if recover.is_empty() {
        return None;
    }

    let mut reduced = Model::new();
    reduced.inherit_ft_adoption_solve_latch(model);
    let mut map = vec![None; n];
    for j in 0..n {
        if j % 256 == 0 && deadline_expired(deadline) {
            return None;
        }
        if !active_col[j] {
            continue;
        }
        let original = Col(j as u32);
        let (lower, upper) = model.col_bounds(original);
        let new_col = match model.col_kind(original) {
            ColKind::Continuous => reduced.add_col(lower, upper),
            ColKind::Binary => reduced.add_binary_col(),
            ColKind::Integer => reduced.add_int_col(lower, upper),
        };
        reduced.cols[new_col.index()].lb = lower;
        reduced.cols[new_col.index()].ub = upper;
        map[j] = Some(new_col);
    }

    let mut row_origin = Vec::with_capacity(nr.saturating_sub(recover.len()));
    for row_index in 0..nr {
        if deadline_expired(deadline) {
            return None;
        }
        if !active_row[row_index] {
            continue;
        }
        let (coeffs, lower, upper) = model.row(Row(row_index as u32));
        let mut emitted = Vec::with_capacity(coeffs.len());
        let mut exact_coefficients = Vec::new();
        for (term_index, &(column, coefficient)) in coeffs.iter().enumerate() {
            if term_index % 1024 == 0 && deadline_expired(deadline) {
                return None;
            }
            let mapped = map.get(column as usize).copied().flatten()?;
            let exact_coefficient = model.row_coeff_exact(row_index, column, coefficient);
            if exact_differs_from_proxy(&exact_coefficient, coefficient) {
                exact_coefficients.push((mapped, exact_coefficient));
            }
            emitted.push((mapped, coefficient));
        }
        let reduced_row = reduced.add_row(lower, upper, &emitted);
        for (column, coefficient) in exact_coefficients {
            reduced.record_inexact_row_coeff(reduced_row, column.0, coefficient);
        }
        if let Some(exact_lower) = model.row_lb_exact(row_index, lower) {
            if exact(lower).as_ref() != Some(&exact_lower) {
                reduced.record_inexact_row_bound(reduced_row, true, exact_lower);
            }
        }
        if let Some(exact_upper) = model.row_ub_exact(row_index, upper) {
            if exact(upper).as_ref() != Some(&exact_upper) {
                reduced.record_inexact_row_bound(reduced_row, false, exact_upper);
            }
        }
        row_origin.push(row_index);
    }
    let mut emitted_objective = Vec::new();
    let mut exact_objective = Vec::new();
    for (original, coefficient) in objective.iter().enumerate() {
        if original % 256 == 0 && deadline_expired(deadline) {
            return None;
        }
        if !coefficient.is_zero() {
            let mapped = map.get(original).copied().flatten()?;
            let proxy = coefficient.to_f64()?;
            if !proxy.is_finite() {
                return None;
            }
            if exact_differs_from_proxy(coefficient, proxy) {
                exact_objective.push((mapped, coefficient.clone()));
            }
            emitted_objective.push((mapped, proxy));
        }
    }
    reduced.set_objective(&emitted_objective, model.sense());
    for (column, coefficient) in exact_objective {
        reduced.record_inexact_obj_coeff(column.0, coefficient);
    }
    reduced.set_objective_offset(model.objective_offset());
    let exact_offset = model.obj_offset_exact();
    if exact_differs_from_proxy(&exact_offset, model.objective_offset()) {
        reduced.record_inexact_obj_offset(exact_offset);
    }

    if trace_enabled() {
        eprintln!(
            "AY_MILP_TRACE objective-singleton-sub: eliminated {} continuous cols/rows; \
             model {nr}r/{n}c -> {}r/{}c",
            recover.len(),
            reduced.num_rows(),
            reduced.num_cols(),
        );
    }
    Some((
        reduced,
        ObjectiveSingletonPostsolve {
            n_orig: n,
            map,
            recover,
            row_origin,
            const_delta,
        },
    ))
}

fn deadline_expired(deadline: Option<Instant>) -> bool {
    deadline.is_some_and(|deadline| Instant::now() >= deadline)
}

fn exact_differs_from_proxy(value: &BigRational, proxy: f64) -> bool {
    BigRational::from_float(proxy).as_ref() != Some(value)
}

#[cfg(test)]
mod tests {
    use num_traits::One;

    use super::*;

    #[test]
    fn aggregate_slack_exposes_and_eliminates_a_second_layer() {
        let mut model = Model::new();
        let t = model.add_int_col(5.0, 10.0);
        let slack = model.add_col(0.0, f64::INFINITY);
        let aggregate = model.add_col(0.0, f64::INFINITY);
        model.add_row(f64::NEG_INFINITY, 3.0, &[(t, 1.0), (slack, -1.0)]);
        model.add_row(f64::NEG_INFINITY, 0.0, &[(slack, 1.0), (aggregate, -1.0)]);
        model.set_objective(&[(aggregate, 1.0)], Sense::Minimize);

        let (reduced, post) =
            substitute_objective_singletons(&model).expect("both layers eliminate");
        assert_eq!(reduced.num_cols(), 1);
        assert_eq!(reduced.num_rows(), 0);
        assert_eq!(post.recover.len(), 2);
        assert_eq!(reduced.obj_coeff(Col(0)), 1.0);
        assert_eq!(*post.const_delta(), BigRational::from_integer((-3).into()));
        let reduced_point = vec![BigRational::from_integer(7.into())];
        let full = post.widen(&reduced_point);
        assert_eq!(
            full,
            vec![
                BigRational::from_integer(7.into()),
                BigRational::from_integer(4.into()),
                BigRational::from_integer(4.into())
            ]
        );
        assert!(model.check_point(&full).is_ok());
        assert_eq!(
            model.objective_value_at(&full),
            reduced.objective_value_at(&reduced_point) + post.const_delta()
        );
    }

    #[test]
    fn rational_fold_stays_available_to_exact_routes() {
        let mut model = Model::new();
        let decision = model.add_binary_col();
        let objective = model.add_col(f64::NEG_INFINITY, f64::INFINITY);
        // 10*objective - decision = 0, hence objective = decision/10.
        // The transform is exact even though its f64 advice coefficient 0.1
        // cannot represent the authoritative rational 1/10.
        model.add_row(0.0, 0.0, &[(objective, 10.0), (decision, -1.0)]);
        model.set_objective(&[(objective, 1.0)], Sense::Minimize);

        let (reduced, post) =
            substitute_objective_singletons(&model).expect("singleton must eliminate");
        assert_eq!(reduced.num_cols(), 1);
        assert_eq!(reduced.num_rows(), 0);
        assert!(
            reduced.has_inexact_objective_coeffs(),
            "the exact 1/10 cost must remain in the side store"
        );
        let reduced_decision = post.map[decision.index()].expect("decision survives");
        assert_eq!(
            reduced.obj_coeff_exact_at(reduced_decision.0, reduced.obj_coeff(reduced_decision)),
            BigRational::new(1.into(), 10.into())
        );

        let reduced_point = vec![BigRational::one()];
        let full = post.widen(&reduced_point);
        assert!(model.check_point(&full).is_ok());
        assert_eq!(
            full[objective.index()],
            BigRational::new(1.into(), 10.into())
        );
        assert_eq!(
            model.objective_value_at(&full),
            reduced.objective_value_at(&reduced_point) + post.const_delta()
        );
    }

    #[test]
    fn a_box_that_can_bind_before_the_row_declines_piecewise_elimination() {
        let mut model = Model::new();
        let t = model.add_int_col(0.0, 10.0);
        let slack = model.add_col(0.0, f64::INFINITY);
        model.add_row(f64::NEG_INFINITY, 3.0, &[(t, 1.0), (slack, -1.0)]);
        model.set_objective(&[(slack, 1.0)], Sense::Minimize);
        // s=max(0,t-3), not one affine expression over t's box.
        assert!(substitute_objective_singletons(&model).is_none());
    }

    #[test]
    fn maximization_uses_the_opposite_oriented_row_side() {
        let mut model = Model::new();
        let t = model.add_int_col(0.0, 5.0);
        let reward = model.add_col(f64::NEG_INFINITY, 10.0);
        model.add_row(0.0, f64::INFINITY, &[(t, -1.0), (reward, -1.0)]);
        model.set_objective(&[(reward, 1.0)], Sense::Maximize);
        let (reduced, post) = substitute_objective_singletons(&model).expect("upper target");
        assert_eq!(post.recover[0].side, ObjectiveSingletonSide::Lower);
        let full = post.widen(&[BigRational::one()]);
        assert_eq!(full[1], BigRational::from_integer((-1).into()));
        assert!(model.check_point(&full).is_ok());
        assert_eq!(reduced.obj_coeff(Col(0)), -1.0);
    }

    #[test]
    fn expired_deadline_declines_without_a_partial_transform() {
        let mut model = Model::new();
        let decision = model.add_binary_col();
        let cost = model.add_col(f64::NEG_INFINITY, f64::INFINITY);
        model.add_row(0.0, 0.0, &[(cost, 1.0), (decision, -2.0)]);
        model.set_objective(&[(cost, 1.0)], Sense::Minimize);

        assert!(
            substitute_objective_singletons_with_deadline(&model, Some(Instant::now())).is_none()
        );
    }
}

/// Cached trace predicate; see the live-read ratchet in `tests/env_ledger.rs`.
fn trace_enabled() -> bool {
    static ENABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ENABLED.get_or_init(|| std::env::var_os("AY_MILP_TRACE").is_some())
}

/// Force this module's cached env accessor at solve entry, so a consumer that
/// rewrites its environment between window solves cannot race it. Called from
/// `bab::prime_env_all`.
pub(crate) fn prime_env() {
    let _ = trace_enabled();
}
