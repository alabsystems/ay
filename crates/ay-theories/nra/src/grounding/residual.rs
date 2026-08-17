// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact pin substitution and private linear residual solving.

use ay_core::term::TermId;
use ay_core::{TheoryResult, TheorySolver};
use num_rational::BigRational;
use num_traits::{One, Zero};

use crate::univariate::{rational_sign, MultiPoly, Rel};
use crate::NraSolver;

use super::GroundingPlan;

type LinearTerms = Vec<(TermId, BigRational)>;

struct ResidualSystem {
    intervals: Vec<(TermId, Interval)>,
    coupled: Vec<(BigRational, LinearTerms, Rel)>,
    relaxed: usize,
}

/// Solve one exact pin substitution.  The return value is a candidate only
/// after the final original-atom verification at the bottom of this function.
pub(super) fn solve_grounded_residual(
    nra: &NraSolver<'_>,
    pins: &[(TermId, BigRational)],
    plan: &GroundingPlan,
) -> Option<Vec<(TermId, BigRational)>> {
    let pin_map: crate::HashMap<TermId, &BigRational> = pins
        .iter()
        .map(|(variable, value)| (*variable, value))
        .collect();
    let residual = partition_residuals(plan, &pin_map)?;
    let (linear_model, coupled_vars) = solve_private_linear_system(nra, &residual)?;
    let model = assemble_candidate(
        plan,
        &pin_map,
        &residual.intervals,
        &linear_model,
        &coupled_vars,
    )?;

    // Load-bearing soundness gate: no residual verdict, relaxed constraint,
    // cover invariant, or LRA model is trusted.  Every original nonlinear atom
    // must hold under exact BigRational evaluation.
    if !nra.verify_model(&model) {
        if nra.debug {
            tracing::debug!(
                "[NRA] grounding candidate rejected ({} pins, {} coupled, {} relaxed)",
                pins.len(),
                residual.coupled.len(),
                residual.relaxed
            );
        }
        return None;
    }
    Some(model)
}

fn partition_residuals(
    plan: &GroundingPlan,
    pins: &crate::HashMap<TermId, &BigRational>,
) -> Option<ResidualSystem> {
    let mut system = ResidualSystem {
        intervals: Vec::new(),
        coupled: Vec::new(),
        relaxed: 0,
    };
    for constraint in &plan.constraints {
        let Some((constant, linear)) = substitute_pins(&constraint.poly, pins) else {
            system.relaxed += 1;
            continue;
        };
        match linear.as_slice() {
            [] => {
                if !constraint.rel.holds_for_sign(rational_sign(&constant)) {
                    return None;
                }
            }
            [(variable, coefficient)] => {
                if matches!(constraint.rel, Rel::Ne) {
                    system.relaxed += 1;
                    continue;
                }
                let bound = -constant / coefficient;
                let relation = if coefficient < &BigRational::zero() {
                    mirror(constraint.rel)
                } else {
                    constraint.rel
                };
                let interval = interval_for(&mut system.intervals, *variable);
                if !interval.tighten(&bound, relation) {
                    return None;
                }
            }
            _ if matches!(constraint.rel, Rel::Ne) => system.relaxed += 1,
            _ => system.coupled.push((constant, linear, constraint.rel)),
        }
    }
    Some(system)
}

fn interval_for(intervals: &mut Vec<(TermId, Interval)>, variable: TermId) -> &mut Interval {
    if let Some(slot) = intervals
        .iter()
        .position(|(candidate, _)| *candidate == variable)
    {
        return &mut intervals[slot].1;
    }
    intervals.push((variable, Interval::unbounded()));
    let last = intervals.len() - 1;
    &mut intervals[last].1
}

fn solve_private_linear_system(
    nra: &NraSolver<'_>,
    residual: &ResidualSystem,
) -> Option<(ay_lra::LraSolver, crate::HashSet<TermId>)> {
    let mut solver = ay_lra::LraSolver::new(nra.terms);
    solver.set_combined_theory_mode(true);
    let mut coupled_vars = crate::HashSet::default();

    for (constant, linear, relation) in &residual.coupled {
        let coefficients: Vec<(u32, BigRational)> = linear
            .iter()
            .map(|(variable, coefficient)| {
                coupled_vars.insert(*variable);
                (solver.ensure_var_registered(*variable), coefficient.clone())
            })
            .collect();
        assert_relation(
            &mut solver,
            &coefficients,
            &-constant,
            *relation,
            linear[0].0,
        );
    }
    for (variable, interval) in &residual.intervals {
        let lra_variable = solver.ensure_var_registered(*variable);
        let coefficient = [(lra_variable, BigRational::one())];
        if let Some((value, strict)) = &interval.lower {
            solver.assert_linear_bound(&coefficient, value, true, *strict, *variable);
        }
        if let Some((value, strict)) = &interval.upper {
            solver.assert_linear_bound(&coefficient, value, false, *strict, *variable);
        }
    }

    if !residual.coupled.is_empty()
        && !matches!(
            nra.normalize_lra_result(TheorySolver::check(&mut solver)),
            TheoryResult::Sat | TheoryResult::Unknown
        )
    {
        return None;
    }
    Some((solver, coupled_vars))
}

fn assert_relation(
    solver: &mut ay_lra::LraSolver,
    coefficients: &[(u32, BigRational)],
    bound: &BigRational,
    relation: Rel,
    reason: TermId,
) {
    match relation {
        Rel::Eq => {
            solver.assert_linear_bound(coefficients, bound, true, false, reason);
            solver.assert_linear_bound(coefficients, bound, false, false, reason);
        }
        Rel::Le => solver.assert_linear_bound(coefficients, bound, false, false, reason),
        Rel::Lt => solver.assert_linear_bound(coefficients, bound, false, true, reason),
        Rel::Ge => solver.assert_linear_bound(coefficients, bound, true, false, reason),
        Rel::Gt => solver.assert_linear_bound(coefficients, bound, true, true, reason),
        Rel::Ne => unreachable!("disequalities are relaxed before private LRA assertion"),
    }
}

fn assemble_candidate(
    plan: &GroundingPlan,
    pins: &crate::HashMap<TermId, &BigRational>,
    intervals: &[(TermId, Interval)],
    linear_model: &ay_lra::LraSolver,
    coupled_vars: &crate::HashSet<TermId>,
) -> Option<Vec<(TermId, BigRational)>> {
    let mut model = Vec::with_capacity(plan.model_vars.len());
    for &variable in &plan.model_vars {
        let value = if let Some(value) = pins.get(&variable) {
            (*value).clone()
        } else if coupled_vars.contains(&variable) {
            linear_model
                .get_value(variable)
                .unwrap_or_else(BigRational::zero)
        } else if let Some((_, interval)) = intervals
            .iter()
            .find(|(candidate, _)| *candidate == variable)
        {
            interval.sample()?
        } else {
            BigRational::zero()
        };
        model.push((variable, value));
    }
    Some(model)
}

/// Exact feasible interval for one residual variable.  It is handled outside
/// the simplex because a row-less variable with contradictory direct bounds is
/// not detected by a bare private `LraSolver`.
#[derive(Clone, Debug, Default)]
pub(super) struct Interval {
    pub(super) lower: Option<(BigRational, bool)>,
    pub(super) upper: Option<(BigRational, bool)>,
}

impl Interval {
    pub(super) fn unbounded() -> Self {
        Self::default()
    }

    pub(super) fn tighten(&mut self, bound: &BigRational, relation: Rel) -> bool {
        match relation {
            Rel::Ge => self.raise_lower(bound.clone(), false),
            Rel::Gt => self.raise_lower(bound.clone(), true),
            Rel::Le => self.lower_upper(bound.clone(), false),
            Rel::Lt => self.lower_upper(bound.clone(), true),
            Rel::Eq => {
                self.raise_lower(bound.clone(), false) && self.lower_upper(bound.clone(), false)
            }
            Rel::Ne => false,
        }
    }

    fn raise_lower(&mut self, value: BigRational, strict: bool) -> bool {
        let tighter = match &self.lower {
            None => true,
            Some((current, current_strict)) => {
                value > *current || (value == *current && strict && !current_strict)
            }
        };
        if tighter {
            self.lower = Some((value, strict));
        }
        self.nonempty()
    }

    fn lower_upper(&mut self, value: BigRational, strict: bool) -> bool {
        let tighter = match &self.upper {
            None => true,
            Some((current, current_strict)) => {
                value < *current || (value == *current && strict && !current_strict)
            }
        };
        if tighter {
            self.upper = Some((value, strict));
        }
        self.nonempty()
    }

    fn nonempty(&self) -> bool {
        match (&self.lower, &self.upper) {
            (Some((lower, lower_strict)), Some((upper, upper_strict))) => {
                lower < upper || (lower == upper && !lower_strict && !upper_strict)
            }
            _ => true,
        }
    }

    pub(super) fn sample(&self) -> Option<BigRational> {
        match (&self.lower, &self.upper) {
            (None, None) => Some(BigRational::zero()),
            (Some((lower, strict)), None) => Some(if *strict {
                lower + BigRational::one()
            } else {
                lower.clone()
            }),
            (None, Some((upper, strict))) => Some(if *strict {
                upper - BigRational::one()
            } else {
                upper.clone()
            }),
            (Some((lower, lower_strict)), Some((upper, upper_strict))) => {
                sample_bounded(lower, *lower_strict, upper, *upper_strict)
            }
        }
    }
}

fn sample_bounded(
    lower: &BigRational,
    lower_strict: bool,
    upper: &BigRational,
    upper_strict: bool,
) -> Option<BigRational> {
    if lower == upper {
        return (!lower_strict && !upper_strict).then(|| lower.clone());
    }
    if lower > upper {
        return None;
    }
    if lower_strict || upper_strict {
        Some((lower + upper) / BigRational::from_integer(2.into()))
    } else {
        Some(lower.clone())
    }
}

fn mirror(relation: Rel) -> Rel {
    match relation {
        Rel::Lt => Rel::Gt,
        Rel::Le => Rel::Ge,
        Rel::Ge => Rel::Le,
        Rel::Gt => Rel::Lt,
        Rel::Eq => Rel::Eq,
        Rel::Ne => Rel::Ne,
    }
}

pub(super) fn substitute_pins(
    poly: &MultiPoly,
    pins: &crate::HashMap<TermId, &BigRational>,
) -> Option<(BigRational, LinearTerms)> {
    let mut constant = BigRational::zero();
    let mut linear = Vec::new();
    for (monomial, coefficient) in &poly.terms {
        let mut value = coefficient.clone();
        let mut free = None;
        for factor in monomial {
            if let Some(pinned) = pins.get(factor) {
                value *= *pinned;
            } else if free.is_some() {
                return None;
            } else {
                free = Some(*factor);
            }
        }
        if value.is_zero() {
            continue;
        }
        match free {
            None => constant += value,
            Some(variable) => add_linear_term(&mut linear, variable, value),
        }
    }
    linear.retain(|(_, coefficient)| !coefficient.is_zero());
    Some((constant, linear))
}

fn add_linear_term(linear: &mut LinearTerms, variable: TermId, coefficient: BigRational) {
    if let Some((_, current)) = linear
        .iter_mut()
        .find(|(candidate, _)| *candidate == variable)
    {
        *current += coefficient;
    } else {
        linear.push((variable, coefficient));
    }
}
