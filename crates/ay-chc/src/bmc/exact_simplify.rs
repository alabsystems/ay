// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Fallible orchestration of the exact-path simplifier.
//!
//! Explicit substitutions and phase boundaries share the original expansion's
//! admission/control context. Existing algebraic simplifiers retain their
//! semantics; this is not a per-operation latency bound on those routines.

use super::{AcyclicNames, BmcSolver, ChcExpr, ChcSort, FxHashMap, IntInterval};

mod booleans;
mod bounds;
mod definitions;
mod expression;
mod squares;
use bounds::collect_bounds;
use expression::simplify_expression;
pub(super) use squares::linearize as linearize_squares;

pub(super) fn simplify(conjuncts: Vec<ChcExpr>, names: &mut AcyclicNames<'_>) -> Option<ChcExpr> {
    let combined = conjunction(conjuncts, names)?;
    let combined = propagate(combined, names)?;
    let mut conjuncts = combined.collect_conjuncts_nontrivial();
    names.check_all(&conjuncts)?;
    let mut env = FxHashMap::default();
    if infeasible(&conjuncts, &mut env, names)? {
        return finish(ChcExpr::Bool(false), names);
    }
    substitute_intervals(&mut conjuncts, &env, names)?;
    if infeasible(&conjuncts, &mut env, names)? {
        return finish(ChcExpr::Bool(false), names);
    }

    // This established step is an overapproximation, not an equivalence:
    // UNSAT is useful for safety, while SAT still needs original-clause replay.
    squares::linearize(&mut conjuncts, &env, names)?;
    if infeasible(&conjuncts, &mut env, names)? {
        return finish(ChcExpr::Bool(false), names);
    }
    substitute_intervals(&mut conjuncts, &env, names)?;
    if infeasible(&conjuncts, &mut env, names)? {
        return finish(ChcExpr::Bool(false), names);
    }

    names.check_all(&conjuncts)?;
    let mut local_bools = super::FxHashSet::default();
    for conjunct in &conjuncts {
        names.poll()?;
        for variable in conjunct.vars() {
            names.poll()?;
            if variable.sort == ChcSort::Bool {
                local_bools.insert(variable.name);
            }
        }
    }
    booleans::simplify(&mut conjuncts, &mut env, &local_bools, names)?;
    substitute_intervals(&mut conjuncts, &env, names)?;
    if conjuncts.len() <= 512 {
        definitions::substitute(&mut conjuncts, names)?;
    }
    let combined = conjunction(conjuncts, names)?;
    propagate(combined, names)
}

fn conjunction(conjuncts: Vec<ChcExpr>, names: &mut AcyclicNames<'_>) -> Option<ChcExpr> {
    names.check_all(&conjuncts)?;
    let combined = ChcExpr::and_all_checked(conjuncts, || names.poll().is_none())?;
    finish(combined, names)
}

fn finish(expression: ChcExpr, names: &mut AcyclicNames<'_>) -> Option<ChcExpr> {
    names.check(&expression)?;
    Some(expression)
}

fn propagate(mut expression: ChcExpr, names: &mut AcyclicNames<'_>) -> Option<ChcExpr> {
    // Preserve the established five-round literal propagation. Even literal
    // substitution can be followed by growing ITE/constant rewrites, so admit
    // every result before another round's census or substitution.
    for _ in 0..5 {
        names.check(&expression)?;
        let equalities = expression.extract_var_const_equalities();
        names.poll()?;
        if equalities.is_empty() {
            return finish(expression, names);
        }
        let mut substitutions = Vec::with_capacity(equalities.len());
        for (variable, value) in equalities {
            names.poll()?;
            // Preserve full ChcVar identity (including sort), exactly as the
            // established propagation pass does for even raw input ASTs.
            substitutions.push((variable, ChcExpr::Int(value)));
        }
        let result = names
            .substitute_typed(&expression, &substitutions)?
            .simplify_constants();
        names.check(&result)?;
        if result == expression || matches!(result, ChcExpr::Bool(_)) {
            return finish(result, names);
        }
        expression = result;
    }
    finish(expression, names)
}

fn infeasible(
    conjuncts: &[ChcExpr],
    env: &mut FxHashMap<String, IntInterval>,
    names: &mut AcyclicNames<'_>,
) -> Option<bool> {
    collect_bounds(conjuncts, env, names).map(|feasible| !feasible)
}

fn substitute_intervals(
    conjuncts: &mut Vec<ChcExpr>,
    env: &FxHashMap<String, IntInterval>,
    names: &mut AcyclicNames<'_>,
) -> Option<()> {
    names.check_all(conjuncts)?;
    let mut substitutions = FxHashMap::default();
    for (name, interval) in env {
        names.poll()?;
        if let (Some(lower), Some(upper)) = (interval.lower, interval.upper) {
            if lower == upper {
                substitutions.insert(name.clone(), ChcExpr::Int(lower));
            }
        }
    }
    if substitutions.is_empty() {
        return names.poll();
    }
    let mut result = Vec::with_capacity(conjuncts.len());
    for conjunct in conjuncts.iter() {
        let substituted = names.substitute(conjunct, &substitutions)?;
        match simplify_expression(substituted, names)? {
            ChcExpr::Bool(true) => {}
            ChcExpr::Bool(false) => {
                result.clear();
                result.push(ChcExpr::Bool(false));
                break;
            }
            other => result.push(other),
        }
    }
    names.check_all(&result)?;
    *conjuncts = result;
    names.poll()
}

#[cfg(test)]
mod tests;
