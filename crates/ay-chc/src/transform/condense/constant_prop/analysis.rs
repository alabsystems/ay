// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The same bounded, typed pin analysis is used in BOTH dataflow phases.

use ay_core::kani_compat::DetHashMap as FxHashMap;

use crate::{ChcExpr, ChcOp, ChcProblem, ChcVar, ClauseHead, HornClause, PredicateId};

use super::evaluate::{evaluate, Pins};
use super::ground::{Budget, Stopped, Value};

type Position = (PredicateId, usize);
type Values = FxHashMap<Position, Cpv>;
const MAX_POSITIONS: usize = 16_384;
const MAX_PINS: usize = 1024;

// Structural equality only determines convergence. Logical equality must use
// Value::equivalent, including in justification and contradictory-pin checks.
#[derive(Clone, Debug, PartialEq)]
enum Cpv {
    Unknown,
    Const(Value),
    Varies,
}

pub(super) fn constants(
    problem: &ChcProblem,
    budget: &mut Budget,
) -> Result<FxHashMap<PredicateId, Vec<(usize, ChcExpr)>>, Stopped> {
    let values = optimistic_fixpoint(problem, budget)?;
    let values = justify(problem, values, budget)?;
    let mut result: FxHashMap<PredicateId, Vec<(usize, ChcExpr)>> = FxHashMap::default();
    for ((pid, index), value) in values {
        budget.charge(1)?;
        if let Cpv::Const(value) = value {
            result
                .entry(pid)
                .or_default()
                .push((index, value.to_expr(budget)?));
        }
    }
    for positions in result.values_mut() {
        budget.charge(positions.len())?;
        positions.sort_by_key(|(index, _)| *index);
    }
    budget.charge(0)?;
    Ok(result)
}

/// None means a PROVED contradictory conjunction, never analysis exhaustion.
fn clause_pins(
    clause: &HornClause,
    values: &Values,
    budget: &mut Budget,
) -> Result<Option<(Pins, bool)>, Stopped> {
    let mut pins = Pins::default();
    let mut unknown = false;
    for (pid, args) in &clause.body.predicates {
        for (index, arg) in args.iter().enumerate() {
            budget.charge(1)?;
            let ChcExpr::Var(var) = arg else { continue };
            match values.get(&(*pid, index)) {
                Some(Cpv::Const(value)) => {
                    if !insert_pin(&mut pins, var, value.clone(), budget)? {
                        return Ok(None);
                    }
                }
                Some(Cpv::Unknown) => unknown = true,
                _ => {}
            }
        }
    }
    let equations = constraint_equations(clause, budget)?;
    loop {
        let old_len = pins.len();
        for (var, rhs) in &equations {
            budget.charge(1)?;
            if let Some(value) = evaluate(rhs, &pins, budget, 0)? {
                if !insert_pin(&mut pins, var, value, budget)? {
                    return Ok(None);
                }
            }
        }
        if old_len == pins.len() {
            return Ok(Some((pins, unknown)));
        }
    }
}

fn insert_pin(
    pins: &mut Pins,
    var: &ChcVar,
    value: Value,
    budget: &mut Budget,
) -> Result<bool, Stopped> {
    budget.charge(var.name.len() + 1)?;
    if !value.matches_sort(&var.sort) {
        // Ill-typed inputs are not evidence of a vacuous clause.
        return Err(budget.stop());
    }
    match pins.get(var) {
        Some(existing) => existing.equivalent(&value, budget),
        None => {
            if pins.len() >= MAX_PINS {
                return Err(budget.stop());
            }
            pins.insert(var.clone(), value);
            Ok(true)
        }
    }
}

fn constraint_equations<'a>(
    clause: &'a HornClause,
    budget: &mut Budget,
) -> Result<Vec<(&'a ChcVar, &'a ChcExpr)>, Stopped> {
    let mut equations = Vec::new();
    let mut pending = Vec::new();
    if let Some(constraint) = &clause.body.constraint {
        pending.push(constraint);
    }
    while let Some(expr) = pending.pop() {
        budget.charge(1)?;
        match expr {
            ChcExpr::Op(ChcOp::And, args) => {
                budget.charge(args.len())?;
                pending.extend(args.iter().map(AsRef::as_ref));
            }
            ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
                for (lhs, rhs) in [
                    (args[0].as_ref(), args[1].as_ref()),
                    (args[1].as_ref(), args[0].as_ref()),
                ] {
                    if let ChcExpr::Var(var) = lhs {
                        equations.push((var, rhs));
                    }
                }
            }
            _ => {}
        }
    }
    Ok(equations)
}

fn eval_head(
    arg: &ChcExpr,
    pins: &Pins,
    unknown: bool,
    budget: &mut Budget,
) -> Result<Cpv, Stopped> {
    Ok(match evaluate(arg, pins, budget, 0)? {
        Some(value) => Cpv::Const(value),
        None if unknown && matches!(arg, ChcExpr::Var(_)) => Cpv::Unknown,
        None => Cpv::Varies,
    })
}

fn join(left: Cpv, right: Cpv, budget: &mut Budget) -> Result<Cpv, Stopped> {
    budget.charge(1)?;
    Ok(match (left, right) {
        (Cpv::Unknown, other) | (other, Cpv::Unknown) => other,
        (Cpv::Varies, _) | (_, Cpv::Varies) => Cpv::Varies,
        (Cpv::Const(a), Cpv::Const(b)) => {
            if a.equivalent(&b, budget)? {
                Cpv::Const(a)
            } else {
                Cpv::Varies
            }
        }
    })
}

/// Validate occurrence arities and constant head sorts while initializing the
/// table. Unbounded declarations cannot allocate an unbounded candidate map.
fn initial_values(problem: &ChcProblem, budget: &mut Budget) -> Result<Values, Stopped> {
    let mut values = Values::default();
    for pred in problem.predicates() {
        if pred.arity() > MAX_POSITIONS.saturating_sub(values.len()) {
            return Err(budget.stop());
        }
        budget.charge(pred.arity() + 1)?;
        for index in 0..pred.arity() {
            values.insert((pred.id, index), Cpv::Unknown);
        }
    }
    for clause in problem.clauses() {
        budget.charge(1)?;
        let head = match &clause.head {
            ClauseHead::Predicate(pid, args) => Some((pid, args)),
            ClauseHead::False => None,
        };
        for (pid, args) in clause
            .body
            .predicates
            .iter()
            .map(|(p, a)| (p, a))
            .chain(head)
        {
            budget.charge(args.len() + 1)?;
            let pred = problem.get_predicate(*pid).ok_or_else(|| budget.stop())?;
            if pred.arity() != args.len() {
                return Err(budget.stop());
            }
            for (arg, sort) in args.iter().zip(&pred.arg_sorts) {
                if let ChcExpr::Var(var) = arg {
                    if &var.sort != sort {
                        return Err(budget.stop());
                    }
                }
            }
        }
    }
    Ok(values)
}

/// The cap is retained: vacuity under optimistic pins need not be monotone.
/// Only the subsequent COMPLETE justification grants a constant authority.
fn optimistic_fixpoint(problem: &ChcProblem, budget: &mut Budget) -> Result<Values, Stopped> {
    let mut values = initial_values(problem, budget)?;
    let max_sweeps = values.len().saturating_mul(2).saturating_add(4);
    for _ in 0..max_sweeps {
        budget.charge(values.len() + 1)?;
        let mut next: Values = values.keys().map(|key| (*key, Cpv::Unknown)).collect();
        for clause in problem.clauses() {
            budget.charge(1)?;
            let ClauseHead::Predicate(pid, args) = &clause.head else {
                continue;
            };
            let Some((pins, unknown)) = clause_pins(clause, &values, budget)? else {
                continue;
            };
            let pred = problem.get_predicate(*pid).ok_or_else(|| budget.stop())?;
            for (index, arg) in args.iter().enumerate() {
                let value = eval_head(arg, &pins, unknown, budget)?;
                if let Cpv::Const(value) = &value {
                    if !value.matches_sort(&pred.arg_sorts[index]) {
                        return Err(budget.stop());
                    }
                }
                let slot = next.get_mut(&(*pid, index)).ok_or_else(|| budget.stop())?;
                *slot = join(slot.clone(), value, budget)?;
            }
        }
        // Convergence comparison also touches array maps. Reserve the actual
        // stored representation sizes before relying on structural Eq.
        for value in values.values() {
            budget.charge(match value {
                Cpv::Const(value) => value.comparison_cost(),
                _ => 1,
            })?;
        }
        if next == values {
            break;
        }
        values = next;
    }
    Ok(values)
}

fn justify(
    problem: &ChcProblem,
    mut values: Values,
    budget: &mut Budget,
) -> Result<Values, Stopped> {
    loop {
        let mut demote = Vec::new();
        for clause in problem.clauses() {
            budget.charge(1)?;
            let ClauseHead::Predicate(pid, args) = &clause.head else {
                continue;
            };
            let Some((pins, _)) = clause_pins(clause, &values, budget)? else {
                continue;
            };
            for (index, arg) in args.iter().enumerate() {
                budget.charge(1)?;
                let Some(Cpv::Const(expected)) = values.get(&(*pid, index)) else {
                    continue;
                };
                match eval_head(arg, &pins, false, budget)? {
                    Cpv::Const(value) if value.equivalent(expected, budget)? => {}
                    _ => demote.push((*pid, index)),
                }
            }
        }
        if demote.is_empty() {
            return Ok(values);
        }
        for position in demote {
            values.insert(position, Cpv::Varies);
        }
    }
}
