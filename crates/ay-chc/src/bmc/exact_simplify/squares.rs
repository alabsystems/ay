// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Checked square-envelope relaxation for acyclic expansion callers.
//!
//! The envelope preserves every original model but can admit extra models.
//! UNSAT remains useful; SAT still needs original-clause witness replay.

use super::{simplify_expression, AcyclicNames, BmcSolver, ChcExpr, FxHashMap, IntInterval};
use crate::bmc::BoundedSquareDefinition;
use crate::{ChcSort, ChcVar};
use ay_core::kani_compat::DetHashSet;
use std::sync::Arc;

mod rewrite;

pub(in crate::bmc) fn linearize(
    conjuncts: &mut Vec<ChcExpr>,
    env: &FxHashMap<String, IntInterval>,
    names: &mut AcyclicNames<'_>,
) -> Option<usize> {
    names.check_all(conjuncts)?;
    let Some((output, count)) = build(conjuncts, env, names)? else {
        names.poll()?;
        return Some(0);
    };
    // All replacement/discovery scratch has been dropped. No fallible work
    // follows this admission, so a refused call leaves the input untouched.
    names.check_all(&output)?;
    names.poll()?;
    *conjuncts = output;
    Some(count)
}

fn build(
    conjuncts: &[ChcExpr],
    env: &FxHashMap<String, IntInterval>,
    names: &mut AcyclicNames<'_>,
) -> Option<Option<(Vec<ChcExpr>, usize)>> {
    let mut definitions = Vec::new();
    let mut replacements = FxHashMap::default();
    for conjunct in conjuncts {
        names.poll()?;
        if let Some(definition) = BmcSolver::bounded_square_definition(conjunct, env) {
            replacements.insert(
                definition.square.clone(),
                ChcExpr::var(definition.product.clone()),
            );
            definitions.push(definition);
        }
    }
    let (mut used, squares) = discover(conjuncts, env, names)?;
    let mut standalone = Vec::new();
    for square in squares {
        names.poll()?;
        if replacements.contains_key(&square) {
            continue;
        }
        let Some(input) = BmcSolver::square_input_var(&square) else {
            continue;
        };
        let Some(interval) = env.get(&input.name).copied() else {
            continue;
        };
        if interval.bounded_nonnegative_square_domain().is_none() {
            continue;
        }
        let product = loop {
            let candidate = names.square_name()?;
            if used.insert(candidate.clone()) {
                break ChcVar::new(candidate, ChcSort::Int);
            }
        };
        replacements.insert(square.clone(), ChcExpr::var(product.clone()));
        standalone.push(BoundedSquareDefinition {
            product,
            input,
            square,
            interval,
        });
    }
    let Some(count) = definitions.len().checked_add(standalone.len()) else {
        return names.refuse();
    };
    if count == 0 {
        return Some(None);
    }

    let mut output = Vec::new();
    for definition in &standalone {
        append_envelope(&mut output, definition, names)?;
    }
    for conjunct in conjuncts {
        names.poll()?;
        if let Some(definition) = BmcSolver::bounded_square_definition(conjunct, env) {
            append_envelope(&mut output, &definition, names)?;
        } else {
            let replaced = rewrite::replace(conjunct, &replacements, names)?;
            output.push(simplify_expression(replaced, names)?);
        }
    }
    names.check_all(&output)?;
    Some(Some((output, count)))
}

fn append_envelope(
    output: &mut Vec<ChcExpr>,
    definition: &BoundedSquareDefinition,
    names: &mut AcyclicNames<'_>,
) -> Option<()> {
    names.poll()?;
    // The established finite-domain envelope arithmetic is unchanged. Its
    // individual pure operations remain opaque; admit every output before use.
    for expression in BmcSolver::bounded_square_lia_envelope(definition) {
        names.poll()?;
        output.push(simplify_expression(expression, names)?);
    }
    names.check_all(output)
}

fn discover(
    conjuncts: &[ChcExpr],
    env: &FxHashMap<String, IntInterval>,
    names: &mut AcyclicNames<'_>,
) -> Option<(DetHashSet<String>, DetHashSet<ChcExpr>)> {
    let mut used = DetHashSet::default();
    let mut squares = DetHashSet::default();
    let mut seen = DetHashSet::default();
    let mut pending = Vec::new();
    for conjunct in conjuncts {
        pending.push(conjunct);
        while let Some(expression) = pending.pop() {
            names.poll()?;
            // All borrowed inputs stay alive through discovery. Identity
            // avoids repeated walks of shared nodes, not semantic decisions.
            if !seen.insert(std::ptr::from_ref(expression)) {
                continue;
            }
            if let Some(input) = BmcSolver::square_input_var(expression) {
                if env
                    .get(&input.name)
                    .copied()
                    .and_then(IntInterval::bounded_nonnegative_square_domain)
                    .is_some()
                {
                    squares.insert(expression.clone());
                }
            }
            let children: &[Arc<ChcExpr>] = match expression {
                ChcExpr::Var(variable) => {
                    used.insert(variable.name.clone());
                    &[]
                }
                ChcExpr::FuncApp(name, _, args) | ChcExpr::PredicateApp(name, _, args) => {
                    used.insert(name.clone());
                    args
                }
                ChcExpr::Op(_, args) => args,
                ChcExpr::ConstArray(_, value) => std::slice::from_ref(value),
                ChcExpr::IsTesterMarker(name) => {
                    used.insert(name.clone());
                    &[]
                }
                _ => &[],
            };
            for child in children.iter().rev() {
                names.poll()?;
                pending.push(child.as_ref());
            }
        }
    }
    names.poll()?;
    Some((used, squares))
}

#[cfg(test)]
mod tests;
