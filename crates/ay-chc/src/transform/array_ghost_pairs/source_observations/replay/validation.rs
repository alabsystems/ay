// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::super::layout::scalar;
use super::*;
use std::collections::BTreeSet;

pub(in crate::transform::array_ghost_pairs) fn validate(
    problem: &QuantifiedChcProblem,
    model: &ObservationModel,
    control: &SourceControl<'_>,
) -> Option<()> {
    if !model.layout.matches_source(problem, control)
        || model.model.len() != problem.source_problem().predicates().len()
        || model.model.has_quantified_array_certificate()
    {
        return None;
    }
    for predicate in problem.source_problem().predicates() {
        control.poll()?;
        let original = model.layout.original_sorts(predicate.id)?;
        for sort in original.iter().chain(&predicate.arg_sorts) {
            control.bytes(sort_bytes(sort)?)?;
        }
        if original != predicate.arg_sorts.as_slice() {
            return None;
        }
        let canonical = model.layout.canonical(predicate.id)?;
        control.charge(canonical.len())?;
        for var in canonical {
            control.bytes(var.name.len().checked_add(sort_bytes(&var.sort)?)?)?;
        }
        let expected = model.layout.extended_sorts(predicate.id, control)?;
        let interpretation = model.model.get(&predicate.id)?;
        if expected.len() != canonical.len() || canonical.len() != interpretation.vars.len() {
            return None;
        }
        let mut names = BTreeSet::new();
        for ((var, wanted), sort) in interpretation.vars.iter().zip(canonical).zip(&expected) {
            control.bytes(var.name.len().checked_add(sort_bytes(&var.sort)?)?)?;
            if var != wanted || &var.sort != sort || !names.insert(var.name.as_str()) {
                return None;
            }
        }
        if !model
            .layout
            .axes(predicate.id)?
            .iter()
            .all(|s| matches!(s, ChcSort::BitVec(1..=crate::MAX_BITVECTOR_WIDTH)))
        {
            return None;
        }
        source_premises::preflight(&interpretation.formula, control, &mut 0)?;
        if scalar_sort(&interpretation.formula, canonical, control, 0)? != ChcSort::Bool {
            return None;
        }
    }
    control.poll()
}

// Candidate syntax is deliberately narrower than original-source syntax.
// Aggregate formal parameters are retained, but cannot occur in this formula.
fn scalar_sort(
    expr: &ChcExpr,
    vars: &[ChcVar],
    control: &SourceControl<'_>,
    depth: usize,
) -> Option<ChcSort> {
    control.charge(1)?;
    if depth > 128 {
        return None;
    }
    let sort = match expr {
        ChcExpr::Bool(_) => ChcSort::Bool,
        ChcExpr::BitVec(value, width)
            if (1..=crate::MAX_BITVECTOR_WIDTH).contains(width)
                && (*width >= 128 || *value < (1_u128 << width)) =>
        {
            ChcSort::BitVec(*width)
        }
        ChcExpr::Var(var) => {
            control.charge(vars.len())?;
            if !scalar(&var.sort) || !vars.contains(var) {
                return None;
            }
            control.bytes(sort_bytes(&var.sort)?)?;
            var.sort.clone()
        }
        ChcExpr::Op(op, args) => {
            control.charge(args.len())?;
            control.bytes(args.len().checked_mul(std::mem::size_of::<ChcSort>())?)?;
            let mut sorts = Vec::new();
            sorts.try_reserve_exact(args.len()).ok()?;
            for arg in args {
                sorts.push(scalar_sort(arg, vars, control, depth + 1)?);
            }
            crate::pdr::validate_qf_operation(*op, &sorts).ok()?
        }
        _ => return None,
    };
    if !scalar(&sort) {
        return None;
    }
    control.bytes(sort_bytes(&sort)?)?;
    Some(sort)
}
