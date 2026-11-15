// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::collections::BTreeSet;

pub(super) fn reserved<'a>(
    problem: &'a QuantifiedChcProblem,
    registry: &'a Registry,
    control: &SourceControl<'_>,
) -> Option<BTreeSet<&'a str>> {
    let mut names = BTreeSet::new();
    // Global functions remain global even when unused in every source clause.
    for name in controlled::names(problem, control)? {
        control.poll()?;
        names.insert(name);
    }
    for name in registry.term_names() {
        control.charge(1)?;
        names.insert(name);
    }
    for name in problem.source_problem().datatype_defs().keys() {
        control.charge(1)?;
        names.insert(name.as_str());
    }
    for predicate in problem.source_problem().predicates() {
        control.charge(1)?;
        names.insert(predicate.name.as_str());
    }
    for (clause, premises) in problem
        .source_problem()
        .clauses()
        .iter()
        .zip(problem.premises())
    {
        for (_, args) in &clause.body.predicates {
            for arg in args {
                expression_names(arg, &mut names, control)?;
            }
        }
        if let Some(expr) = &clause.body.constraint {
            expression_names(expr, &mut names, control)?;
        }
        if let ClauseHead::Predicate(_, args) = &clause.head {
            for arg in args {
                expression_names(arg, &mut names, control)?;
            }
        }
        for premise in premises {
            for binder in premise.binders() {
                control.charge(1)?;
                names.insert(binder.name.as_str());
            }
            expression_names(premise.matrix(), &mut names, control)?;
        }
    }
    control.poll()?;
    Some(names)
}

fn expression_names<'a>(
    expr: &'a ChcExpr,
    names: &mut BTreeSet<&'a str>,
    control: &SourceControl<'_>,
) -> Option<()> {
    control.charge(1)?;
    let mut pending = vec![(expr, 0usize)];
    while let Some((expr, depth)) = pending.pop() {
        control.charge(1)?;
        if depth > 64 {
            return None;
        }
        match expr {
            ChcExpr::Var(var) => {
                names.insert(&var.name);
            }
            ChcExpr::FuncApp(name, _, args) => {
                names.insert(name);
                control.charge(args.len())?;
                pending.try_reserve(args.len()).ok()?;
                pending.extend(args.iter().map(|arg| (arg.as_ref(), depth + 1)));
            }
            ChcExpr::Op(_, args) => {
                control.charge(args.len())?;
                pending.try_reserve(args.len()).ok()?;
                pending.extend(args.iter().map(|arg| (arg.as_ref(), depth + 1)));
            }
            ChcExpr::ConstArray(_, value) => {
                control.charge(1)?;
                pending.try_reserve(1).ok()?;
                pending.push((value, depth + 1));
            }
            ChcExpr::Bool(_) | ChcExpr::BitVec(_, _) => {}
            _ => return None,
        }
    }
    control.poll()
}
