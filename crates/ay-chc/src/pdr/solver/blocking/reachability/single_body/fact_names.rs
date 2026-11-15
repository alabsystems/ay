// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact, source-stable alpha-renaming for PDR fact joins.

use crate::{ChcExpr, ChcProblem, ChcVar, ClauseHead};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};

#[cfg(test)]
#[path = "fact_names/tests.rs"]
mod tests;

pub(super) struct SourceNames {
    used: FxHashSet<String>,
}

impl SourceNames {
    pub(super) fn collect(problem: &ChcProblem, open: &mut impl FnMut() -> bool) -> Option<Self> {
        let mut used = FxHashSet::default();
        for predicate in problem.predicates() {
            if !open() {
                return None;
            }
            used.insert(predicate.name.clone());
        }
        for (name, constructors) in problem.datatype_defs() {
            if !open() {
                return None;
            }
            used.insert(name.clone());
            for (constructor, selectors) in constructors {
                if !open() {
                    return None;
                }
                used.insert(constructor.clone());
                for (selector, _) in selectors {
                    if !open() {
                        return None;
                    }
                    used.insert(selector.clone());
                }
            }
        }
        let mut roots = Vec::new();
        for clause in problem.source_clauses() {
            if !open() {
                return None;
            }
            roots.extend(clause.body.constraint.iter());
            for (_, args) in &clause.body.predicates {
                for arg in args {
                    if !open() {
                        return None;
                    }
                    roots.push(arg);
                }
            }
            if let ClauseHead::Predicate(_, args) = &clause.head {
                for arg in args {
                    if !open() {
                        return None;
                    }
                    roots.push(arg);
                }
            }
        }
        walk(roots, open, |expr| {
            if let Some(name) = symbol(expr) {
                used.insert(name.to_owned());
            }
            Some(())
        })?;
        Some(Self { used })
    }

    pub(super) fn rename<'a>(
        &self,
        constraint: &ChcExpr,
        args: &[ChcExpr],
        prefix: &str,
        query_roots: impl IntoIterator<Item = &'a ChcExpr>,
        open: &mut impl FnMut() -> bool,
    ) -> Option<(ChcExpr, Vec<ChcExpr>)> {
        let mut variables: FxHashMap<String, ChcVar> = FxHashMap::default();
        walk(std::iter::once(constraint).chain(args), open, |expr| {
            if let ChcExpr::Var(var) = expr {
                if let Some(prior) = variables.get(&var.name) {
                    if prior != var {
                        return None;
                    }
                } else {
                    variables.insert(var.name.clone(), var.clone());
                }
            }
            Some(())
        })?;
        let mut variables: Vec<_> = variables.into_values().collect();
        variables.sort_unstable_by(|a, b| a.name.cmp(&b.name));
        let mut fresh: FxHashMap<String, ChcVar> = FxHashMap::default();
        let mut substitution = Vec::new();
        for var in variables {
            if !open() {
                return None;
            }
            let base = format!("{prefix}{}", var.name);
            let attempts = self.used.len().checked_add(fresh.len())?.checked_add(1)?;
            let mut name = None;
            for suffix in 0..=attempts {
                if !open() {
                    return None;
                }
                let candidate = if suffix == 0 {
                    base.clone()
                } else {
                    format!("{base}_{suffix}")
                };
                if !self.used.contains(&candidate) && !fresh.contains_key(&candidate) {
                    name = Some(candidate);
                    break;
                }
            }
            let name = name?;
            let renamed = ChcVar::new(name.clone(), var.sort.clone());
            fresh.insert(name, renamed.clone());
            substitution.push((var, ChcExpr::var(renamed)));
        }
        // Never vary a cached background's renaming with the current POB.
        // Names introduced after source admission instead make this join refuse.
        walk(query_roots, open, |expr| {
            if symbol(expr).is_some_and(|name| fresh.contains_key(name)) {
                return None;
            }
            Some(())
        })?;
        if !open() {
            return None;
        }
        let renamed_constraint = constraint.substitute(&substitution);
        let mut renamed_args = Vec::with_capacity(args.len());
        for arg in args {
            if !open() {
                return None;
            }
            renamed_args.push(arg.substitute(&substitution));
        }
        // The existing substitution is best-effort at its depth/node limits.
        // An exact iterative census rejects ANY leftover (or wrong-sort) local;
        // ordinary `vars()` is depth-limited and cannot certify completeness.
        walk(
            std::iter::once(&renamed_constraint).chain(&renamed_args),
            open,
            |expr| {
                if let ChcExpr::Var(var) = expr {
                    if fresh.get(&var.name) != Some(var) {
                        return None;
                    }
                }
                Some(())
            },
        )?;
        Some((renamed_constraint, renamed_args))
    }
}

/// Whether every variable of `expr` is one of `vars`, name AND sort, by the
/// same exact census `rename` certifies with (`ChcExpr::vars` is
/// depth-limited). A cancelled census answers `false`, so a caller that
/// admits only closed formulas fails closed.
pub(super) fn mentions_only(
    expr: &ChcExpr,
    vars: &[ChcVar],
    open: &mut impl FnMut() -> bool,
) -> bool {
    walk(std::iter::once(expr), open, |node| match node {
        ChcExpr::Var(var) if !vars.contains(var) => None,
        _ => Some(()),
    })
    .is_some()
}

fn symbol(expr: &ChcExpr) -> Option<&str> {
    match expr {
        ChcExpr::Var(var) => Some(&var.name),
        ChcExpr::FuncApp(name, _, _)
        | ChcExpr::PredicateApp(name, _, _)
        | ChcExpr::IsTesterMarker(name) => Some(name),
        _ => None,
    }
}

/// Borrowed roots keep every pointer key alive for the complete census.
/// Poll per node/edge; no recursive tree walk or depth-truncated inventory.
fn walk<'a>(
    roots: impl IntoIterator<Item = &'a ChcExpr>,
    open: &mut impl FnMut() -> bool,
    mut inspect: impl FnMut(&ChcExpr) -> Option<()>,
) -> Option<()> {
    let mut pending = Vec::new();
    for root in roots {
        if !open() {
            return None;
        }
        pending.push(root);
    }
    let mut seen = FxHashSet::default();
    while let Some(expr) = pending.pop() {
        if !open() {
            return None;
        }
        if !seen.insert(expr as *const ChcExpr) {
            continue;
        }
        inspect(expr)?;
        match expr {
            ChcExpr::Op(_, args)
            | ChcExpr::PredicateApp(_, _, args)
            | ChcExpr::FuncApp(_, _, args) => {
                for arg in args {
                    if !open() {
                        return None;
                    }
                    pending.push(arg.as_ref());
                }
            }
            ChcExpr::ConstArray(_, value) => pending.push(value.as_ref()),
            _ => {}
        }
    }
    open().then_some(())
}
