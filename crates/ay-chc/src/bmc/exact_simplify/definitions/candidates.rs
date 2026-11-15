// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

pub(super) fn collect(
    conjuncts: &[ChcExpr],
    names: &mut AcyclicNames<'_>,
) -> Option<DetHashMap<String, ChcExpr>> {
    names.check_all(conjuncts)?;
    let mut candidates: DetHashMap<String, Option<ChcExpr>> = DetHashMap::default();
    for conjunct in conjuncts {
        names.poll()?;
        let simplified = super::super::simplify_expression(conjunct.clone(), names)?;
        let ChcExpr::Op(ChcOp::Eq, args) = &simplified else {
            continue;
        };
        if args.len() != 2 {
            continue;
        }
        let Some((name, expression)) =
            BmcSolver::orient_definitional_equality(args[0].as_ref(), args[1].as_ref())
        else {
            continue;
        };
        names.poll()?;
        if BmcSolver::expr_mentions_var(&expression, &name) || expression.node_count(4096) >= 4096 {
            continue;
        }
        names.poll()?;
        match candidates.get_mut(&name) {
            Some(slot) if slot.as_ref() == Some(&expression) => {}
            Some(slot) => *slot = None,
            None => {
                candidates.insert(name, Some(expression));
            }
        }
    }

    // Keep the legacy insertion/key/removal order: cyclic candidate pruning
    // consults the map after each previous key's removal.
    let mut substitutions = DetHashMap::default();
    for (name, expression) in candidates {
        names.poll()?;
        if let Some(expression) = expression {
            substitutions.insert(name, expression);
        }
    }
    let mut keys = Vec::new();
    if keys.try_reserve_exact(substitutions.len()).is_err() {
        return names.refuse();
    }
    for name in substitutions.keys() {
        names.poll()?;
        keys.push(name.clone());
    }
    for name in keys {
        names.poll()?;
        if let Some(expression) = substitutions.get(&name) {
            if depends_on(&name, expression, &substitutions, names)? {
                substitutions.remove(&name);
            }
        }
    }
    names.poll()?;
    Some(substitutions)
}

/// Reachability is independent of DFS revisitation order. A global expanded
/// name set explores each candidate RHS once, including cycles, and asks the
/// same target-reachability question as the old recursive path-local set.
fn depends_on(
    target: &str,
    expression: &ChcExpr,
    substitutions: &DetHashMap<String, ChcExpr>,
    names: &mut AcyclicNames<'_>,
) -> Option<bool> {
    names.poll()?;
    let mut expanded = DetHashSet::default();
    let mut pending = Vec::new();
    if pending.try_reserve_exact(1).is_err() {
        return names.refuse();
    }
    pending.push(expression);
    while let Some(expression) = pending.pop() {
        names.poll()?;
        if let ChcExpr::Var(variable) = expression {
            if variable.name == target {
                return Some(true);
            }
            if let Some(replacement) = substitutions.get(&variable.name) {
                if expanded.insert(variable.name.as_str()) {
                    names.poll()?;
                    pending.push(replacement);
                }
            }
        }
        let children: &[std::sync::Arc<ChcExpr>] = match expression {
            ChcExpr::Op(_, args)
            | ChcExpr::PredicateApp(_, _, args)
            | ChcExpr::FuncApp(_, _, args) => args,
            ChcExpr::ConstArray(_, value) => std::slice::from_ref(value),
            _ => &[],
        };
        if pending.try_reserve(children.len()).is_err() {
            return names.refuse();
        }
        for child in children.iter().rev() {
            names.poll()?;
            pending.push(child.as_ref());
        }
    }
    names.poll()?;
    Some(false)
}
