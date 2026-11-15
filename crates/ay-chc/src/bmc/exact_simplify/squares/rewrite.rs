// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

pub(super) fn replace(
    expression: &ChcExpr,
    replacements: &FxHashMap<ChcExpr, ChcExpr>,
    names: &mut AcyclicNames<'_>,
) -> Option<ChcExpr> {
    names.check(expression)?;
    let mut memo = FxHashMap::default();
    let rewritten = node(expression, replacements, names, &mut memo)?;
    drop(memo);
    let rewritten = Arc::unwrap_or_clone(rewritten);
    names.check(&rewritten)?;
    Some(rewritten)
}

fn node(
    expression: &ChcExpr,
    replacements: &FxHashMap<ChcExpr, ChcExpr>,
    names: &mut AcyclicNames<'_>,
    memo: &mut FxHashMap<*const ChcExpr, Arc<ChcExpr>>,
) -> Option<Arc<ChcExpr>> {
    // Recursion is bounded by the complete input preflight. Only replacement
    // by a scalar variable is possible, so this walk cannot increase depth.
    names.poll()?;
    let key = std::ptr::from_ref(expression);
    if let Some(cached) = memo.get(&key) {
        return Some(Arc::clone(cached));
    }
    // Keys are exactly x*x terms. Do not deep-hash every other subtree merely
    // to learn that it cannot be one of these fixed-shape keys.
    if BmcSolver::square_input_var(expression).is_some() {
        if let Some(replacement) = replacements.get(expression) {
            let result = Arc::new(replacement.clone());
            memo.insert(key, Arc::clone(&result));
            return Some(result);
        }
    }
    let children: &[Arc<ChcExpr>] = match expression {
        ChcExpr::Op(_, args) | ChcExpr::PredicateApp(_, _, args) | ChcExpr::FuncApp(_, _, args) => {
            args
        }
        ChcExpr::ConstArray(_, value) => std::slice::from_ref(value),
        _ => &[],
    };
    let mut rewritten = Vec::new();
    if rewritten.try_reserve_exact(children.len()).is_err() {
        return names.refuse();
    }
    for child in children {
        rewritten.push(node(child, replacements, names, memo)?);
    }
    let result = match expression {
        ChcExpr::Op(op, _) => ChcExpr::Op(*op, rewritten),
        ChcExpr::PredicateApp(name, predicate, _) => {
            ChcExpr::PredicateApp(name.clone(), *predicate, rewritten)
        }
        ChcExpr::FuncApp(name, sort, _) => ChcExpr::FuncApp(name.clone(), sort.clone(), rewritten),
        ChcExpr::ConstArray(sort, _) => {
            let Some(value) = rewritten.pop() else {
                return names.refuse();
            };
            ChcExpr::ConstArray(sort.clone(), value)
        }
        _ => expression.clone(),
    };
    let result = Arc::new(result);
    memo.insert(key, Arc::clone(&result));
    Some(result)
}
