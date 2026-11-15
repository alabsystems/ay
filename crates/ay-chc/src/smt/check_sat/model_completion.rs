// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model-completion walks of `sat_or_unknown`: the variables a model misses,
//! and values derived for them from SSA defining equalities (`q = RHS`).

use super::super::types::SmtValue;
use crate::ChcExpr;
use ay_core::kani_compat::DetHashMap as FxHashMap;
use ay_core::kani_compat::DetHashSet as FxHashSet;

/// All SCALAR variables of `exprs` that occur in a position the STRICT model
/// verifier can evaluate but have NO representation in `model` — neither a direct
/// assignment nor a BvToBool bit-decomposition. Deduplicated by name, in
/// first-encounter order, with their sorts (empty if none are missing).
///
/// This is the signature of an upstream abstraction DROPPING the variable\'s
/// defining conjunct (the fail-open repro class). Three deliberate exemptions
/// keep every known-legitimate Indeterminate acceptance intact:
///
/// - Variables occurring ONLY inside uninterpreted `PredicateApp`/`FuncApp`
///   argument lists: the strict evaluator skips those atoms entirely, so such a
///   variable cannot affect verification (#4712).
/// - Array / datatype / uninterpreted-sorted variables: the theory solver owns
///   them and the strict evaluator generally cannot evaluate their atoms anyway
///   (the conditional array/DT demotion in `assumptions.rs` #6047/#7016 is the
///   existing, separate guard for that class).
/// - Scalars whose BvToBool bit-decomposition IS in the model (`{name}_b0`, the
///   `transform/bv_to_bool` naming): the model constrains them fully — just in
///   transformed vocabulary (e.g. the #6781 preprocessed lane) — which is not
///   the dropped-conjunct signature.
///
/// Iterative walk — no recursion-depth hazard on deep expressions.
pub(super) fn evaluable_free_vars_missing_from_model<'a>(
    exprs: impl IntoIterator<Item = &'a ChcExpr>,
    model: &FxHashMap<String, SmtValue>,
) -> Vec<(String, crate::ChcSort)> {
    let mut missing: Vec<(String, crate::ChcSort)> = Vec::new();
    let mut seen: FxHashSet<String> = FxHashSet::default();
    // A shared sub-term is walked once: the depth-first walk visits its
    // subtree right after its first visit, so a repeat adds no variable and
    // changes no first-encounter order (the tree walk was exponential in the
    // nesting of shared sub-terms). Addresses stay valid: `exprs` are
    // borrowed for the whole walk.
    let mut walked: FxHashSet<*const ChcExpr> = FxHashSet::default();
    let mut stack: Vec<&ChcExpr> = exprs.into_iter().collect();
    // Preserve first-encounter order across the conjunct list.
    stack.reverse();
    while let Some(e) = stack.pop() {
        if !walked.insert(std::ptr::from_ref(e)) {
            continue;
        }
        match e {
            ChcExpr::ArrayLambda(lambda) => {
                stack.extend(lambda.captures().iter().map(AsRef::as_ref))
            }
            ChcExpr::Var(v) => {
                let scalar = matches!(
                    v.sort,
                    crate::ChcSort::Bool
                        | crate::ChcSort::Int
                        | crate::ChcSort::Real
                        | crate::ChcSort::BitVec(_)
                );
                if scalar
                    && crate::expr::lookup_model_value(model, v).is_none()
                    && !model.contains_key(&format!("{}_b0", v.name))
                    && seen.insert(v.name.clone())
                {
                    missing.push((v.name.clone(), v.sort.clone()));
                }
            }
            ChcExpr::Op(_, args) => stack.extend(args.iter().map(|a| a.as_ref())),
            ChcExpr::ConstArray(_, inner) => stack.push(inner.as_ref()),
            ChcExpr::PredicateApp(..)
            | ChcExpr::FuncApp(..)
            | ChcExpr::Bool(_)
            | ChcExpr::Int(_)
            | ChcExpr::Real(_, _)
            | ChcExpr::BitVec(_, _)
            | ChcExpr::ConstArrayMarker(_)
            | ChcExpr::IsTesterMarker(_) => {}
        }
    }
    missing
}

/// If `lhs` is a scalar variable and `rhs` is a DIFFERENT expression, return the
/// `(var_name, defining_rhs)` pair describing an SSA binding candidate the
/// variable can be pinned to. A self-identity (`q = q`) pins nothing, and only
/// scalar sorts are eligible (matching `evaluable_free_var_missing_from_model`).
fn binding_candidate<'a>(lhs: &'a ChcExpr, rhs: &'a ChcExpr) -> Option<(String, &'a ChcExpr)> {
    let ChcExpr::Var(v) = lhs else {
        return None;
    };
    let scalar = matches!(
        v.sort,
        crate::ChcSort::Bool
            | crate::ChcSort::Int
            | crate::ChcSort::Real
            | crate::ChcSort::BitVec(_)
    );
    if !scalar {
        return None;
    }
    if matches!(rhs, ChcExpr::Var(rv) if rv.name == v.name) {
        return None;
    }
    Some((v.name.clone(), rhs))
}

/// Complete `model` in place by DERIVING values for scalar variables that occur
/// in an evaluable position of `expr` but are absent from the model, using their
/// SSA defining equalities (`q = RHS`) already present in `expr` (the head-arg
/// binding `q = bvudiv(d, 2)` class the linear model leaves implicit).
///
/// A variable is filled ONLY when some `=` atom binds it to a right-hand side
/// that is itself fully evaluable under the CURRENT model — the unique value the
/// constraint forces. This NEVER default-assigns and NEVER invents a value: an
/// unbound or not-yet-evaluable variable is left missing so the caller's
/// fail-closed net still fires. Only `=` atoms are used; a disequality/negation
/// never assigns. Existing assignments are never overwritten.
///
/// Iterates to a fixpoint so a chain of bindings (`q1 = f(q2)`, `q2 = g(d)`)
/// resolves in dependency order. Returns `true` iff at least one assignment was
/// added.
///
/// SOUNDNESS: completion only ADDS bindings the constraint forces; every caller
/// re-runs STRICT verification over the whole expression and accepts ONLY on a
/// `Valid` verdict, so a derived value inconsistent with any other conjunct
/// yields Invalid/Indeterminate — never a spurious Sat.
pub(in crate::smt) fn complete_model_from_bindings(
    expr: &ChcExpr,
    model: &mut FxHashMap<String, SmtValue>,
) -> bool {
    // Gather candidate (var, defining-rhs) pairs from every `=` atom. A shared
    // sub-term is walked once: its first visit already walked its subtree, so
    // a repeat could only append duplicate candidates (the tree walk was
    // exponential in time and memory in the nesting of shared sub-terms: past
    // 8 GB on one bist_cell self-inductiveness model). Addresses stay valid:
    // `expr` is borrowed for the whole walk.
    let mut bindings: Vec<(String, &ChcExpr)> = Vec::new();
    let mut walked: FxHashSet<*const ChcExpr> = FxHashSet::default();
    let mut stack = vec![expr];
    while let Some(e) = stack.pop() {
        if !walked.insert(std::ptr::from_ref(e)) {
            continue;
        }
        match e {
            ChcExpr::Op(crate::ChcOp::Eq, args) if args.len() == 2 => {
                let (l, r) = (args[0].as_ref(), args[1].as_ref());
                if let Some(b) = binding_candidate(l, r) {
                    bindings.push(b);
                }
                if let Some(b) = binding_candidate(r, l) {
                    bindings.push(b);
                }
                stack.push(l);
                stack.push(r);
            }
            ChcExpr::Op(_, args) => stack.extend(args.iter().map(|a| a.as_ref())),
            ChcExpr::ConstArray(_, inner) => stack.push(inner.as_ref()),
            _ => {}
        }
    }
    if bindings.is_empty() {
        return false;
    }
    let mut changed = false;
    // Fixpoint: each pass may make another RHS evaluable via a value derived in
    // an earlier pass. Terminates because every pass either inserts >= 1 new key
    // (guarded below) or makes no progress and breaks.
    loop {
        let mut progressed = false;
        for (name, rhs) in &bindings {
            if model.contains_key(name) {
                continue;
            }
            if let Some(value) = crate::expr::evaluate_expr(rhs, model) {
                model.insert(name.clone(), value);
                progressed = true;
                changed = true;
            }
        }
        if !progressed {
            break;
        }
    }
    changed
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ChcOp, ChcSort, ChcVar};
    use std::sync::Arc;

    fn int(name: &str) -> ChcExpr {
        ChcExpr::var(ChcVar::new(name, ChcSort::Int))
    }

    /// `c(0) = base`, `c(i+1) = c(i) and (c(i) or d <= i)`: `base` occurs
    /// `2^depth` times in the tree and once in the DAG.
    fn shared_chain(depth: i64, base: ChcExpr) -> ChcExpr {
        let mut c = Arc::new(base);
        for i in 0..depth {
            let p = Arc::new(ChcExpr::le(int("d"), ChcExpr::int(i)));
            let or = Arc::new(ChcExpr::Op(ChcOp::Or, vec![Arc::clone(&c), p]));
            c = Arc::new(ChcExpr::Op(ChcOp::And, vec![Arc::clone(&c), or]));
        }
        Arc::unwrap_or_clone(c)
    }

    #[test]
    #[ntest::timeout(60_000)]
    fn a_shared_binding_is_collected_once_and_still_completes_the_model() {
        let binding = ChcExpr::eq(int("q"), ChcExpr::add(int("d"), ChcExpr::int(1)));
        let expr = shared_chain(64, binding);
        let mut model = FxHashMap::default();
        model.insert("d".to_string(), SmtValue::Int(4));

        assert!(complete_model_from_bindings(&expr, &mut model));
        assert_eq!(model.get("q"), Some(&SmtValue::Int(5)));
    }

    /// The missing-variable scan walks each shared sub-term once and keeps
    /// the tree walk's first-encounter order (last argument first).
    #[test]
    #[ntest::timeout(60_000)]
    fn missing_variables_below_a_shared_dag_are_found_once_in_order() {
        let base = ChcExpr::and(
            ChcExpr::eq(int("q"), int("r")),
            ChcExpr::le(int("s"), int("d")),
        );
        let expr = shared_chain(64, base);
        let mut model = FxHashMap::default();
        model.insert("d".to_string(), SmtValue::Int(4));

        let missing = evaluable_free_vars_missing_from_model([&expr], &model);
        let names: Vec<&str> = missing.iter().map(|(name, _)| name.as_str()).collect();
        assert_eq!(names, ["s", "r", "q"]);
    }
}
