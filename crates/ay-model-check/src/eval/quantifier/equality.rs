// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact finite support for binders over an INFINITE sort that the body only
//! ever compares for equality (#eq-only-quantifier-eval).
//!
//! # The fragment
//!
//! Let `Q = (∀|∃) x⃗. φ` be evaluated in an environment `ρ`, and let `I` be
//! every name bound by `Q` itself or by a quantifier nested in `φ`. The
//! planner applies only when
//!
//! * every binder in `I` has ONE sort `S ∈ {Int, Real}` (both infinite);
//! * every occurrence of a variable named in `I` is BOUND where it occurs —
//!   by `Q` itself or by a quantifier of `φ` enclosing the occurrence — and
//!   is a DIRECT argument of a binary `=` / `distinct` over `S` whose other
//!   argument is either such a bound variable or a term mentioning no name
//!   in `I` at all;
//! * `φ` contains no `let` and no binder of any other sort.
//!
//! Occurrences are resolved by SCOPE, not by name. A name in `I` that also
//! occurs where no binder of `Q` encloses it — a nested binder shadowing a
//! free constant or a variable of `ρ`, as in `∀x. (x = y) = (∀y. y ≠ x)` with
//! `y` free — makes the planner decline: that occurrence denotes a value of
//! `ρ`, which the argument below neither permutes nor puts in `V`. The whole
//! argument ASSUMES every `I`-named occurrence it admits refers to a binder
//! of `Q` (or of a quantifier nested in it); the scope-aware audit is what
//! establishes that.
//!
//! Let `V` be the values, under `ρ`, of the `I`-free arguments of those
//! atoms (the terms a bound `I`-variable is ever compared with).
//!
//! # Why a finite candidate set is exact
//!
//! Any permutation `π` of the carrier of `S` that fixes `V` pointwise
//! preserves the truth of `φ` when applied to the values of all `I`-variables
//! at once: every atom mentioning an `I`-variable is an equality between two
//! `I`-values (`π` is a bijection) or between an `I`-value and a value in `V`
//! (fixed by `π`), and every other atom mentions no `I`-variable at all. A
//! nested quantifier ranges over the whole carrier, which `π` maps onto
//! itself. So for any tuple `a⃗` the values outside `V` can be renamed, in
//! order of first occurrence, to fresh values `c₁, c₂, …` that lie outside
//! `V` without changing `φ`'s truth value. Hence `Q`'s truth value is decided
//! by the tuples whose `i`-th value is in `V` or is one of the fresh values
//! `c₁ … c_{k+1}`, `k` being the number of fresh values the tuple's prefix
//! already uses (a restricted-growth enumeration). The carrier is infinite,
//! so the fresh values exist; they are chosen as the successive integers
//! above every value in `V`.
//!
//! Nested quantifiers are evaluated by the ordinary recursive evaluator,
//! which re-plans each one in its own (now larger) environment.
//!
//! The planner never consults the solver: it reads the body syntactically
//! and evaluates the `I`-free comparison terms through this same evaluator.

use super::*;
use ay_core::term::TermData;
use ay_core::TermStore;
use num_rational::BigRational;
use num_traits::Zero;
use std::collections::{HashMap, HashSet};

/// Most distinct comparison values the planner enumerates against.
const MAX_EQUALITY_SUPPORT_VALUES: usize = 64;

/// Plan the exact candidate tuples for an equality-only binder group, or
/// `Ok(None)` when the body is outside the fragment (the caller then keeps
/// its own rejection). Resource exhaustion is reported as an error so it is
/// never mistaken for "not applicable".
pub(super) fn plan(
    evaluator: &Evaluator<'_>,
    bindings: &[(String, Sort)],
    body: TermId,
    depth: usize,
) -> Result<Option<Vec<Vec<ModelValue>>>, QuantifierRejection> {
    let Some((_, sort)) = bindings.first() else {
        return Ok(None);
    };
    let sort = sort.clone();
    if !matches!(sort, Sort::Int | Sort::Real) || bindings.len() > MAX_QUANTIFIER_BINDERS {
        return Ok(None);
    }
    let mut internal: HashSet<&str> = HashSet::new();
    for (index, (name, binder_sort)) in bindings.iter().enumerate() {
        if *binder_sort != sort {
            return Ok(None);
        }
        if bindings[..index].iter().any(|(prior, _)| prior == name) {
            return Err(QuantifierRejection::DuplicateBinder);
        }
        internal.insert(name.as_str());
    }
    if !collect_nested_binders(evaluator, body, &sort, &mut internal)? {
        return Ok(None);
    }
    let Some(comparands) = comparison_terms(evaluator, body, bindings, &sort, &internal)? else {
        return Ok(None);
    };
    // Evaluate every comparand in the CURRENT environment. None of them
    // mentions a name this group (or a nested group) binds.
    let mut support: Vec<ModelValue> = Vec::new();
    let mut support_keys: Vec<BigRational> = Vec::new();
    let mut ceiling = BigInt::zero();
    for term in comparands {
        charge(evaluator, 1)?;
        let value = match evaluator.eval(term, depth + 1) {
            Ok(value) => value,
            Err(error) => return Err(QuantifierRejection::UnevaluableBody(error)),
        };
        let key = match (&sort, &value) {
            (Sort::Int, ModelValue::Int(value)) => BigRational::from_integer(value.clone()),
            (Sort::Real, ModelValue::Real(value)) => value.clone(),
            _ => return Err(QuantifierRejection::BindingSortMismatch),
        };
        let floor = key.floor().to_integer();
        if floor > ceiling {
            ceiling = floor;
        }
        if !support_keys.contains(&key) {
            if support.len() == MAX_EQUALITY_SUPPORT_VALUES {
                return Err(QuantifierRejection::AssignmentBudget);
            }
            support_keys.push(key);
            support.push(value);
        }
    }
    // Fresh values: successive integers strictly above every support value.
    let fresh: Vec<ModelValue> = (1..=bindings.len())
        .map(|offset| {
            let value = &ceiling + BigInt::from(offset);
            match sort {
                Sort::Int => ModelValue::Int(value),
                _ => ModelValue::Real(BigRational::from_integer(value)),
            }
        })
        .collect();
    let mut tuples = Vec::new();
    let mut prefix = Vec::with_capacity(bindings.len());
    enumerate(
        evaluator,
        bindings.len(),
        &support,
        &fresh,
        0,
        &mut prefix,
        &mut tuples,
    )?;
    Ok(Some(tuples))
}

fn charge(evaluator: &Evaluator<'_>, work: usize) -> Result<(), QuantifierRejection> {
    evaluator
        .charge_quantifier_work(work)
        .map_err(QuantifierRejection::UnevaluableBody)
}

/// Restricted-growth enumeration: position `i` takes a support value, a fresh
/// value already used by the prefix, or the next unused fresh value.
fn enumerate(
    evaluator: &Evaluator<'_>,
    width: usize,
    support: &[ModelValue],
    fresh: &[ModelValue],
    fresh_used: usize,
    prefix: &mut Vec<ModelValue>,
    tuples: &mut Vec<Vec<ModelValue>>,
) -> Result<(), QuantifierRejection> {
    charge(evaluator, 1)?;
    if prefix.len() == width {
        let state = &evaluator.quantifier_state;
        if tuples.len() >= state.assignments_left.get() {
            return Err(QuantifierRejection::AssignmentBudget);
        }
        tuples
            .try_reserve(1)
            .map_err(|_| QuantifierRejection::EvaluationBudget)?;
        tuples.push(prefix.clone());
        return Ok(());
    }
    for value in support {
        prefix.push(value.clone());
        enumerate(evaluator, width, support, fresh, fresh_used, prefix, tuples)?;
        prefix.pop();
    }
    let next = (fresh_used + 1).min(fresh.len());
    for (index, value) in fresh.iter().take(next).enumerate() {
        prefix.push(value.clone());
        let used = fresh_used.max(index + 1);
        enumerate(evaluator, width, support, fresh, used, prefix, tuples)?;
        prefix.pop();
    }
    Ok(())
}

/// Add every binder of every quantifier nested in `body` to `internal`.
/// `Ok(false)` when a nested binder has another sort, or the body holds a
/// `let` (whose names this syntactic audit does not resolve).
fn collect_nested_binders<'t>(
    evaluator: &Evaluator<'t>,
    body: TermId,
    sort: &Sort,
    internal: &mut HashSet<&'t str>,
) -> Result<bool, QuantifierRejection> {
    let terms: &'t TermStore = evaluator.terms;
    let mut stack = vec![body];
    let mut seen: HashSet<TermId> = HashSet::new();
    while let Some(term) = stack.pop() {
        charge(evaluator, 1)?;
        if !seen.insert(term) {
            continue;
        }
        match terms.get(term) {
            TermData::Forall(vars, inner, _) | TermData::Exists(vars, inner, _) => {
                for (name, binder_sort) in vars {
                    if binder_sort != sort {
                        return Ok(false);
                    }
                    internal.insert(name.as_str());
                }
                stack.push(*inner);
            }
            TermData::Let(..) => return Ok(false),
            TermData::Var(..) | TermData::Const(_) => {}
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(condition, then_term, else_term) => {
                stack.extend([*condition, *then_term, *else_term]);
            }
            // Any other node kind: refuse rather than guess its binding
            // structure.
            _ => return Ok(false),
        }
    }
    Ok(true)
}

/// Whether `term` is a variable whose name is BOUND at this position: by the
/// group itself or by a quantifier of `body` enclosing the position.
fn is_bound_var(terms: &TermStore, term: TermId, scope: &[&str]) -> bool {
    matches!(terms.get(term), TermData::Var(name, _) if scope.contains(&name.as_str()))
}

/// Intern the scope `base ∪ names` (kept sorted and deduplicated) and return
/// its index.
fn extend_scope<'t>(
    scopes: &mut Vec<Vec<&'t str>>,
    index_of: &mut HashMap<Vec<&'t str>, usize>,
    base: usize,
    names: &'t [(String, Sort)],
) -> usize {
    let mut scope = scopes[base].clone();
    scope.extend(names.iter().map(|(name, _)| name.as_str()));
    scope.sort_unstable();
    scope.dedup();
    if let Some(&index) = index_of.get(&scope) {
        return index;
    }
    let index = scopes.len();
    index_of.insert(scope.clone(), index);
    scopes.push(scope);
    index
}

/// Whether `term` mentions a variable named in `internal` anywhere.
fn mentions_internal(
    evaluator: &Evaluator<'_>,
    term: TermId,
    internal: &HashSet<&str>,
) -> Result<bool, QuantifierRejection> {
    let terms = evaluator.terms;
    let mut stack = vec![term];
    let mut seen: HashSet<TermId> = HashSet::new();
    while let Some(term) = stack.pop() {
        charge(evaluator, 1)?;
        if !seen.insert(term) {
            continue;
        }
        match terms.get(term) {
            TermData::Var(name, _) => {
                if internal.contains(name.as_str()) {
                    return Ok(true);
                }
            }
            TermData::Const(_) => {}
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(condition, then_term, else_term) => {
                stack.extend([*condition, *then_term, *else_term]);
            }
            TermData::Forall(_, inner, _) | TermData::Exists(_, inner, _) => stack.push(*inner),
            // Conservative: an unknown node kind may hide an occurrence.
            _ => return Ok(true),
        }
    }
    Ok(false)
}

/// The occurrence audit. Returns the `I`-free arguments of every `S`-sorted
/// binary equality/disequality that compares a BOUND `I`-variable, or `None`
/// when some `I`-name occurs anywhere else.
///
/// Occurrences are resolved by SCOPE, not by name: a variable counts as a
/// binder occurrence only where its name is bound by the group itself or by
/// a quantifier of `body` enclosing that position. An `I`-name reached where
/// no such binder encloses it (a nested binder that SHADOWS a free constant
/// or an outer variable, e.g. `∀x. (x = y) = (∀y. y ≠ x)` with `y` free)
/// denotes an environment value, and the planner DECLINES rather than
/// resolve it: such a name is neither a binder occurrence (the permutation
/// argument would not cover it) nor a safe comparand (the conservative
/// `mentions_internal` test rejects every `I`-name). Hash-consing shares one
/// `TermId` between positions under different scopes, so the visited set is
/// keyed by `(term, scope)`.
fn comparison_terms(
    evaluator: &Evaluator<'_>,
    body: TermId,
    bindings: &[(String, Sort)],
    sort: &Sort,
    internal: &HashSet<&str>,
) -> Result<Option<Vec<TermId>>, QuantifierRejection> {
    let terms = evaluator.terms;
    let mut comparands: Vec<TermId> = Vec::new();
    let mut scopes: Vec<Vec<&str>> = vec![Vec::new()];
    let mut index_of: HashMap<Vec<&str>, usize> = HashMap::new();
    index_of.insert(Vec::new(), 0);
    let root = extend_scope(&mut scopes, &mut index_of, 0, bindings);
    let mut stack = vec![(body, root)];
    let mut seen: HashSet<(TermId, usize)> = HashSet::new();
    while let Some((term, scope)) = stack.pop() {
        charge(evaluator, 1)?;
        if !seen.insert((term, scope)) {
            continue;
        }
        match terms.get(term) {
            TermData::Var(name, _) => {
                // Reached outside an admitted atom position (bound or not).
                if internal.contains(name.as_str()) {
                    return Ok(None);
                }
            }
            TermData::Const(_) => {}
            TermData::App(symbol, args)
                if matches!(symbol.name(), "=" | "distinct")
                    && args.len() == 2
                    && terms.sort(args[0]) == sort
                    && terms.sort(args[1]) == sort =>
            {
                charge(evaluator, symbol.name().len().div_ceil(64).max(1))?;
                if !matches!(symbol, ay_core::Symbol::Named(_))
                    || terms.is_declared_function(symbol.name())
                {
                    return Ok(None);
                }
                let (lhs, rhs) = (args[0], args[1]);
                let lhs_bound = is_bound_var(terms, lhs, &scopes[scope]);
                let rhs_bound = is_bound_var(terms, rhs, &scopes[scope]);
                if !lhs_bound && !rhs_bound {
                    // No bound I-variable here: an I-name nested inside
                    // either side is a violation, found by descending.
                    stack.push((lhs, scope));
                    stack.push((rhs, scope));
                    continue;
                }
                for (side, side_bound) in [(lhs, lhs_bound), (rhs, rhs_bound)] {
                    if side_bound {
                        continue;
                    }
                    // Also rejects an UNBOUND occurrence of an I-name.
                    if mentions_internal(evaluator, side, internal)? {
                        return Ok(None);
                    }
                    if !comparands.contains(&side) {
                        comparands.push(side);
                    }
                }
            }
            TermData::App(_, args) => stack.extend(args.iter().map(|&arg| (arg, scope))),
            TermData::Not(inner) => stack.push((*inner, scope)),
            TermData::Ite(condition, then_term, else_term) => {
                stack.extend([*condition, *then_term, *else_term].map(|child| (child, scope)));
            }
            TermData::Forall(vars, inner, _) | TermData::Exists(vars, inner, _) => {
                let nested = extend_scope(&mut scopes, &mut index_of, scope, vars);
                stack.push((*inner, nested));
            }
            _ => return Ok(None),
        }
    }
    Ok(Some(comparands))
}

#[cfg(test)]
mod tests;
