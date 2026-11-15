// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact quantifier elimination for EQUALITY-ONLY binders over an infinite
//! sort (#eq-qe-lane).
//!
//! # Fragment
//!
//! A binder `x` of sort `S ∈ {Int, Real}` is eliminable from a
//! quantifier-free body `φ` when every occurrence of `x` in `φ` is a direct
//! argument of a binary `=` or `distinct` over `S` whose other argument is
//! `x` itself or a term `t` NOT mentioning `x` (`t` may be anything else: a
//! constant, an outer binder, an arithmetic term over other symbols).
//! Nested quantifiers are eliminated innermost first, so an outer binder is
//! checked against the already quantifier-free result.
//!
//! # The elimination (exact over an infinite carrier)
//!
//! Let `T` be the distinct comparison terms of `x` in `φ`, and let `φ[⊥]` be
//! `φ` with every atom `x = t` (`t ≠ x`) replaced by `false`, `x = x` by
//! `true`, and `distinct` dually. Then, in EVERY interpretation of the other
//! symbols,
//!
//! ```text
//! ∃x. φ  ≡  ⋁_{t ∈ T} φ[x := t]  ∨  φ[⊥]
//! ∀x. φ  ≡  ⋀_{t ∈ T} φ[x := t]  ∧  φ[⊥]
//! ```
//!
//! `φ` depends on the value `v` of `x` only through which atoms `x = t` hold.
//! If `v` equals the value of some `t ∈ T`, every atom `x = t'` has the truth
//! value of `t = t'`, so `φ(v) ⇔ φ[x := t]`. Otherwise every such atom is
//! false, so `φ(v) ⇔ φ[⊥]`; conversely, `φ[⊥]` true gives a witness because
//! the carrier is infinite and `T` finite (some value avoids every `t`). The
//! `∀` case is the dual. The result is an EQUIVALENT quantifier-free formula
//! — no sampling, no over- or under-approximation.
//!
//! # Use
//!
//! The only consumer is the SAT-only probe `executor::eq_qe_lane`: it solves
//! the eliminated formulas and hands the model to the unchanged publication
//! gates, which re-decide every AUTHORED quantifier against that model with
//! the independent evaluator (`ay-model-check`'s equality-only planner).
//! Nothing here is publication authority.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::{Symbol, TermData};
use ay_core::{Sort, TermId, TermStore};

use crate::ematching::{mk_app_simplified, subst_vars};

/// Most distinct comparison terms one binder may have.
const MAX_COMPARANDS: usize = 64;

/// Shared work allowance for one elimination call (node visits plus the
/// size of every body copy). Exhaustion declines the whole root.
#[derive(Debug)]
pub(crate) struct EqQeBudget {
    work_left: usize,
}

impl EqQeBudget {
    pub(crate) fn new(work: usize) -> Self {
        Self { work_left: work }
    }

    fn charge(&mut self, amount: usize) -> Option<()> {
        self.work_left = self.work_left.checked_sub(amount)?;
        Some(())
    }
}

/// Node-visit cap for the side-effect-free recognizer.
const MAX_RECOGNIZER_VISITS: usize = 1 << 20;

/// Side-effect-free recognizer (mints no term): every quantifier of `root`
/// binds only `Int`/`Real` variables, and every occurrence of a bound
/// variable is a direct argument of a binary `=`/`distinct` whose arguments
/// are each a bare variable or a term mentioning no variable bound at that
/// point. Under this invariant every elimination step of
/// [`eliminate_equality_quantifiers`] stays inside the fragment (it only
/// substitutes bare variables or binder-free terms for bare variables), so
/// the elimination can then fail only on its work budget.
pub(crate) fn in_equality_fragment(terms: &TermStore, root: TermId) -> bool {
    let mut visits = MAX_RECOGNIZER_VISITS;
    let mut scope: Vec<&str> = Vec::new();
    recognize(terms, root, &mut scope, &mut visits).unwrap_or(false)
}

/// `Some(true)` in fragment, `Some(false)` out, `None` visit cap.
fn recognize<'t>(
    terms: &'t TermStore,
    term: TermId,
    scope: &mut Vec<&'t str>,
    visits: &mut usize,
) -> Option<bool> {
    *visits = visits.checked_sub(1)?;
    let bound = |scope: &Vec<&'t str>, t: TermId| -> bool {
        matches!(terms.get(t), TermData::Var(n, _) if scope.contains(&n.as_str()))
    };
    Some(match terms.get(term) {
        TermData::Const(_) => true,
        TermData::Var(name, _) => !scope.contains(&name.as_str()),
        TermData::Forall(vars, body, _) | TermData::Exists(vars, body, _) => {
            if vars
                .iter()
                .any(|(_, sort)| !matches!(sort, Sort::Int | Sort::Real))
            {
                return Some(false);
            }
            let depth = scope.len();
            scope.extend(vars.iter().map(|(name, _)| name.as_str()));
            let ok = recognize(terms, *body, scope, visits);
            scope.truncate(depth);
            ok?
        }
        TermData::App(symbol, args)
            if matches!(symbol.name(), "=" | "distinct")
                && args.len() == 2
                && matches!(terms.sort(args[0]), Sort::Int | Sort::Real)
                && (bound(scope, args[0]) || bound(scope, args[1])) =>
        {
            for &side in args.iter() {
                if bound(scope, side) {
                    continue;
                }
                // A non-variable side must mention no bound variable at all
                // (the model gate's independent planner demands the same).
                if mentions_any(terms, side, scope, visits)? {
                    return Some(false);
                }
            }
            true
        }
        TermData::App(_, args) => {
            for &arg in args.iter() {
                if !recognize(terms, arg, scope, visits)? {
                    return Some(false);
                }
            }
            true
        }
        TermData::Not(inner) => recognize(terms, *inner, scope, visits)?,
        TermData::Ite(c, a, b) => {
            recognize(terms, *c, scope, visits)?
                && recognize(terms, *a, scope, visits)?
                && recognize(terms, *b, scope, visits)?
        }
        // `let` and any other node kind: out of scope.
        _ => false,
    })
}

/// Whether `term` mentions any variable named in `scope` (or holds a node
/// kind this audit does not open). `None` on the visit cap.
fn mentions_any(
    terms: &TermStore,
    term: TermId,
    scope: &[&str],
    visits: &mut usize,
) -> Option<bool> {
    let mut stack = vec![term];
    while let Some(t) = stack.pop() {
        *visits = visits.checked_sub(1)?;
        match terms.get(t) {
            TermData::Var(name, _) => {
                if scope.contains(&name.as_str()) {
                    return Some(true);
                }
            }
            TermData::Const(_) => {}
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, a, b) => stack.extend([*c, *a, *b]),
            _ => return Some(true),
        }
    }
    Some(false)
}

/// Eliminate every quantifier of `root`, or `None` when some quantifier is
/// outside the fragment (or the budget runs out). A quantifier-free `root`
/// is returned unchanged.
pub(crate) fn eliminate_equality_quantifiers(
    terms: &mut TermStore,
    root: TermId,
    budget: &mut EqQeBudget,
) -> Option<TermId> {
    let mut memo: HashMap<TermId, TermId> = HashMap::default();
    eliminate(terms, root, budget, &mut memo)
}

fn eliminate(
    terms: &mut TermStore,
    term: TermId,
    budget: &mut EqQeBudget,
    memo: &mut HashMap<TermId, TermId>,
) -> Option<TermId> {
    if let Some(&done) = memo.get(&term) {
        return Some(done);
    }
    budget.charge(1)?;
    let result = match terms.get(term).clone() {
        TermData::Const(_) | TermData::Var(..) => term,
        TermData::Forall(vars, body, _) | TermData::Exists(vars, body, _) => {
            let universal = matches!(terms.get(term), TermData::Forall(..));
            let mut current = eliminate(terms, body, budget, memo)?;
            for (name, sort) in vars.iter().rev() {
                current = eliminate_binder(terms, name, sort, current, universal, budget)?;
            }
            current
        }
        TermData::Not(inner) => {
            let new_inner = eliminate(terms, inner, budget, memo)?;
            if new_inner == inner {
                term
            } else {
                terms.mk_not(new_inner)
            }
        }
        TermData::Ite(condition, then_term, else_term) => {
            let c = eliminate(terms, condition, budget, memo)?;
            let t = eliminate(terms, then_term, budget, memo)?;
            let e = eliminate(terms, else_term, budget, memo)?;
            if (c, t, e) == (condition, then_term, else_term) {
                term
            } else {
                terms.mk_ite(c, t, e)
            }
        }
        TermData::App(symbol, args) => {
            let mut new_args = Vec::with_capacity(args.len());
            for &arg in &args {
                new_args.push(eliminate(terms, arg, budget, memo)?);
            }
            if new_args == args {
                term
            } else {
                // Only Boolean structure can hold a quantifier; the rebuilt
                // node keeps its authored connective.
                rebuild_app(terms, &symbol, new_args, term)
            }
        }
        // `let` and any other node kind: out of scope. A quantifier-free one
        // is left alone; one hiding a quantifier declines the root.
        _ => {
            if crate::ematching::contains_quantifier(terms, term) {
                return None;
            }
            term
        }
    };
    memo.insert(term, result);
    Some(result)
}

fn rebuild_app(
    terms: &mut TermStore,
    symbol: &Symbol,
    args: Vec<TermId>,
    original: TermId,
) -> TermId {
    match symbol.name() {
        "and" => terms.mk_and(args),
        "or" => terms.mk_or(args),
        _ => mk_app_simplified(terms, symbol, args, original),
    }
}

fn is_binder(terms: &TermStore, term: TermId, name: &str, sort: &Sort) -> bool {
    matches!(terms.get(term), TermData::Var(n, _) if n == name) && terms.sort(term) == sort
}

/// Whether `term` mentions a variable spelled `name` (any sort).
fn mentions(terms: &TermStore, term: TermId, name: &str, budget: &mut EqQeBudget) -> Option<bool> {
    let mut stack = vec![term];
    let mut seen = ay_core::kani_compat::DetHashSet::default();
    while let Some(t) = stack.pop() {
        budget.charge(1)?;
        if !seen.insert(t) {
            continue;
        }
        match terms.get(t) {
            TermData::Var(n, _) => {
                if n == name {
                    return Some(true);
                }
            }
            TermData::Const(_) => {}
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, a, b) => stack.extend([*c, *a, *b]),
            // A quantifier or let here would mean the body is not
            // quantifier-free, which the caller guarantees; refuse anyway.
            _ => return None,
        }
    }
    Some(false)
}

/// The occurrence audit for one binder: the distinct comparison terms, or
/// `None` when the binder occurs outside an admitted atom position.
fn comparands(
    terms: &TermStore,
    body: TermId,
    name: &str,
    sort: &Sort,
    budget: &mut EqQeBudget,
) -> Option<Vec<TermId>> {
    let mut found: Vec<TermId> = Vec::new();
    let mut stack = vec![body];
    let mut seen = ay_core::kani_compat::DetHashSet::default();
    while let Some(t) = stack.pop() {
        budget.charge(1)?;
        if !seen.insert(t) {
            continue;
        }
        match terms.get(t) {
            TermData::Var(n, _) => {
                if n == name {
                    return None;
                }
            }
            TermData::Const(_) => {}
            TermData::App(symbol, args)
                if matches!(symbol.name(), "=" | "distinct")
                    && args.len() == 2
                    && terms.sort(args[0]) == sort
                    && terms.sort(args[1]) == sort
                    && (is_binder(terms, args[0], name, sort)
                        || is_binder(terms, args[1], name, sort)) =>
            {
                for &side in args.iter() {
                    if is_binder(terms, side, name, sort) {
                        continue;
                    }
                    if mentions(terms, side, name, budget)? {
                        return None;
                    }
                    if !found.contains(&side) {
                        if found.len() == MAX_COMPARANDS {
                            return None;
                        }
                        found.push(side);
                    }
                }
            }
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, a, b) => stack.extend([*c, *a, *b]),
            _ => return None,
        }
    }
    Some(found)
}

/// Replace every admitted atom over the binder by its truth value when the
/// binder's value differs from every comparison term.
fn fresh_case(
    terms: &mut TermStore,
    term: TermId,
    name: &str,
    sort: &Sort,
    budget: &mut EqQeBudget,
    memo: &mut HashMap<TermId, TermId>,
) -> Option<TermId> {
    if let Some(&done) = memo.get(&term) {
        return Some(done);
    }
    budget.charge(1)?;
    let result = match terms.get(term).clone() {
        TermData::App(symbol, args)
            if matches!(symbol.name(), "=" | "distinct")
                && args.len() == 2
                && terms.sort(args[0]) == sort
                && terms.sort(args[1]) == sort
                && (is_binder(terms, args[0], name, sort)
                    || is_binder(terms, args[1], name, sort)) =>
        {
            let same = args[0] == args[1];
            let equal = same;
            terms.mk_bool(if symbol.name() == "=" { equal } else { !equal })
        }
        TermData::App(symbol, args) => {
            let mut new_args = Vec::with_capacity(args.len());
            for &arg in &args {
                new_args.push(fresh_case(terms, arg, name, sort, budget, memo)?);
            }
            if new_args == args {
                term
            } else {
                rebuild_app(terms, &symbol, new_args, term)
            }
        }
        TermData::Not(inner) => {
            let new_inner = fresh_case(terms, inner, name, sort, budget, memo)?;
            if new_inner == inner {
                term
            } else {
                terms.mk_not(new_inner)
            }
        }
        TermData::Ite(c, a, b) => {
            let nc = fresh_case(terms, c, name, sort, budget, memo)?;
            let na = fresh_case(terms, a, name, sort, budget, memo)?;
            let nb = fresh_case(terms, b, name, sort, budget, memo)?;
            if (nc, na, nb) == (c, a, b) {
                term
            } else {
                terms.mk_ite(nc, na, nb)
            }
        }
        TermData::Const(_) | TermData::Var(..) => term,
        _ => return None,
    };
    memo.insert(term, result);
    Some(result)
}

/// Eliminate one binder from a quantifier-free body (module header).
fn eliminate_binder(
    terms: &mut TermStore,
    name: &str,
    sort: &Sort,
    body: TermId,
    universal: bool,
    budget: &mut EqQeBudget,
) -> Option<TermId> {
    if !matches!(sort, Sort::Int | Sort::Real) {
        return None;
    }
    if !mentions(terms, body, name, budget)? {
        // Vacuous over a non-empty carrier.
        return Some(body);
    }
    let comparison = comparands(terms, body, name, sort, budget)?;
    let body_size = dag_size(terms, body, budget)?;
    budget.charge(body_size.saturating_mul(comparison.len() + 1))?;
    let mut cases = Vec::with_capacity(comparison.len() + 1);
    for &t in &comparison {
        let mut subst: HashMap<String, TermId> = HashMap::default();
        subst.insert(name.to_string(), t);
        cases.push(subst_vars(terms, body, &subst));
    }
    let mut memo = HashMap::default();
    cases.push(fresh_case(terms, body, name, sort, budget, &mut memo)?);
    Some(if universal {
        terms.mk_and(cases)
    } else {
        terms.mk_or(cases)
    })
}

fn dag_size(terms: &TermStore, root: TermId, budget: &mut EqQeBudget) -> Option<usize> {
    let mut stack = vec![root];
    let mut seen = ay_core::kani_compat::DetHashSet::default();
    while let Some(t) = stack.pop() {
        budget.charge(1)?;
        if seen.insert(t) {
            stack.extend(terms.children(t));
        }
    }
    Some(seen.len())
}

#[cfg(test)]
mod tests;
