// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Term helpers shared by the pipeline passes: quantifier views, binder-aware
//! free-name collection, clause views, and the folding rebuild every pass uses
//! after a substitution.
//!
//! Bound variables are `Var` nodes whose NAME is bound by the enclosing
//! quantifier's variable list; scoping is by name, exactly as in
//! [`crate::ematching::subst_vars`], which every pass here uses for its
//! (capture-avoiding) substitutions. Walks that meet a `TermData` variant they
//! do not know answer conservatively (the name "occurs", the term "is not
//! closed"), so an unknown node can only block a rewrite, never license one.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::TermData;
use ay_core::{Sort, TermId, TermStore};

/// Red zone / segment size for the recursive walks below (same values as the
/// skolemizer's, #8414).
const STACK_RED_ZONE: usize = 32 * 1024;
const STACK_SIZE: usize = 1024 * 1024;

/// Which binder a quantifier node carries.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Binder {
    Forall,
    Exists,
}

/// An owned view of one quantifier node.
#[derive(Clone, Debug)]
pub(super) struct Quantifier {
    pub(super) binder: Binder,
    pub(super) vars: Vec<(String, Sort)>,
    pub(super) body: TermId,
    pub(super) triggers: Vec<Vec<TermId>>,
}

/// View `t` as a quantifier, if it is one.
pub(super) fn as_quantifier(terms: &TermStore, t: TermId) -> Option<Quantifier> {
    match terms.get(t) {
        TermData::Forall(vars, body, triggers) => Some(Quantifier {
            binder: Binder::Forall,
            vars: vars.clone(),
            body: *body,
            triggers: triggers.clone(),
        }),
        TermData::Exists(vars, body, triggers) => Some(Quantifier {
            binder: Binder::Exists,
            vars: vars.clone(),
            body: *body,
            triggers: triggers.clone(),
        }),
        _ => None,
    }
}

/// Rebuild a quantifier from its parts. An empty variable list yields the
/// body itself (a binder over no variables is its body). Metadata (qid,
/// weight, no-patterns, no-mbqi) is carried over from `original`.
pub(super) fn rebuild_quantifier(
    terms: &mut TermStore,
    original: TermId,
    binder: Binder,
    vars: Vec<(String, Sort)>,
    body: TermId,
    triggers: Vec<Vec<TermId>>,
) -> TermId {
    if vars.is_empty() {
        return body;
    }
    // A constant body makes the binder vacuous (non-empty sorts).
    if matches!(terms.get(body), TermData::Const(_)) {
        return body;
    }
    let rebuilt = match binder {
        Binder::Forall => terms.mk_forall_with_triggers(vars, body, triggers),
        Binder::Exists => terms.mk_exists_with_triggers(vars, body, triggers),
    };
    if rebuilt != original {
        terms.copy_quantifier_metadata(original, rebuilt);
    }
    rebuilt
}

/// Keep only the trigger groups that mention none of `eliminated`.
pub(super) fn triggers_without(
    terms: &TermStore,
    triggers: &[Vec<TermId>],
    eliminated: &HashSet<String>,
) -> Vec<Vec<TermId>> {
    triggers
        .iter()
        .filter(|group| {
            !group
                .iter()
                .any(|&t| mentions_any_name(terms, t, eliminated))
        })
        .cloned()
        .collect()
}

/// Does any `Var` whose name is in `names` occur anywhere under `t` (bound or
/// free, at any depth)? Conservative: an unknown node counts as a mention.
pub(super) fn mentions_any_name(terms: &TermStore, t: TermId, names: &HashSet<String>) -> bool {
    if names.is_empty() {
        return false;
    }
    let mut seen: HashSet<TermId> = HashSet::default();
    let mut stack = vec![t];
    while let Some(cur) = stack.pop() {
        if !seen.insert(cur) {
            continue;
        }
        match terms.get(cur) {
            TermData::Const(_) => {}
            TermData::Var(name, _) => {
                if names.contains(name) {
                    return true;
                }
            }
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, a, b) => stack.extend([*c, *a, *b]),
            TermData::Let(bindings, body) => {
                stack.extend(bindings.iter().map(|(_, v)| *v));
                stack.push(*body);
            }
            TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
                stack.push(*body);
                for group in triggers {
                    stack.extend(group.iter().copied());
                }
            }
            _ => return true,
        }
    }
    false
}

/// Does an application headed by `head` (a `Symbol::Named` spelling) occur
/// anywhere under `t`, including inside binder bodies and triggers?
/// Conservative: an unknown node counts as an occurrence.
pub(super) fn mentions_head(terms: &TermStore, t: TermId, head: &str) -> bool {
    let mut seen: HashSet<TermId> = HashSet::default();
    let mut stack = vec![t];
    while let Some(cur) = stack.pop() {
        if !seen.insert(cur) {
            continue;
        }
        match terms.get(cur) {
            TermData::Const(_) => {}
            // A nullary symbol is a `Var`; macro heads always have arity >= 1,
            // but refuse a same-named variable too so a spelling clash can
            // only block the elimination.
            TermData::Var(name, _) => {
                if name == head {
                    return true;
                }
            }
            TermData::App(sym, args) => {
                if sym.name() == head {
                    return true;
                }
                stack.extend(args.iter().copied());
            }
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, a, b) => stack.extend([*c, *a, *b]),
            TermData::Let(bindings, body) => {
                stack.extend(bindings.iter().map(|(_, v)| *v));
                stack.push(*body);
            }
            TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
                stack.push(*body);
                for group in triggers {
                    stack.extend(group.iter().copied());
                }
            }
            _ => return true,
        }
    }
    false
}

/// The names occurring FREE in `t` (respecting nested binders).
///
/// Returns `None` when the term contains a node kind this walk does not model
/// (callers then refuse the rewrite).
pub(super) fn free_names(terms: &TermStore, t: TermId) -> Option<HashSet<String>> {
    fn walk(
        terms: &TermStore,
        t: TermId,
        bound: &mut Vec<String>,
        out: &mut HashSet<String>,
        memo: &mut HashSet<TermId>,
    ) -> bool {
        stacker::maybe_grow(STACK_RED_ZONE, STACK_SIZE, || {
            // Memoize only at binder-free depth: under a binder the answer
            // depends on the bound set.
            if bound.is_empty() && !memo.insert(t) {
                return true;
            }
            match terms.get(t) {
                TermData::Const(_) => true,
                TermData::Var(name, _) => {
                    if !bound.iter().any(|b| b == name) {
                        out.insert(name.clone());
                    }
                    true
                }
                TermData::App(_, args) => {
                    let args = args.clone();
                    args.iter().all(|&a| walk(terms, a, bound, out, memo))
                }
                TermData::Not(inner) => walk(terms, *inner, bound, out, memo),
                TermData::Ite(c, a, b) => {
                    let (c, a, b) = (*c, *a, *b);
                    walk(terms, c, bound, out, memo)
                        && walk(terms, a, bound, out, memo)
                        && walk(terms, b, bound, out, memo)
                }
                TermData::Let(bindings, body) => {
                    let (bindings, body) = (bindings.clone(), *body);
                    if !bindings
                        .iter()
                        .all(|(_, v)| walk(terms, *v, bound, out, memo))
                    {
                        return false;
                    }
                    let depth = bound.len();
                    bound.extend(bindings.iter().map(|(n, _)| n.clone()));
                    let ok = walk(terms, body, bound, out, memo);
                    bound.truncate(depth);
                    ok
                }
                TermData::Forall(vars, body, triggers) | TermData::Exists(vars, body, triggers) => {
                    let (vars, body, triggers) = (vars.clone(), *body, triggers.clone());
                    let depth = bound.len();
                    bound.extend(vars.iter().map(|(n, _)| n.clone()));
                    let mut ok = walk(terms, body, bound, out, memo);
                    for group in &triggers {
                        for &trig in group {
                            ok = ok && walk(terms, trig, bound, out, memo);
                        }
                    }
                    bound.truncate(depth);
                    ok
                }
                _ => false,
            }
        })
    }
    let mut out = HashSet::default();
    let mut memo = HashSet::default();
    walk(terms, t, &mut Vec::new(), &mut out, &mut memo).then_some(out)
}

/// The literal view of a quantifier body: the disjuncts of a `∀` clause or the
/// conjuncts of a `∃` matrix, flattened through nested `or`/`and`, `=>` and
/// De Morgan (`¬(a ∧ b)` contributes `¬a`, `¬b` to a clause). Rebuilding the
/// returned literals with `mk_or` (`∀`) / `mk_and` (`∃`) gives a body
/// equivalent to the input.
pub(super) fn body_literals(terms: &mut TermStore, body: TermId, binder: Binder) -> Vec<TermId> {
    // (term, polarity): a positive entry contributes `term`, a negative one
    // contributes `¬term`.
    let mut out = Vec::new();
    let mut stack = vec![(body, true)];
    let (join, meet) = match binder {
        Binder::Forall => ("or", "and"),
        Binder::Exists => ("and", "or"),
    };
    while let Some((t, positive)) = stack.pop() {
        match terms.get(t).clone() {
            TermData::Not(inner) => stack.push((inner, !positive)),
            TermData::App(sym, args) if positive && sym.name() == join => {
                stack.extend(args.iter().rev().map(|&a| (a, true)));
            }
            TermData::App(sym, args) if !positive && sym.name() == meet => {
                stack.extend(args.iter().rev().map(|&a| (a, false)));
            }
            // `a => b` is a clause `¬a ∨ b`; its negation is the matrix `a ∧ ¬b`.
            TermData::App(sym, args)
                if sym.name() == "=>"
                    && args.len() == 2
                    && positive == (binder == Binder::Forall) =>
            {
                let (lhs, rhs) = (args[0], args[1]);
                stack.push((rhs, positive));
                stack.push((lhs, !positive));
            }
            _ => out.push(if positive { t } else { terms.mk_not(t) }),
        }
    }
    out
}

/// `(= a b)` with exactly two arguments: return them.
pub(super) fn as_binary_eq(terms: &TermStore, t: TermId) -> Option<(TermId, TermId)> {
    match terms.get(t) {
        TermData::App(sym, args) if sym.name() == "=" && args.len() == 2 => {
            Some((args[0], args[1]))
        }
        _ => None,
    }
}

/// `(not (= a b))`: return `a`, `b`.
pub(super) fn as_binary_diseq(terms: &TermStore, t: TermId) -> Option<(TermId, TermId)> {
    match terms.get(t) {
        TermData::Not(inner) => as_binary_eq(terms, *inner),
        _ => None,
    }
}

/// Is `t` the variable spelled `name`?
pub(super) fn is_var_named(terms: &TermStore, t: TermId, name: &str) -> bool {
    matches!(terms.get(t), TermData::Var(n, _) if n == name)
}

/// Tree size of `t` (shared subterms counted once per occurrence), saturating
/// at `limit + 1`. Used to refuse walks that are not DAG-memoized.
pub(super) fn tree_size_exceeds(terms: &TermStore, t: TermId, limit: u64) -> bool {
    fn size(terms: &TermStore, t: TermId, memo: &mut HashMap<TermId, u64>, cap: u64) -> u64 {
        if let Some(&s) = memo.get(&t) {
            return s;
        }
        let children: Vec<TermId> = match terms.get(t) {
            TermData::Const(_) | TermData::Var(_, _) => Vec::new(),
            TermData::App(_, args) => args.clone(),
            TermData::Not(inner) => vec![*inner],
            TermData::Ite(c, a, b) => vec![*c, *a, *b],
            TermData::Let(bindings, body) => {
                let mut v: Vec<TermId> = bindings.iter().map(|(_, x)| *x).collect();
                v.push(*body);
                v
            }
            TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => vec![*body],
            _ => return cap,
        };
        let mut total: u64 = 1;
        for c in children {
            let s = stacker::maybe_grow(STACK_RED_ZONE, STACK_SIZE, || size(terms, c, memo, cap));
            total = total.saturating_add(s).min(cap);
        }
        memo.insert(t, total);
        total
    }
    let cap = limit.saturating_add(1);
    size(terms, t, &mut HashMap::default(), cap) > limit
}

/// The number of distinct quantifier nodes under `t` (DAG-shared nodes once).
pub(super) fn quantifier_count(terms: &TermStore, t: TermId) -> usize {
    let mut seen: HashSet<TermId> = HashSet::default();
    let mut stack = vec![t];
    let mut count = 0;
    while let Some(cur) = stack.pop() {
        if !seen.insert(cur) {
            continue;
        }
        match terms.get(cur) {
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, a, b) => stack.extend([*c, *a, *b]),
            TermData::Let(bindings, body) => {
                stack.extend(bindings.iter().map(|(_, v)| *v));
                stack.push(*body);
            }
            TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => {
                count += 1;
                stack.push(*body);
            }
            _ => {}
        }
    }
    count
}
