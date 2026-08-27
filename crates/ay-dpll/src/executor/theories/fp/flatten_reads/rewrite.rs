// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The substitution pass and its fail-closed residue check.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::TermData;
use ay_core::{Sort, TermId, TermStore};

/// Stack red zone / growth for the DAG rewrite (KLEE queries nest deeply).
const FLATTEN_STACK_RED_ZONE: usize = 128 * 1024;
const FLATTEN_STACK_SIZE: usize = 16 * 1024 * 1024;

/// Rewrite `term`, replacing each planned `select` with its fresh constant.
/// Structure-preserving everywhere else.
pub(super) fn rewrite(
    terms: &mut TermStore,
    term: TermId,
    subst: &HashMap<TermId, TermId>,
    memo: &mut HashMap<TermId, TermId>,
) -> TermId {
    stacker::maybe_grow(FLATTEN_STACK_RED_ZONE, FLATTEN_STACK_SIZE, || {
        if let Some(&hit) = memo.get(&term) {
            return hit;
        }
        if let Some(&fresh) = subst.get(&term) {
            memo.insert(term, fresh);
            return fresh;
        }
        let result = match terms.get(term).clone() {
            TermData::App(sym, args) => {
                let new_args: Vec<TermId> = args
                    .iter()
                    .map(|&a| rewrite(terms, a, subst, memo))
                    .collect();
                if new_args == args {
                    term
                } else {
                    let sort = terms.sort(term).clone();
                    terms.mk_app(sym, new_args, sort)
                }
            }
            TermData::Not(inner) => {
                let new_inner = rewrite(terms, inner, subst, memo);
                if new_inner == inner {
                    term
                } else {
                    terms.mk_not_raw(new_inner)
                }
            }
            TermData::Ite(c, t, e) => {
                let nc = rewrite(terms, c, subst, memo);
                let nt = rewrite(terms, t, subst, memo);
                let ne = rewrite(terms, e, subst, memo);
                if nc == c && nt == t && ne == e {
                    term
                } else {
                    terms.mk_ite_raw(nc, nt, ne)
                }
            }
            // Everything else is a leaf for this rewrite. `plan_cells` already
            // refused `let`/quantifier shapes, so nothing reachable can hide a
            // `select` here; `is_array_free` re-verifies it anyway.
            _ => term,
        };
        memo.insert(term, result);
        result
    })
}

/// FAIL-CLOSED BACKSTOP: no array-sorted term, `select` or `store` may survive.
///
/// This is not decoration. `plan_cells` and `rewrite` walk the DAG
/// independently; if they ever disagree (a future `TermData` variant, a shape
/// the rewriter treats as a leaf) the residue would be an array term handed to
/// a solver that cannot see the array theory — the #8728 failure mode.
/// Detecting it here converts that into an abstention.
pub(super) fn is_array_free(terms: &TermStore, assertions: &[TermId]) -> bool {
    let mut visited: HashSet<TermId> = HashSet::default();
    let mut stack: Vec<TermId> = assertions.to_vec();
    while let Some(term) = stack.pop() {
        if !visited.insert(term) {
            continue;
        }
        if matches!(terms.sort(term), Sort::Array(_)) {
            return false;
        }
        match terms.get(term) {
            TermData::App(sym, args) => {
                if matches!(
                    sym.name(),
                    "select" | "store" | "const-array" | "lambda-array"
                ) {
                    return false;
                }
                stack.extend_from_slice(args);
            }
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, t, e) => {
                stack.push(*c);
                stack.push(*t);
                stack.push(*e);
            }
            TermData::Let(bindings, body) => {
                stack.extend(bindings.iter().map(|(_, v)| *v));
                stack.push(*body);
            }
            TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => stack.push(*body),
            _ => {}
        }
    }
    true
}
