// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `qe-light` preprocessing pass: reachable Cooper LIA quantifier elimination.
//!
//! Walks each assertion's term DAG and replaces every `(exists ((x Int)) φ)`
//! subterm that falls inside Cooper's supported fragment with the
//! quantifier-free equivalent produced by
//! [`crate::qe::eliminate_exists`]. Anything outside the fragment is left
//! **byte-for-byte unchanged** (faithful identity).
//!
//! # Fragment (what is eliminated)
//!
//! Only `∃x. φ` where:
//! * exactly ONE bound variable `x`, of sort [`Sort::Int`], and
//! * `φ` is a conjunction of supported linear-integer literals
//!   (`t ≤ 0`, `t < 0`, `t = 0`, `t ≠ 0`, `d | t`; see [`crate::qe::cooper`]).
//!
//! Every other shape — universals, multi-variable existentials, non-Int bound
//! sorts, nested/alternating quantifiers, non-linear or disjunctive matrices —
//! is refused by `eliminate_exists` (returns
//! [`QeResult::NotSupported`](crate::qe::QeResult::NotSupported)), so the pass
//! keeps the original quantified node verbatim.
//!
//! # Publication boundary
//!
//! Cooper implements an equivalence-preserving algorithm and its candidate is
//! screened by an independent finite differential battery. The battery is not
//! a proof over every valuation of the remaining free variables. Consequently
//! this pass is a candidate producer, not public verdict authority: decision
//! paths must either retain the exact quantified roots or compose a changed
//! root with a separate symbolic equivalence certificate. On every refused node
//! the pass remains the byte-for-byte identity.
//!
//! # Capture safety
//!
//! We only ever *consume* an `Exists` node by replacing the whole node with a
//! formula over its FREE variables (the eliminated `x` does not occur in the
//! result). We never push a rewrite *through* a binder, so no free variable can
//! be captured. A quantifier we cannot eliminate is returned unchanged, so its
//! body (and any binder inside it) is untouched.
//!
//! Recovering the eliminated variable's identity is load-bearing here: the
//! elaborator builds bound variables with `mk_fresh_var`, which does NOT
//! register the fresh name in the intern-by-name table, so re-interning via
//! `mk_var(name)` would mint a *distinct phantom* variable that never occurs in
//! the body. Cooper would then "eliminate" that non-occurring variable, leave
//! the real bound variable dangling free, and produce an unsound (under
//! negation, UNSAT→SAT) result. We therefore recover the exact bound-variable
//! node by scanning the body for the matching `Var` ([`find_bound_var`]), and
//! fail-closed via a final [`mentions_var`] gate that refuses to emit any result
//! still referencing the eliminated variable.

use super::PreprocessingPass;
use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::TermData;
use ay_core::{Sort, TermId, TermStore};
use std::collections::HashSet;

use crate::qe::{eliminate_exists, QeResult};

/// Replace in-fragment `(exists ((x Int)) φ)` subterms with their Cooper
/// quantifier-free equivalents; identity everywhere else.
pub(crate) struct QeLight {
    /// Whether any node was actually rewritten during the current `apply`.
    progress: bool,
}

impl QeLight {
    pub(crate) fn new() -> Self {
        Self { progress: false }
    }
}

impl Default for QeLight {
    fn default() -> Self {
        Self::new()
    }
}

impl PreprocessingPass for QeLight {
    fn apply(&mut self, terms: &mut TermStore, assertions: &mut Vec<TermId>) -> bool {
        self.progress = false;
        // Memoize the rewrite over the shared hash-consed DAG so each distinct
        // subterm is processed once. The cache is local to this `apply` call.
        let mut cache: HashMap<TermId, TermId> = HashMap::default();
        for a in assertions.iter_mut() {
            *a = rewrite(terms, *a, &mut cache, &mut self.progress);
        }
        self.progress
    }

    fn reset(&mut self) {
        self.progress = false;
    }
}

/// Post-order rewrite of `term`: rebuild children, eliminating any in-fragment
/// `Exists` subterm. Returns the (possibly identical) rewritten term.
///
/// Sets `*progress = true` exactly when an `Exists` node is replaced by its
/// eliminated equivalent. Children are rebuilt with the folding constructors so
/// the rewritten DAG is the same shape AY would have built natively.
fn rewrite(
    terms: &mut TermStore,
    term: TermId,
    cache: &mut HashMap<TermId, TermId>,
    progress: &mut bool,
) -> TermId {
    if let Some(&cached) = cache.get(&term) {
        return cached;
    }

    let result = match terms.get(term).clone() {
        // Leaves: nothing to rewrite.
        TermData::Const(_) | TermData::Var(_, _) => term,

        TermData::App(sym, args) => {
            let mut changed = false;
            let new_args: Vec<TermId> = args
                .iter()
                .map(|&arg| {
                    let na = rewrite(terms, arg, cache, progress);
                    changed |= na != arg;
                    na
                })
                .collect();
            if changed {
                let sort = terms.sort(term).clone();
                terms.mk_app(sym, new_args, sort)
            } else {
                term
            }
        }

        TermData::Not(inner) => {
            let ni = rewrite(terms, inner, cache, progress);
            if ni == inner {
                term
            } else {
                terms.mk_not(ni)
            }
        }

        TermData::Ite(c, t, e) => {
            let nc = rewrite(terms, c, cache, progress);
            let nt = rewrite(terms, t, cache, progress);
            let ne = rewrite(terms, e, cache, progress);
            if nc == c && nt == t && ne == e {
                term
            } else {
                terms.mk_ite(nc, nt, ne)
            }
        }

        // We deliberately do NOT descend into Let bodies (a `let` should have
        // been expanded before solving); leave it untouched.
        TermData::Let(_, _) => term,

        // Universals are out of fragment — keep the node verbatim.
        TermData::Forall(_, _, _) => term,

        TermData::Exists(vars, _body, _triggers) => {
            try_eliminate_exists(terms, term, &vars, progress)
        }

        // `TermData` is `#[non_exhaustive]`: any future node kind is left
        // UNCHANGED (faithful identity), never silently rewritten.
        _ => term,
    };

    cache.insert(term, result);
    result
}

/// Attempt Cooper elimination on a single `Exists` node.
///
/// Returns the eliminated quantifier-free equivalent (and sets `*progress`) on
/// success; returns the ORIGINAL node unchanged on any out-of-fragment / refused
/// case. We do not recurse into the body of a quantifier we cannot eliminate, so
/// its binder scope stays intact (no variable capture).
fn try_eliminate_exists(
    terms: &mut TermStore,
    original: TermId,
    vars: &[(String, Sort)],
    progress: &mut bool,
) -> TermId {
    // Cooper's fragment eliminates exactly one Int-sorted variable. Anything
    // else (no vars, multiple vars, or a non-Int sort) is out of fragment: keep
    // the original node.
    let [(name, sort)] = vars else {
        return original;
    };
    if *sort != Sort::Int {
        return original;
    }

    // Recover the matrix `φ`. The body is the quantifier's second field; we read
    // it back from the live node so we operate on the exact stored term.
    let TermData::Exists(_, body, _) = terms.get(original).clone() else {
        // Unreachable: caller matched Exists. Be conservative and keep it.
        return original;
    };

    // Recover the EXACT bound-variable identity as it occurs in the body.
    //
    // We must NOT re-intern via `terms.mk_var(name, Int)`: the elaborator builds
    // bound variables with `mk_fresh_var`, which mints a fresh `Var(name, id)`
    // WITHOUT registering `name` in the intern-by-name table. So `mk_var(name)`
    // would create a DISTINCT phantom variable that never occurs in the body —
    // Cooper would then "eliminate" a non-occurring variable, trivially return
    // the body, and leave the real bound variable dangling FREE. That strip is
    // unsound to print: under a negation it flips an UNSAT assertion like
    // `(not (exists ((x Int)) (and (< 0 x) (< x 5))))` into a satisfiable goal.
    // Find the real node by scanning the body for the `Var` whose name matches
    // the binding; `mk_fresh_var` uniquifies bound names, so the match is
    // unambiguous.
    let Some(var) = find_bound_var(terms, body, name) else {
        // The bound variable does not occur in the body (vacuous quantifier):
        // refusing is always sound, so keep the original node verbatim.
        return original;
    };

    match eliminate_exists(terms, body, var) {
        // The candidate passed Cooper's bounded differential check. Public
        // decision code must still retain the source or provide independent
        // symbolic equivalence authority before adopting this changed root.
        QeResult::Eliminated(qf) => {
            // Capture-safety gate (defence in depth): never emit a result that
            // still references the eliminated variable — a freed binder is
            // exactly the unsoundness this pass must avoid. Cooper's self-check
            // already guarantees closure; re-checking here keeps the property
            // local and fail-closed.
            if mentions_var(terms, qf, var) {
                return original;
            }
            *progress = true;
            qf
        }
        // Fail-closed: keep the original quantified node verbatim.
        QeResult::NotSupported => original,
    }
}

/// Find the hash-consed `Var` node named `name` — the exact bound-variable
/// identity as it appears in `term`. `mk_fresh_var` uniquifies bound-variable
/// names, so a body normally holds at most one such `Var`; however
/// `mk_fresh_var` does NOT register the fresh name in the intern-by-name
/// table, so a later `mk_var` with an identical name can mint a second,
/// distinct `Var` node. If more than one distinct `Var` matches the name we
/// cannot tell which is the bound one, so we refuse (`None`): eliminating the
/// wrong node would leave the real bound variable dangling free — the exact
/// UNSAT→SAT hazard documented in the module header — and both fail-closed
/// gates (Cooper's self-check and [`mentions_var`]) would check the wrong
/// node.
///
/// Returns `None` when the name does not occur (e.g. a vacuous quantifier or a
/// future node kind we do not traverse) or is ambiguous, in which case the
/// caller keeps the original node — always the sound, conservative choice.
pub(crate) fn find_bound_var(terms: &TermStore, term: TermId, name: &str) -> Option<TermId> {
    let mut stack = vec![term];
    let mut seen: HashSet<TermId> = HashSet::new();
    let mut found: Option<TermId> = None;
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        match terms.get(t) {
            TermData::Var(n, _) if n.as_str() == name => match found {
                // Two DISTINCT Var nodes share the binder's name: ambiguous.
                Some(prev) if prev != t => return None,
                _ => found = Some(t),
            },
            TermData::Var(_, _) | TermData::Const(_) => {}
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, th, e) => {
                stack.push(*c);
                stack.push(*th);
                stack.push(*e);
            }
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Let(bindings, b) => {
                for (_, v) in bindings {
                    stack.push(*v);
                }
                stack.push(*b);
            }
            TermData::Forall(_, b, _) | TermData::Exists(_, b, _) => stack.push(*b),
            // `TermData` is `#[non_exhaustive]`: an unrecognized node is not
            // traversed, so we may fail to find the var — which is safe (the
            // caller keeps the original quantifier).
            _ => {}
        }
    }
    found
}

/// Whether `var` (by hash-consed identity) occurs anywhere in `term`.
pub(crate) fn mentions_var(terms: &TermStore, term: TermId, var: TermId) -> bool {
    let mut stack = vec![term];
    let mut seen: HashSet<TermId> = HashSet::new();
    while let Some(t) = stack.pop() {
        if t == var {
            return true;
        }
        if !seen.insert(t) {
            continue;
        }
        match terms.get(t) {
            TermData::Var(_, _) | TermData::Const(_) => {}
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, th, e) => {
                stack.push(*c);
                stack.push(*th);
                stack.push(*e);
            }
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Let(bindings, b) => {
                for (_, v) in bindings {
                    stack.push(*v);
                }
                stack.push(*b);
            }
            TermData::Forall(_, b, _) | TermData::Exists(_, b, _) => stack.push(*b),
            _ => {}
        }
    }
    false
}

#[cfg(test)]
#[path = "qe_light_tests.rs"]
mod tests;
