// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Destructive Equality Resolution (z3's `der` tactic).
//!
//! For a top-level universally quantified clause
//!
//! ```text
//! (forall (… x …) (or … (not (= x t)) … R …))
//! ```
//!
//! where `t` is free of `x` (occurs-check), the negated-equality literal is
//! resolved away by the one-point rule and every remaining literal has `x`
//! replaced by `t`:
//!
//! ```text
//! (forall (…) (or … R[x:=t] …))
//! ```
//!
//! This is applied to a fixpoint, one eliminable variable at a time, and it
//! also handles the mirrored `(not (= t x))` shape (measured: z3 resolves both
//! directions). Because AY stores `(=> a b)` as `(or (not a) b)`, the implication
//! sugar `(forall (x) (=> (= x t) R))` is already a clause and needs no special
//! desugaring here.
//!
//! # Soundness
//!
//! EQUIVALENCE-PRESERVING. `∀x. (x ≠ t ∨ C(x)) ≡ C(t)` when `t` does not mention
//! `x` (the one-point rule: the clause can only fail at `x = t`, where it demands
//! `C(t)`). Multi-literal and multi-variable clauses iterate this equivalence.
//! An empty residual clause means `∀x. ¬(x = t)`, which is unsatisfiable for any
//! ground `t` (the domain contains `t`), so the assertion collapses to `false`.
//!
//! ## Capture safety (the fail-closed guard)
//!
//! [`TermStore::substitute`] is **not** capture-avoiding: it rewrites the bodies
//! of nested binders structurally (`subst.rs`), and bound variables are interned
//! `Var` nodes matched by identity. Substituting `x := t` into a clause that
//! nests a `∀`/`∃`/`let` binding a name that occurs free in `t` (or in the
//! clause) would therefore CAPTURE — turning a satisfiable input into an
//! unsatisfiable transformed goal (a wrong verdict). z3 dodges this by renaming
//! the inner binder; AY instead **fail-closes**: if the quantifier body contains
//! ANY nested `Forall`/`Exists`/`Let` binder, der leaves the whole assertion
//! untouched (the sound identity). No nested binder ⇒ no scope for `t`'s free
//! variables to be captured, so the substitution is safe. This conservative
//! superset covers both outer-variable shadowing AND replacement-term capture
//! (the two soundness holes found in adversarial review).
//!
//! # Scope
//!
//! Apply-surface only: this is a plain struct with an `apply` method, NOT a
//! [`super::PreprocessingPass`], so it is never auto-enrolled in the solve
//! pipeline — plain `check-sat` behavior is byte-for-byte unchanged.

use ay_core::kani_compat::{det_hash_set_new, DetHashSet as HashSet};
use ay_core::term::{Symbol, TermData};
use ay_core::{Sort, TermId, TermStore};

/// The `der` goal transform.
pub(crate) struct Der;

impl Der {
    pub(crate) fn new() -> Self {
        Der
    }

    /// Resolve negated-equality literals in every top-level `forall` assertion.
    /// Returns whether any assertion changed.
    pub(crate) fn apply(&mut self, terms: &mut TermStore, assertions: &mut [TermId]) -> bool {
        let mut changed = false;
        for a in assertions.iter_mut() {
            if let Some(new) = der_assertion(terms, *a) {
                if new != *a {
                    *a = new;
                    changed = true;
                }
            }
        }
        changed
    }
}

/// Apply DER to a single assertion, or `None` if it is not a `forall` clause or
/// nothing could be eliminated (or the fail-closed guard fired).
fn der_assertion(terms: &mut TermStore, a: TermId) -> Option<TermId> {
    let (vars, body) = match terms.get(a).clone() {
        TermData::Forall(vars, body, _triggers) => (vars, body),
        _ => return None,
    };

    // Fail-closed capture guard: any nested binder ⇒ leave the assertion alone.
    if has_binder(terms, body, &mut det_hash_set_new()) {
        return None;
    }

    let mut bound: Vec<(String, Sort)> = vars;
    let mut disjuncts = clause_disjuncts(terms, body);
    let mut eliminated_any = false;

    loop {
        // Find a still-bound variable that a residual disequality literal pins
        // to an occurrence-free term.
        let mut found: Option<(usize, usize, TermId, TermId)> = None;
        'search: for (vi, (vname, _)) in bound.iter().enumerate() {
            for (di, &d) in disjuncts.iter().enumerate() {
                if let Some((vterm, rterm)) = diseq_on_var(terms, d, vname) {
                    if !occurs(terms, vterm, rterm, &mut det_hash_set_new()) {
                        found = Some((vi, di, vterm, rterm));
                        break 'search;
                    }
                }
            }
        }
        let Some((vi, di, vterm, rterm)) = found else {
            break;
        };

        // Resolve away the disequality literal and substitute into the rest.
        let _ = disjuncts.remove(di);
        for d in disjuncts.iter_mut() {
            *d = terms.substitute(*d, &[vterm], &[rterm]);
        }
        bound.remove(vi);
        eliminated_any = true;
    }

    if !eliminated_any {
        return None;
    }

    // Empty residual ⇒ `∀x. ¬(x = t)` is `false`; `mk_or([])` yields `false`.
    let new_body = terms.mk_or(disjuncts);
    if bound.is_empty() {
        Some(new_body)
    } else {
        Some(terms.mk_forall(bound, new_body))
    }
}

/// View a clause body as a list of disjuncts: the arguments of a top-level `or`,
/// else the single literal.
fn clause_disjuncts(terms: &TermStore, body: TermId) -> Vec<TermId> {
    match terms.get(body) {
        TermData::App(Symbol::Named(n), args) if n == "or" => args.clone(),
        _ => vec![body],
    }
}

/// If `d` is `(not (= v r))` or `(not (= r v))` with `v` a `Var` named `vname`,
/// return `(v_termid, r)`.
fn diseq_on_var(terms: &TermStore, d: TermId, vname: &str) -> Option<(TermId, TermId)> {
    let TermData::Not(inner) = terms.get(d) else {
        return None;
    };
    let inner = *inner;
    let TermData::App(Symbol::Named(n), args) = terms.get(inner) else {
        return None;
    };
    if n != "=" || args.len() != 2 {
        return None;
    }
    let (l, r) = (args[0], args[1]);
    if is_var_named(terms, l, vname) {
        return Some((l, r));
    }
    if is_var_named(terms, r, vname) {
        return Some((r, l));
    }
    None
}

fn is_var_named(terms: &TermStore, t: TermId, vname: &str) -> bool {
    matches!(terms.get(t), TermData::Var(n, _) if n == vname)
}

/// Does `needle` appear as a subterm of `hay` (by hash-consed identity)?
fn occurs(terms: &TermStore, needle: TermId, hay: TermId, seen: &mut HashSet<TermId>) -> bool {
    if needle == hay {
        return true;
    }
    if !seen.insert(hay) {
        return false;
    }
    match terms.get(hay).clone() {
        TermData::Const(_) | TermData::Var(_, _) => false,
        TermData::Not(i) => occurs(terms, needle, i, seen),
        TermData::Ite(c, t, e) => {
            occurs(terms, needle, c, seen)
                || occurs(terms, needle, t, seen)
                || occurs(terms, needle, e, seen)
        }
        TermData::App(_, args) => args.iter().any(|&arg| occurs(terms, needle, arg, seen)),
        TermData::Let(bindings, b) => {
            bindings
                .iter()
                .any(|(_, v)| occurs(terms, needle, *v, seen))
                || occurs(terms, needle, b, seen)
        }
        TermData::Forall(_, b, _) | TermData::Exists(_, b, _) => occurs(terms, needle, b, seen),
        // A future `TermData` variant: conservatively assume `needle` occurs,
        // which blocks the elimination (fail-closed to the identity).
        _ => true,
    }
}

/// Does `t` contain any nested `Forall`/`Exists`/`Let` binder?
fn has_binder(terms: &TermStore, t: TermId, seen: &mut HashSet<TermId>) -> bool {
    if !seen.insert(t) {
        return false;
    }
    match terms.get(t).clone() {
        TermData::Const(_) | TermData::Var(_, _) => false,
        TermData::Forall(_, _, _) | TermData::Exists(_, _, _) | TermData::Let(_, _) => true,
        TermData::Not(i) => has_binder(terms, i, seen),
        TermData::Ite(c, th, e) => {
            has_binder(terms, c, seen) || has_binder(terms, th, seen) || has_binder(terms, e, seen)
        }
        TermData::App(_, args) => args.iter().any(|&arg| has_binder(terms, arg, seen)),
        // A future `TermData` variant: conservatively assume it binds, which
        // makes der fail-close to the identity on this assertion.
        _ => true,
    }
}

#[cfg(test)]
#[path = "der_tests.rs"]
mod tests;
