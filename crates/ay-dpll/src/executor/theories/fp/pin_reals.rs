// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tier A: pin symbolic `Real` variables to a value asserted by a top-level
//! equality, so a `((_ to_fp eb sb) rm <real-var>)` whose argument was symbolic
//! becomes ground and the standard `to_fp` constant-fold path can decide it.
//!
//! **Soundness — UNSAT only.** When the formula contains a top-level conjunct
//! `(= r c)` with `r` a `Real` variable and `c` a ground rational, then under
//! that conjunct the whole conjunction is equivalent to the one with every
//! occurrence of `r` replaced by `c`:  φ ∧ (r = c)  ⇔  φ[r:=c] ∧ (c = c).
//! Hence `φ[r:=c]` UNSAT ⟹ the original (which *includes* `r = c` as one of its
//! assertions) is UNSAT — sound in the unsat direction.
//!
//! The caller trusts ONLY the unsat verdict from the pinned formula. It does
//! **not** emit a model: after substitution `r` no longer occurs, so the FP
//! model layer would fill it with a default (e.g. `0.0`) that need not satisfy
//! the original `(= r c)` — a falsifying model. Producing a real witness needs
//! full FP+LRA model integration (out of scope), so SAT/unknown on the pinned
//! formula fail-close to `unknown`, exactly as before Tier A.
//!
//! Shadowing note: `=` is a core theory symbol and is not user-declarable, and
//! the operands are matched by CORE SORT (`Sort::Real` `Var` vs. ground
//! rational), never by a user-shadowable name — a declared UF cannot be routed
//! through this substitution.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::{Symbol, TermData};
use ay_core::{Sort, TermId, TermStore};

use super::support::is_ground_rational;

/// Build a `{Real Var TermId -> ground-rational TermId}` pin map from the
/// top-level positive equalities among the assertions. First-wins on a repeated
/// variable (a conflicting second pin turns into a `(= c1 c2)` literal that
/// stays visible to the solver, preserving unsat).
fn build_pin_map(terms: &TermStore, assertions: &[TermId]) -> HashMap<TermId, TermId> {
    let mut map: HashMap<TermId, TermId> = HashMap::default();
    for &a in assertions {
        if let TermData::App(Symbol::Named(name), args) = terms.get(a) {
            if name != "=" || args.len() != 2 {
                continue;
            }
            let (l, r) = (args[0], args[1]);
            // Match by core sort/kind: one side a Real Var, the other a ground
            // rational expression. Never by a user-shadowable name.
            for (var_side, val_side) in [(l, r), (r, l)] {
                if matches!(terms.get(var_side), TermData::Var(_, _))
                    && matches!(terms.sort(var_side), Sort::Real)
                    && is_ground_rational(terms, val_side)
                {
                    map.entry(var_side).or_insert(val_side);
                }
            }
        }
    }
    map
}

fn rewrite(
    terms: &mut TermStore,
    term: TermId,
    map: &HashMap<TermId, TermId>,
    cache: &mut HashMap<TermId, TermId>,
) -> TermId {
    if let Some(&c) = map.get(&term) {
        return c;
    }
    if let Some(&cached) = cache.get(&term) {
        return cached;
    }
    let data = terms.get(term).clone();
    let sort = terms.sort(term).clone();
    let result = match data {
        TermData::Const(_) | TermData::Var(_, _) => term,
        TermData::Not(inner) => {
            let ni = rewrite(terms, inner, map, cache);
            if ni == inner {
                term
            } else {
                terms.mk_not(ni)
            }
        }
        TermData::Ite(cnd, t, e) => {
            let nc = rewrite(terms, cnd, map, cache);
            let nt = rewrite(terms, t, map, cache);
            let ne = rewrite(terms, e, map, cache);
            if nc == cnd && nt == t && ne == e {
                term
            } else {
                terms.mk_ite(nc, nt, ne)
            }
        }
        TermData::App(sym, args) => {
            let new_args: Vec<TermId> = args
                .iter()
                .map(|&a| rewrite(terms, a, map, cache))
                .collect();
            if new_args == args {
                term
            } else {
                terms.mk_app(sym, new_args, sort)
            }
        }
        TermData::Let(bindings, body) => {
            let new_bindings: Vec<_> = bindings
                .iter()
                .map(|(n, v)| (n.clone(), rewrite(terms, *v, map, cache)))
                .collect();
            let nb = rewrite(terms, body, map, cache);
            if nb == body && new_bindings == bindings {
                term
            } else {
                terms.mk_let(new_bindings, nb)
            }
        }
        // Do not descend into binders: the pinned vars are free Real consts, not
        // bound; substituting under a binder that shadows the name is unsound.
        // (Pins target top-level declared consts by TermId, which never appear
        // as bound variables, but skipping is the conservative choice.)
        TermData::Forall(..) | TermData::Exists(..) => term,
        _ => term,
    };
    cache.insert(term, result);
    result
}

/// If any Real variable is pinned by a top-level equality, return the assertion
/// list with every pinned variable substituted by its value. Returns `None`
/// when there is nothing to pin or the substitution changes nothing (guarantees
/// the caller cannot loop: after substitution the pinned `Var` TermIds no longer
/// occur, so a second call finds an empty pin map).
pub(super) fn pin_real_assertions(
    terms: &mut TermStore,
    assertions: &[TermId],
) -> Option<Vec<TermId>> {
    let map = build_pin_map(terms, assertions);
    if map.is_empty() {
        return None;
    }
    let mut cache: HashMap<TermId, TermId> = HashMap::default();
    let pinned: Vec<TermId> = assertions
        .iter()
        .map(|&a| rewrite(terms, a, &map, &mut cache))
        .collect();
    if pinned == assertions {
        None
    } else {
        Some(pinned)
    }
}
