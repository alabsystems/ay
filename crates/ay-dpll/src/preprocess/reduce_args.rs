// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Eliminate always-constant function arguments (z3's `reduce-args` tactic).
//!
//! For an uninterpreted function `f`, a positional argument is *droppable* iff
//! EVERY occurrence of `f` in the goal supplies a literal constant there. The
//! droppable positions form a mask; the surviving occurrences are then grouped
//! by the tuple of constants at the masked positions and each distinct tuple
//! `c̄` gets a fresh specialized symbol `f!k` standing for `λȳ. f(c̄, ȳ)` (with
//! `c̄`/`ȳ` interleaved at the original positions). When every position is
//! masked the specialization is a 0-ary constant `f!0`.
//!
//! Examples (measured against z3 4.15.4):
//! - `(f 1 x)`, `(f 1 5)` → `(f!0 x)`, `(f!0 5)` (position 0 always `1`).
//! - `(f 1 x)`, `(f 2 5)` → `(f!0 x)`, `(f!1 5)` (distinct constant tuples).
//! - `(p x true)`, `(p 3 true)` → `(p!0 x)`, `(p!0 3)` (predicates too).
//! - `(f 1)` (arity 1, always `1`) → the 0-ary constant `f!0`.
//!
//! # Soundness
//!
//! EQUISATISFIABLE (like Tseitin): the `f!k` are fresh symbols. Every model `M`
//! of the original extends to a model of the transformed goal by defining
//! `f!k(ȳ) := f(c̄_k, ȳ)`; conversely any model of the transformed goal, read
//! back through that definition, satisfies the original. Verdicts carry over in
//! both directions. Because a masked position holds a literal constant in EVERY
//! occurrence, a bound variable (which is never a `Const`) can never sit at a
//! masked position, so specialization never moves a term across a binder — no
//! capture. The occurrence-collection walk and the rewrite walk visit the
//! IDENTICAL node set (App args, `not`, `ite`, `let` values+body, quantifier
//! bodies), so the mask can neither miss an occurrence the rewrite specializes
//! nor vice versa.
//!
//! Fresh names are collision-scanned against every symbol name in the goal AND
//! the term store's interned-name table, so an `f!0` a user already declared can
//! never be aliased (which would be unsound in the 0-ary case, where the
//! specialization is minted via [`TermStore::mk_var`], interned by name).
//!
//! Any quantifier whose body is specialized is rebuilt WITHOUT its `:pattern`
//! triggers (they may reference the pre-specialization symbol; triggers are
//! instantiation hints, so dropping them is sound).
//!
//! # Scope
//!
//! Apply-surface only: a plain struct with an `apply` method, NOT a
//! [`super::PreprocessingPass`], so it never auto-enrolls in the solve pipeline
//! (which would otherwise let `get-model` emit `f!k` — an invalid output).

use ay_core::kani_compat::{det_hash_map_new, det_hash_set_new, DetHashMap, DetHashSet};
use ay_core::term::{Symbol, TermData};
use ay_core::{TermId, TermStore};

/// The `reduce-args` goal transform.
pub(crate) struct ReduceArgs;

/// Per-function aggregate gathered in the collection pass.
struct FnInfo {
    arity: usize,
    /// `all_const[p]` stays true while every seen occurrence supplies a literal
    /// constant at position `p`.
    all_const: Vec<bool>,
    /// Cleared if occurrences disagree on arity (well-typed goals never do).
    consistent: bool,
}

impl ReduceArgs {
    pub(crate) fn new() -> Self {
        ReduceArgs
    }

    pub(crate) fn apply(&mut self, terms: &mut TermStore, assertions: &mut [TermId]) -> bool {
        // Pass 1: collect per-function const-argument profiles + every symbol name.
        let mut info: DetHashMap<String, FnInfo> = det_hash_map_new();
        let mut used_names: DetHashSet<String> = det_hash_set_new();
        let mut seen = det_hash_set_new();
        // Poisoned if collection meets a `TermData` variant it cannot traverse
        // (a future addition): reducing then risks an asymmetric collect/rewrite,
        // so refuse the whole pass — the sound identity.
        let mut bail = false;
        for &a in assertions.iter() {
            collect(terms, a, &mut info, &mut used_names, &mut seen, &mut bail);
        }
        if bail {
            return false;
        }

        // Pass 2: masks (positions const in EVERY occurrence). Skip functions with
        // an empty mask or inconsistent arity.
        let mut masks: DetHashMap<String, Vec<usize>> = det_hash_map_new();
        for (f, fi) in &info {
            if !fi.consistent || fi.arity == 0 {
                continue;
            }
            let mask: Vec<usize> = (0..fi.arity).filter(|&p| fi.all_const[p]).collect();
            if !mask.is_empty() {
                masks.insert(f.clone(), mask);
            }
        }
        if masks.is_empty() {
            return false;
        }

        // Pass 3: assign fresh `f!k` names by first-seen constant tuple.
        let mut names: DetHashMap<(String, Vec<TermId>), String> = det_hash_map_new();
        let mut counters: DetHashMap<String, usize> = det_hash_map_new();
        let mut seen2 = det_hash_set_new();
        for &a in assertions.iter() {
            assign(
                terms,
                a,
                &masks,
                &used_names,
                &mut names,
                &mut counters,
                &mut seen2,
            );
        }

        // Pass 4: rewrite.
        let mut cache: DetHashMap<TermId, TermId> = det_hash_map_new();
        let mut changed = false;
        for a in assertions.iter_mut() {
            let new = rewrite(terms, *a, &masks, &names, &mut cache);
            if new != *a {
                *a = new;
                changed = true;
            }
        }
        changed
    }
}

fn is_const(terms: &TermStore, t: TermId) -> bool {
    matches!(terms.get(t), TermData::Const(_))
}

/// Pass 1 traversal.
fn collect(
    terms: &TermStore,
    t: TermId,
    info: &mut DetHashMap<String, FnInfo>,
    used_names: &mut DetHashSet<String>,
    seen: &mut DetHashSet<TermId>,
    bail: &mut bool,
) {
    if *bail || !seen.insert(t) {
        return;
    }
    match terms.get(t).clone() {
        TermData::Const(_) => {}
        TermData::Var(name, _) => {
            used_names.insert(name);
        }
        TermData::Not(i) => collect(terms, i, info, used_names, seen, bail),
        TermData::Ite(c, th, e) => {
            collect(terms, c, info, used_names, seen, bail);
            collect(terms, th, info, used_names, seen, bail);
            collect(terms, e, info, used_names, seen, bail);
        }
        TermData::App(sym, args) => {
            used_names.insert(sym.name().to_string());
            if let Symbol::Named(name) = &sym {
                if !args.is_empty() && !is_known_operator(name) {
                    let entry = info.entry(name.clone()).or_insert_with(|| FnInfo {
                        arity: args.len(),
                        all_const: vec![true; args.len()],
                        consistent: true,
                    });
                    if entry.arity != args.len() {
                        entry.consistent = false;
                    } else {
                        for (p, &arg) in args.iter().enumerate() {
                            if !is_const(terms, arg) {
                                entry.all_const[p] = false;
                            }
                        }
                    }
                }
            }
            for arg in args {
                collect(terms, arg, info, used_names, seen, bail);
            }
        }
        TermData::Let(bindings, body) => {
            for (_, v) in &bindings {
                collect(terms, *v, info, used_names, seen, bail);
            }
            collect(terms, body, info, used_names, seen, bail);
        }
        TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => {
            collect(terms, body, info, used_names, seen, bail);
        }
        // A future `TermData` variant collection cannot descend into: poison the
        // pass so it makes no change (sound identity).
        _ => *bail = true,
    }
}

/// Pass 3 traversal: mint `f!k` names in first-seen constant-tuple order.
#[allow(clippy::too_many_arguments)]
fn assign(
    terms: &TermStore,
    t: TermId,
    masks: &DetHashMap<String, Vec<usize>>,
    used_names: &DetHashSet<String>,
    names: &mut DetHashMap<(String, Vec<TermId>), String>,
    counters: &mut DetHashMap<String, usize>,
    seen: &mut DetHashSet<TermId>,
) {
    if !seen.insert(t) {
        return;
    }
    match terms.get(t).clone() {
        TermData::Const(_) | TermData::Var(_, _) => {}
        TermData::Not(i) => assign(terms, i, masks, used_names, names, counters, seen),
        TermData::Ite(c, th, e) => {
            assign(terms, c, masks, used_names, names, counters, seen);
            assign(terms, th, masks, used_names, names, counters, seen);
            assign(terms, e, masks, used_names, names, counters, seen);
        }
        TermData::App(sym, args) => {
            if let Symbol::Named(name) = &sym {
                if let Some(mask) = masks.get(name) {
                    let tuple: Vec<TermId> = mask.iter().map(|&p| args[p]).collect();
                    let key = (name.clone(), tuple);
                    if !names.contains_key(&key) {
                        let fresh = fresh_name(name, counters, used_names, terms);
                        names.insert(key, fresh);
                    }
                }
            }
            for arg in args {
                assign(terms, arg, masks, used_names, names, counters, seen);
            }
        }
        TermData::Let(bindings, body) => {
            for (_, v) in &bindings {
                assign(terms, *v, masks, used_names, names, counters, seen);
            }
            assign(terms, body, masks, used_names, names, counters, seen);
        }
        TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => {
            assign(terms, body, masks, used_names, names, counters, seen);
        }
        // Unreachable once `masks` is non-empty (collection traversed the whole
        // goal without poisoning), but required for exhaustiveness.
        _ => {}
    }
}

/// Next `base!k` not colliding with any goal symbol name or interned name.
fn fresh_name(
    base: &str,
    counters: &mut DetHashMap<String, usize>,
    used_names: &DetHashSet<String>,
    terms: &TermStore,
) -> String {
    let k = counters.entry(base.to_string()).or_insert(0);
    loop {
        let candidate = format!("{base}!{k}");
        *k += 1;
        if !used_names.contains(&candidate) && !terms.has_var_name(&candidate) {
            return candidate;
        }
    }
}

/// Pass 4: rewrite each reducible application to its specialized symbol.
fn rewrite(
    terms: &mut TermStore,
    t: TermId,
    masks: &DetHashMap<String, Vec<usize>>,
    names: &DetHashMap<(String, Vec<TermId>), String>,
    cache: &mut DetHashMap<TermId, TermId>,
) -> TermId {
    if let Some(&c) = cache.get(&t) {
        return c;
    }
    let result = match terms.get(t).clone() {
        TermData::Const(_) | TermData::Var(_, _) => t,
        TermData::Not(i) => {
            let ni = rewrite(terms, i, masks, names, cache);
            if ni == i {
                t
            } else {
                terms.mk_not(ni)
            }
        }
        TermData::Ite(c, th, e) => {
            let nc = rewrite(terms, c, masks, names, cache);
            let nt = rewrite(terms, th, masks, names, cache);
            let ne = rewrite(terms, e, masks, names, cache);
            if nc == c && nt == th && ne == e {
                t
            } else {
                terms.mk_ite(nc, nt, ne)
            }
        }
        TermData::App(sym, args) => {
            let reducible_mask = match &sym {
                Symbol::Named(name) => masks.get(name).map(|m| (name.clone(), m.clone())),
                _ => None,
            };
            if let Some((name, mask)) = reducible_mask {
                let tuple: Vec<TermId> = mask.iter().map(|&p| args[p]).collect();
                let new_name = names
                    .get(&(name, tuple))
                    .cloned()
                    .expect("every reducible occurrence is named in pass 3");
                let mut kept = Vec::new();
                for (p, &arg) in args.iter().enumerate() {
                    if !mask.contains(&p) {
                        kept.push(rewrite(terms, arg, masks, names, cache));
                    }
                }
                let ret_sort = terms.sort(t).clone();
                if kept.is_empty() {
                    terms.mk_var(new_name, ret_sort)
                } else {
                    terms.mk_app(Symbol::Named(new_name), kept, ret_sort)
                }
            } else {
                let new_args: Vec<TermId> = args
                    .iter()
                    .map(|&x| rewrite(terms, x, masks, names, cache))
                    .collect();
                if new_args == args {
                    t
                } else {
                    terms.rebuild_app(&sym, new_args, t)
                }
            }
        }
        TermData::Let(bindings, body) => {
            let mut changed = false;
            let new_bindings: Vec<(String, TermId)> = bindings
                .iter()
                .map(|(n, v)| {
                    let nv = rewrite(terms, *v, masks, names, cache);
                    changed |= nv != *v;
                    (n.clone(), nv)
                })
                .collect();
            let nb = rewrite(terms, body, masks, names, cache);
            changed |= nb != body;
            if changed {
                terms.mk_let(new_bindings, nb)
            } else {
                t
            }
        }
        TermData::Forall(vars, body, _triggers) => {
            let nb = rewrite(terms, body, masks, names, cache);
            if nb == body {
                t
            } else {
                terms.mk_forall(vars, nb)
            }
        }
        TermData::Exists(vars, body, _triggers) => {
            let nb = rewrite(terms, body, masks, names, cache);
            if nb == body {
                t
            } else {
                terms.mk_exists(vars, nb)
            }
        }
        // Unreachable once `masks` is non-empty (see `assign`); leave untouched.
        _ => t,
    };
    cache.insert(t, result);
    result
}

/// Recognized core/Boolean/arithmetic/bit-vector/array operator names — a local
/// mirror of the identically-named helper in `api::solving::tactics`. Anything
/// else applied to ≥1 argument is treated as an uninterpreted function.
fn is_known_operator(name: &str) -> bool {
    matches!(
        name,
        // Core / Boolean / equality.
        "true" | "false" | "and" | "or" | "not" | "=>" | "implies" | "xor"
            | "iff" | "<=>" | "=" | "distinct" | "ite"
        // Linear/nonlinear arithmetic.
            | "+" | "-" | "*" | "/" | "div" | "mod" | "rem" | "abs"
            | "<" | "<=" | ">" | ">=" | "^" | "power"
            | "to_real" | "to_int" | "is_int" | "divisible"
        // Arrays.
            | "select" | "store" | "map" | "const"
        // Bit-vectors.
            | "bvadd" | "bvsub" | "bvmul" | "bvudiv" | "bvurem" | "bvsdiv"
            | "bvsrem" | "bvsmod" | "bvand" | "bvor" | "bvxor" | "bvnand"
            | "bvnor" | "bvxnor" | "bvnot" | "bvneg" | "bvshl" | "bvlshr"
            | "bvashr" | "bvult" | "bvule" | "bvugt" | "bvuge" | "bvslt"
            | "bvsle" | "bvsgt" | "bvsge" | "bvcomp" | "concat" | "bv2int"
            | "bv2nat" | "int2bv" | "nat2bv"
    )
}

#[cfg(test)]
#[path = "reduce_args_tests.rs"]
mod tests;
