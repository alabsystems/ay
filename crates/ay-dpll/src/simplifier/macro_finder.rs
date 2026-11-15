// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Macro finder (z3's `macro_finder`, `reference/z3/src/ast/macros/`).
//!
//! A top-level universal that DEFINES an uninterpreted function,
//!
//! ```text
//! (forall (x₁ … xₙ) (= (f x_π(1) … x_π(n)) t))      f ∉ t, x distinct
//! (forall (x₁ … xₙ) (p x_π(1) … x_π(n)))              p := true
//! (forall (x₁ … xₙ) (not (p x_π(1) … x_π(n))))        p := false
//! ```
//!
//! is removed from the window, and every application `f(s̄)` elsewhere
//! (including inside quantifier bodies) is replaced by `t[x̄ := s̄]`. The body
//! `t` must be quantifier-free, so an expansion never nests a binder.
//!
//! # Soundness
//!
//! Satisfiability-preserving with a model converter. Write `Γ` for the other
//! assertions and `Def` for the definition. Any model of `Γ ∧ Def` interprets
//! `f` as `λx̄.t`, so it satisfies the expanded `Γ[f := λx̄.t]`. Conversely, `f`
//! does not occur in the expanded window (checked after expansion; any
//! surviving occurrence abandons the macro), so a model of it extended with
//! `f := λx̄.t` — the recorded [`super::ConverterEntry::Define`] — satisfies
//! `Def` trivially and `Γ` by construction.
//!
//! Capture: `t`'s free names other than the parameters must not be bound by
//! any binder in the window (they would be captured at an expansion site under
//! that binder); otherwise the macro is abandoned. Parameters are replaced
//! with [`crate::ematching::subst_vars`], which renames `t`'s own binders when
//! an argument would be captured by them.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Symbol, TermData};
use ay_core::{Sort, TermId, TermStore};

use super::fold::rebuild_app;
use super::terms::{
    as_binary_eq, as_quantifier, free_names, mentions_head, rebuild_quantifier, Binder,
};
use super::{Justification, Pass, PassContext, Preservation, WorkBudget};

pub(super) struct MacroFinder;

/// One recognized definition.
struct Macro {
    head: String,
    params: Vec<(String, Sort)>,
    body: TermId,
}

impl Pass for MacroFinder {
    fn name(&self) -> &'static str {
        "macro-finder"
    }

    fn preservation(&self) -> Preservation {
        Preservation::SatisfiabilityWithConverter
    }

    fn justification(&self) -> Justification {
        Justification::Unjustified
    }

    fn run(&mut self, cx: &mut PassContext<'_, '_>) -> usize {
        let mut found = 0;
        let mut index = 0;
        while index < cx.window.len() {
            if !cx.budget.tick() {
                break;
            }
            let Some(m) = recognize(cx.terms, cx.window[index], cx.symbols) else {
                index += 1;
                continue;
            };
            if let Some((window, converter)) = try_eliminate(cx, index, &m) {
                *cx.window = window;
                *cx.converter = converter;
                cx.converter.define(m.head, m.params, m.body);
                found += 1;
                // The slot now holds the next assertion; do not advance.
            } else {
                index += 1;
            }
        }
        found
    }
}

/// Recognize a macro definition at the top of `assertion`.
fn recognize(
    terms: &TermStore,
    assertion: TermId,
    symbols: &dyn Fn(&str, usize) -> bool,
) -> Option<Macro> {
    let q = as_quantifier(terms, assertion)?;
    if q.binder != Binder::Forall || q.vars.is_empty() {
        return None;
    }
    let mut names: HashSet<&str> = HashSet::default();
    if !q.vars.iter().all(|(n, _)| names.insert(n.as_str())) {
        return None;
    }
    let candidates: Vec<(TermId, TermId)> = if let Some((l, r)) = as_binary_eq(terms, q.body) {
        vec![(l, r), (r, l)]
    } else {
        let (atom, value) = match terms.get(q.body) {
            TermData::Not(inner) => (*inner, false),
            _ => (q.body, true),
        };
        let value = if value {
            terms.true_term()
        } else {
            terms.false_term()
        };
        vec![(atom, value)]
    };
    for (head_side, def_side) in candidates {
        let TermData::App(sym, args) = terms.get(head_side) else {
            continue;
        };
        if !matches!(sym, Symbol::Named(_)) {
            continue;
        }
        let head = sym.name().to_string();
        if args.len() != q.vars.len() || !symbols(&head, args.len()) {
            continue;
        }
        // Arguments: the bound variables, each exactly once.
        let mut params: Vec<(String, Sort)> = Vec::with_capacity(args.len());
        let mut used: HashSet<&str> = HashSet::default();
        let all_vars = args.iter().all(|&arg| match terms.get(arg) {
            TermData::Var(name, _) => match q.vars.iter().find(|(n, _)| n == name) {
                Some((n, sort)) if used.insert(n.as_str()) && terms.sort(arg) == sort => {
                    params.push((n.clone(), sort.clone()));
                    true
                }
                _ => false,
            },
            _ => false,
        });
        if !all_vars || mentions_head(terms, def_side, &head) {
            continue;
        }
        // Only quantifier-free bodies: inlining a quantified definition at
        // every use would nest binders inside other quantifier bodies (and
        // under negation, alternations) where instantiation-based engines
        // handle the named predicate better than its expansion.
        if crate::ematching::contains_quantifier(terms, def_side) {
            continue;
        }
        if terms.sort(def_side) != terms.sort(head_side) {
            continue;
        }
        return Some(Macro {
            head,
            params,
            body: def_side,
        });
    }
    None
}

/// Expand `m` everywhere except its defining slot. Returns the new window and
/// converter, or `None` when the macro must be abandoned.
fn try_eliminate(
    cx: &mut PassContext<'_, '_>,
    index: usize,
    m: &Macro,
) -> Option<(Vec<TermId>, super::ModelConverter)> {
    // Capture guard: the body's free names beyond the parameters must not be
    // bound anywhere in the window.
    let free = free_names(cx.terms, m.body)?;
    let param_names: HashSet<&str> = m.params.iter().map(|(n, _)| n.as_str()).collect();
    let body_free: HashSet<String> = free
        .into_iter()
        .filter(|n| !param_names.contains(n.as_str()))
        .collect();
    let mut binders: HashSet<String> = HashSet::default();
    for &assertion in cx.window.iter() {
        collect_binder_names(cx.terms, assertion, &mut binders);
    }
    if body_free.iter().any(|n| binders.contains(n)) {
        return None;
    }

    let mut cache: HashMap<TermId, TermId> = HashMap::default();
    let mut window = Vec::with_capacity(cx.window.len().saturating_sub(1));
    for (i, &assertion) in cx.window.iter().enumerate() {
        if i == index {
            continue;
        }
        let expanded = expand(cx.terms, assertion, m, &mut cache, cx.budget)?;
        if mentions_head(cx.terms, expanded, &m.head) {
            return None;
        }
        window.push(expanded);
    }
    let mut converter = cx.converter.clone();
    let terms = &mut *cx.terms;
    let budget = &mut *cx.budget;
    let ok = converter.expand_bodies(|body| {
        let new = expand(terms, body, m, &mut cache, budget)?;
        (!mentions_head(terms, new, &m.head)).then_some(new)
    });
    ok.then_some((window, converter))
}

/// Replace every `head(s̄)` under `t` by the macro body instantiated at `s̄`.
fn expand(
    terms: &mut TermStore,
    t: TermId,
    m: &Macro,
    cache: &mut HashMap<TermId, TermId>,
    budget: &mut WorkBudget<'_>,
) -> Option<TermId> {
    if let Some(&done) = cache.get(&t) {
        return Some(done);
    }
    if !budget.tick() {
        return None;
    }
    let result = stacker::maybe_grow(32 * 1024, 1024 * 1024, || -> Option<TermId> {
        Some(match terms.get(t).clone() {
            TermData::Const(_) => t,
            // A nullary use of the head's spelling cannot be expanded.
            TermData::Var(name, _) => {
                if name == m.head {
                    return None;
                }
                t
            }
            TermData::App(sym, args) => {
                let mut new_args = Vec::with_capacity(args.len());
                for &arg in &args {
                    new_args.push(expand(terms, arg, m, cache, budget)?);
                }
                if sym.name() == m.head {
                    if !matches!(sym, Symbol::Named(_)) || new_args.len() != m.params.len() {
                        return None;
                    }
                    let subst: HashMap<String, TermId> = m
                        .params
                        .iter()
                        .map(|(n, _)| n.clone())
                        .zip(new_args.iter().copied())
                        .collect();
                    crate::ematching::subst_vars(terms, m.body, &subst)
                } else if new_args == args {
                    t
                } else {
                    rebuild_app(terms, &sym, new_args, t)
                }
            }
            TermData::Not(inner) => {
                let ni = expand(terms, inner, m, cache, budget)?;
                if ni == inner {
                    t
                } else {
                    terms.mk_not(ni)
                }
            }
            TermData::Ite(c, a, b) => {
                let nc = expand(terms, c, m, cache, budget)?;
                let na = expand(terms, a, m, cache, budget)?;
                let nb = expand(terms, b, m, cache, budget)?;
                if (nc, na, nb) == (c, a, b) {
                    t
                } else {
                    terms.mk_ite(nc, na, nb)
                }
            }
            TermData::Let(..) => {
                if mentions_head(terms, t, &m.head) {
                    return None;
                }
                t
            }
            TermData::Forall(..) | TermData::Exists(..) => {
                let q = as_quantifier(terms, t)?;
                let nb = expand(terms, q.body, m, cache, budget)?;
                // Patterns over the eliminated head no longer match anything.
                let triggers: Vec<Vec<TermId>> = q
                    .triggers
                    .iter()
                    .filter(|group| !group.iter().any(|&p| mentions_head(terms, p, &m.head)))
                    .cloned()
                    .collect();
                if nb == q.body && triggers == q.triggers {
                    t
                } else {
                    rebuild_quantifier(terms, t, q.binder, q.vars, nb, triggers)
                }
            }
            _ => return None,
        })
    })?;
    cache.insert(t, result);
    Some(result)
}

/// Every binder name (quantifier variables and let names) under `t`.
fn collect_binder_names(terms: &TermStore, t: TermId, out: &mut HashSet<String>) {
    let mut seen: HashSet<TermId> = HashSet::default();
    let mut stack = vec![t];
    while let Some(cur) = stack.pop() {
        if !seen.insert(cur) {
            continue;
        }
        match terms.get(cur) {
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, a, b) => stack.extend([*c, *a, *b]),
            TermData::Let(bindings, body) => {
                for (name, value) in bindings {
                    out.insert(name.clone());
                    stack.push(*value);
                }
                stack.push(*body);
            }
            TermData::Forall(vars, body, triggers) | TermData::Exists(vars, body, triggers) => {
                out.extend(vars.iter().map(|(n, _)| n.clone()));
                stack.push(*body);
                for group in triggers {
                    stack.extend(group.iter().copied());
                }
            }
            _ => {}
        }
    }
}
