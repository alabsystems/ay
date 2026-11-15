// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! NNF + Skolemization of the quantified assertions (z3's `nnf` with its
//! Skolemizer, `reference/z3/src/ast/normal_forms/nnf.cpp`).
//!
//! Delegates to [`crate::skolemize::skolemize_deep_with_provenance`], the walk
//! the quantifier loop already uses: negations are pushed through `and`/`or`/
//! `=>`/binders, positive existentials (and negated universals) become fresh
//! Skolem constants, or Skolem functions of the enclosing universals.
//!
//! Satisfiability-preserving, not equivalence-preserving: every minted Skolem
//! symbol is recorded as [`super::ConverterEntry::Fresh`]. A model of the
//! output restricted to the input signature is a model of the input.
//!
//! An assertion is rewritten only when the walk removes a quantifier node; a
//! walk that merely pushes a negation through a binder leaves it as authored.

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::term::TermData;
use ay_core::{TermId, TermStore};

use super::terms::{quantifier_count, tree_size_exceeds};
use super::{Justification, Pass, PassContext, Preservation};

/// The Skolemizing walk is not DAG-memoized; refuse assertions whose tree
/// expansion is larger than this (they keep their shape).
const MAX_TREE_SIZE: u64 = 200_000;

pub(super) struct NnfSkolem;

impl Pass for NnfSkolem {
    fn name(&self) -> &'static str {
        "nnf-skolem"
    }

    fn preservation(&self) -> Preservation {
        Preservation::SatisfiabilityWithConverter
    }

    fn justification(&self) -> Justification {
        Justification::Unjustified
    }

    fn run(&mut self, cx: &mut PassContext<'_, '_>) -> usize {
        let mut rewritten = 0;
        for index in 0..cx.window.len() {
            if !cx.budget.tick() {
                break;
            }
            let assertion = cx.window[index];
            if !crate::ematching::contains_quantifier(cx.terms, assertion)
                || tree_size_exceeds(cx.terms, assertion, MAX_TREE_SIZE)
            {
                continue;
            }
            let before = skolem_symbols(cx.terms, assertion);
            let (result, _provenance) =
                crate::skolemize::skolemize_deep_with_provenance(cx.terms, assertion, true);
            let Some(new) = result else {
                continue;
            };
            // Adopt the walk only where it eliminated a quantifier. A pure
            // polarity push (`¬∃x. φ` to `∀x. ¬φ`) decides nothing by itself,
            // and the quantifier loop performs the same walk later anyway.
            if quantifier_count(cx.terms, new) >= quantifier_count(cx.terms, assertion) {
                continue;
            }
            let minted: Vec<String> = skolem_symbols(cx.terms, new)
                .into_iter()
                .filter(|name| !before.contains(name))
                .collect();
            for name in minted {
                cx.converter.fresh(name);
            }
            cx.window[index] = new;
            rewritten += 1;
        }
        rewritten
    }
}

/// The Skolem-registry symbols (constants and function heads) under `t`.
fn skolem_symbols(terms: &TermStore, t: TermId) -> Vec<String> {
    let mut out: Vec<String> = Vec::new();
    let mut seen: HashSet<TermId> = HashSet::default();
    let mut stack = vec![t];
    while let Some(cur) = stack.pop() {
        if !seen.insert(cur) {
            continue;
        }
        match terms.get(cur) {
            TermData::Var(name, _) => {
                if terms.is_skolem_symbol(name) && !out.contains(name) {
                    out.push(name.clone());
                }
            }
            TermData::App(sym, args) => {
                if terms.is_skolem_symbol(sym.name()) && !out.iter().any(|n| n == sym.name()) {
                    out.push(sym.name().to_string());
                }
                stack.extend(args.iter().copied());
            }
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, a, b) => stack.extend([*c, *a, *b]),
            TermData::Let(bindings, body) => {
                stack.extend(bindings.iter().map(|(_, v)| *v));
                stack.push(*body);
            }
            TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => stack.push(*body),
            _ => {}
        }
    }
    out
}
