// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Distribute universal quantifiers over conjunction (z3's `distribute-forall`).
//!
//! - `(forall (x…) (and A B …))` becomes the conjuncts `(forall (x…) A)`,
//!   `(forall (x…) B)`, … — one goal formula per flattened conjunct.
//! - `(not (exists (x…) (or A B …)))` becomes `(not (exists (x…) A))`,
//!   `(not (exists (x…) B))`, … — the dual (∃ distributes over ∨).
//! - Anything else (in particular an `=>` body, which AY stores as `(or …)`,
//!   not `(and …)`) is left verbatim.
//!
//! z3 emits the split conjuncts/disjuncts in reversed/reordered order; AY emits
//! them in the term store's canonical order. That is a documented output-SHAPE
//! divergence only — the transform is equivalence-preserving either way.
//!
//! # Soundness
//!
//! EQUIVALENCE-PRESERVING: `∀x.(A ∧ B) ≡ (∀x.A) ∧ (∀x.B)` and, dually,
//! `¬∃x.(A ∨ B) ≡ ¬∃x.A ∧ ¬∃x.B`. Splitting one goal assertion into several
//! whose conjunction is the original preserves the model set exactly. No
//! substitution occurs — each new binder reuses the SAME bound variables and the
//! SAME body subterms — so there is no capture concern.
//!
//! # Scope
//!
//! Apply-surface only: a plain struct with an `apply` method, NOT a
//! [`super::PreprocessingPass`], so it never auto-enrolls in the solve pipeline.

use ay_core::term::{Symbol, TermData};
use ay_core::{TermId, TermStore};

/// The `distribute-forall` goal transform.
pub(crate) struct DistributeForall;

impl DistributeForall {
    pub(crate) fn new() -> Self {
        DistributeForall
    }

    /// Distribute every top-level `forall`-over-`and` (and `¬exists`-over-`or`)
    /// assertion into one assertion per conjunct/disjunct. Returns whether any
    /// assertion was split.
    pub(crate) fn apply(&mut self, terms: &mut TermStore, assertions: &mut Vec<TermId>) -> bool {
        let mut out: Vec<TermId> = Vec::with_capacity(assertions.len());
        let mut changed = false;
        for &a in assertions.iter() {
            if let Some(split) = distribute(terms, a) {
                changed = true;
                out.extend(split);
            } else {
                out.push(a);
            }
        }
        if changed {
            *assertions = out;
        }
        changed
    }
}

/// Split one assertion, or `None` if it is not a distributable shape.
fn distribute(terms: &mut TermStore, a: TermId) -> Option<Vec<TermId>> {
    match terms.get(a).clone() {
        TermData::Forall(vars, body, _triggers) => {
            let conjuncts = flatten_conn(terms, body, "and");
            if conjuncts.len() <= 1 {
                return None; // body is not a (multi-ary) `and`
            }
            Some(
                conjuncts
                    .into_iter()
                    .map(|c| terms.mk_forall(vars.clone(), c))
                    .collect(),
            )
        }
        TermData::Not(inner) => {
            let TermData::Exists(vars, body, _triggers) = terms.get(inner).clone() else {
                return None;
            };
            let disjuncts = flatten_conn(terms, body, "or");
            if disjuncts.len() <= 1 {
                return None; // body is not a (multi-ary) `or`
            }
            Some(
                disjuncts
                    .into_iter()
                    .map(|d| {
                        let ex = terms.mk_exists(vars.clone(), d);
                        terms.mk_not(ex)
                    })
                    .collect(),
            )
        }
        _ => None,
    }
}

/// Flatten a top-level `op` (`and`/`or`) node into its operands, recursing into
/// nested same-`op` nodes. A non-`op` term yields the single-element list `[t]`.
fn flatten_conn(terms: &TermStore, t: TermId, op: &str) -> Vec<TermId> {
    let mut out = Vec::new();
    flatten_into(terms, t, op, &mut out);
    out
}

fn flatten_into(terms: &TermStore, t: TermId, op: &str, out: &mut Vec<TermId>) {
    match terms.get(t) {
        TermData::App(Symbol::Named(n), args) if n == op => {
            let args = args.clone();
            for arg in args {
                flatten_into(terms, arg, op, out);
            }
        }
        _ => out.push(t),
    }
}

#[cfg(test)]
#[path = "distribute_forall_tests.rs"]
mod tests;
