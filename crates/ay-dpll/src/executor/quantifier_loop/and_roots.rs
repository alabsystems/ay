// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The conjunct view of an asserted root vector for the quantified SAT
//! certificate partitions.
//!
//! An asserted `(and A B C)` is, semantically, the three assertions `A`, `B`,
//! `C`: a structure satisfies the root iff it satisfies every conjunct (Alethe
//! justifies the split with the `and` rule). The certificate producers
//! partition their snapshot into top-level `forall`s and quantifier-free
//! ground conjuncts, and used to decline outright on a root like
//! `(and (forall ((g Real)) φ) (>= h b))` — measured on LOIS (SMT-LIB LRA),
//! where 26 single-query conversions sat behind exactly this refusal.
//!
//! # What this view changes, and what it must not
//!
//! It changes ONLY which terms a producer discharges: a root that is an `and`
//! node containing a quantifier is replaced by its (transitively flattened)
//! leaf conjuncts. A producer that certifies every leaf of every root has
//! certified every root, so the certified statement — "this interpretation
//! satisfies every snapshot assertion" — is unchanged in strength.
//!
//! It must NOT change which roots the resulting authority is BOUND to. Every
//! caller keeps the authored, ordered root vector as the identity it installs
//! its witness state for and that the independent gate re-authenticates
//! (`QuantifiedModelCheckScope` / `QuantifiedModelConfirmation` and the
//! per-certificate `is_installed_current_for` checks compare that exact vector
//! and its entry stamps). The independent gate already walks the same
//! conjunct structure (`collect_and_conjuncts`) when it separates quantified
//! leaves from the ground siblings it still evaluates itself.
//!
//! # Strictly additive
//!
//! A root that is not an `and`, or an `and` with no quantifier anywhere below
//! it, is passed through unchanged and in place. Every snapshot every
//! producer admitted before therefore yields an identical partition; only
//! snapshots every producer used to decline can reach a different one.

use ay_core::{Symbol, TermData, TermId, TermStore};

use crate::ematching::contains_quantifier;

/// True when `term` is an `(and …)` application.
fn is_and_node(terms: &TermStore, term: TermId) -> bool {
    matches!(terms.get(term), TermData::App(Symbol::Named(name), _) if name == "and")
}

/// The certificate-partition view of `roots`; see the module docs.
///
/// Each root that is an `and` node containing a quantifier contributes its
/// leaf conjuncts (nested `and`s flattened, in left-to-right order); every
/// other root contributes itself. The walk is iterative, so a deep `and`
/// spine cannot overflow the stack.
pub(in crate::executor) fn flatten_quantified_and_roots(
    terms: &TermStore,
    roots: &[TermId],
) -> Vec<TermId> {
    let mut out = Vec::with_capacity(roots.len());
    for &root in roots {
        if !is_and_node(terms, root) || !contains_quantifier(terms, root) {
            out.push(root);
            continue;
        }
        // Depth-first, left-to-right: push children in reverse.
        let mut stack = vec![root];
        while let Some(term) = stack.pop() {
            match terms.get(term) {
                TermData::App(Symbol::Named(name), args) if name == "and" => {
                    stack.extend(args.iter().rev().copied());
                }
                _ => out.push(term),
            }
        }
    }
    out
}

/// True when the conjunct view of `roots` has the shape every quantified SAT
/// certificate partitions: at least one top-level `forall` leaf, and every
/// other leaf quantifier-free. The exact-public-root rescue asks this before
/// it runs the certificate producers on the authored roots.
pub(in crate::executor) fn roots_match_certificate_partition(
    terms: &TermStore,
    roots: &[TermId],
) -> bool {
    let mut has_top_level_forall = false;
    flatten_quantified_and_roots(terms, roots)
        .into_iter()
        .all(|leaf| {
            if matches!(terms.get(leaf), TermData::Forall(..)) {
                has_top_level_forall = true;
                true
            } else {
                !contains_quantifier(terms, leaf)
            }
        })
        && has_top_level_forall
}

#[cfg(test)]
#[path = "and_roots_tests.rs"]
mod tests;
