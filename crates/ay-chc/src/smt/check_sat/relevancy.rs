// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Don't-care relevancy filtering for the DPLL(T) theory loop (Phase 3 Fix 1).
//!
//! The theory loop historically asserted EVERY theory atom from the Tseitin
//! SAT model to the arithmetic solver. On boolean-heavy transition-system
//! queries (CHC lustre class) most atoms are don't-cares: their values do not
//! contribute to satisfying the asserted roots. Asserting them anyway makes
//! the theory solver enumerate-and-block hundreds of irrelevant don't-care
//! combinations (278–1006 iterations per check observed) — the dominant term
//! of AY's 100-300× per-check gap vs OpenSMT on this profile.
//!
//! `mark_relevant_atoms` walks the term DAG top-down from the asserted roots
//! under the current SAT model (standard don't-care propagation / dual-rail
//! justification frontier):
//! - `and` true → all children relevant; false → ONE known-false child.
//! - `or` false → all children; true → ONE known-true child.
//! - `=>` true → a known-false antecedent or known-true consequent; false →
//!   both children.
//! - `not` → child; Bool `ite` → condition + taken branch; `xor`/Bool-`=` →
//!   all children (conservative).
//! - Theory atoms, Bool vars, constants → stop.
//! - Anything unrecognized, or a node with an unknown model value where a
//!   choice is required → conservative (mark everything reachable).
//!
//! Soundness: only the ASSERTION SET sent to the theory solver shrinks.
//! UNSAT conflicts over fewer asserted atoms yield shorter, more general
//! blocking clauses (still valid theory lemmas). SAT models are re-verified
//! against the original expression by `sat_or_unknown` before SAT is
//! reported, so a wrong don't-care choice can only degrade to Unknown, never
//! to a wrong answer. Kill switch: `--chc-dont-care-filter=0`.

use std::collections::BTreeMap;

use ay_core::kani_compat::DetHashSet as FxHashSet;
use ay_core::term::{Symbol, TermData};
use ay_core::{TermId, TermStore};

use super::super::model_verify::is_theory_atom;

/// Returns true when don't-care relevancy filtering is enabled.
///
/// DEFAULT OFF: the first enabled baseline produced wrong-sat answers on
/// aeval-unsafe/llreve instances (bisected to this filter; suspected leak:
/// a wrong UNSAT inside PDR's own model VALIDATORS — which also run through
/// the filtered check_sat — lets a bad invariant validate, and/or
/// Indeterminate model verification accepting under-evaluated models).
/// Re-enable with `--chc-dont-care-filter` only for experiments until
/// the z3 differential corpus passes and the root cause is fixed.
pub(crate) fn dont_care_filter_enabled() -> bool {
    static ENABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ENABLED.get_or_init(|| ay_core::misc_cli_flags().chc_dont_care_filter)
}

/// Model value of a term under the current SAT model, if it has a CNF var.
fn value_of(term_to_var: &BTreeMap<TermId, u32>, model: &[bool], tid: TermId) -> Option<bool> {
    let &var = term_to_var.get(&tid)?;
    model.get((var - 1) as usize).copied()
}

/// Compute the set of theory atoms relevant to justifying the asserted
/// roots under `model`. Returns `None` when marking cannot be trusted
/// (e.g., a root without a CNF variable) — callers then assert everything
/// (previous behavior).
pub(super) fn mark_relevant_atoms(
    terms: &TermStore,
    roots: &[TermId],
    term_to_var: &BTreeMap<TermId, u32>,
    model: &[bool],
) -> Option<FxHashSet<TermId>> {
    let mut relevant: FxHashSet<TermId> = FxHashSet::default();
    let mut visited: FxHashSet<TermId> = FxHashSet::default();
    let mut work: Vec<TermId> = Vec::with_capacity(roots.len() * 4);

    for &root in roots {
        // Roots are asserted true (assumption literals / root assertion).
        // A root without a CNF var means the encoding shape is unexpected;
        // bail to unfiltered behavior.
        term_to_var.get(&root)?;
        work.push(root);
    }

    while let Some(tid) = work.pop() {
        if !visited.insert(tid) {
            continue;
        }
        if is_theory_atom(terms, tid) {
            relevant.insert(tid);
            continue;
        }
        match terms.get(tid) {
            TermData::Const(_) | TermData::Var(..) => {}
            TermData::Not(inner) => work.push(*inner),
            TermData::Ite(cond, then_b, else_b) => {
                work.push(*cond);
                match value_of(term_to_var, model, *cond) {
                    Some(true) => work.push(*then_b),
                    Some(false) => work.push(*else_b),
                    None => {
                        work.push(*then_b);
                        work.push(*else_b);
                    }
                }
            }
            TermData::App(Symbol::Named(name), args) => match name.as_str() {
                "and" => match value_of(term_to_var, model, tid) {
                    Some(false) => {
                        // One known-false child justifies the false `and`.
                        if let Some(&falsifier) = args
                            .iter()
                            .find(|&&a| value_of(term_to_var, model, a) == Some(false))
                        {
                            work.push(falsifier);
                        } else {
                            work.extend(args.iter().copied());
                        }
                    }
                    // True (all children needed) or unknown (conservative).
                    _ => work.extend(args.iter().copied()),
                },
                "or" => match value_of(term_to_var, model, tid) {
                    Some(true) => {
                        if let Some(&satisfier) = args
                            .iter()
                            .find(|&&a| value_of(term_to_var, model, a) == Some(true))
                        {
                            work.push(satisfier);
                        } else {
                            work.extend(args.iter().copied());
                        }
                    }
                    _ => work.extend(args.iter().copied()),
                },
                "=>" if args.len() == 2 => match value_of(term_to_var, model, tid) {
                    Some(true) => {
                        if value_of(term_to_var, model, args[0]) == Some(false) {
                            work.push(args[0]);
                        } else if value_of(term_to_var, model, args[1]) == Some(true) {
                            work.push(args[1]);
                        } else {
                            work.extend(args.iter().copied());
                        }
                    }
                    _ => work.extend(args.iter().copied()),
                },
                // xor / Bool equality (iff) / distinct and anything else
                // Boolean-structural: all children (conservative but cheap).
                _ => work.extend(args.iter().copied()),
            },
            // Unexpected shapes under a Boolean skeleton (quantifiers, let):
            // bail to unfiltered behavior for the whole check.
            TermData::Let(..) | TermData::Forall(..) | TermData::Exists(..) => return None,
            #[allow(unreachable_patterns)]
            _ => return None,
        }
    }

    Some(relevant)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Build (or A B) where A = (x <= 0), B = (x >= 5); model: or=true,
    /// A=true, B=false → only A should be relevant.
    #[test]
    fn or_true_marks_single_true_child() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x".to_string(), ay_core::Sort::Int);
        let zero = terms.mk_int(num_bigint::BigInt::from(0));
        let five = terms.mk_int(num_bigint::BigInt::from(5));
        let a = terms.mk_le(x, zero);
        let b = terms.mk_ge(x, five);
        let root = terms.mk_or(vec![a, b]);

        let mut term_to_var = BTreeMap::new();
        term_to_var.insert(root, 1u32);
        term_to_var.insert(a, 2u32);
        term_to_var.insert(b, 3u32);
        let model = vec![true, true, false];

        let relevant = mark_relevant_atoms(&terms, &[root], &term_to_var, &model)
            .expect("marking should succeed");
        assert!(relevant.contains(&a), "true child must be relevant");
        assert!(
            !relevant.contains(&b),
            "false child of a satisfied `or` is a don't-care"
        );
    }

    /// Root without a CNF var must bail to unfiltered (None).
    #[test]
    fn unmapped_root_bails() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x".to_string(), ay_core::Sort::Int);
        let zero = terms.mk_int(num_bigint::BigInt::from(0));
        let a = terms.mk_le(x, zero);
        let term_to_var = BTreeMap::new();
        assert!(mark_relevant_atoms(&terms, &[a], &term_to_var, &[]).is_none());
    }
}
