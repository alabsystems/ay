// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Numeric syntax upper bound only; original recognition still selects routes.

use super::*;

/// Call only after complete typed acyclic source preflight and its work debit.
/// Skip the contains-read early exit, conservatively counting extra products.
/// Original branch/fact refusal semantics and raw occurrences are preserved.
pub(in crate::checker::bv_bitblast) fn candidate_bound(
    terms: &TermStore,
    clause: &[TermId],
) -> usize {
    let [negative] = clause else {
        return 0;
    };
    let TermData::Not(root) = terms.get(*negative) else {
        return 0;
    };
    if conjuncts(terms, *root).is_none() {
        return 0;
    }
    let Some(facts) = facts(terms, *root) else {
        return 0;
    };
    let mut candidates = 0usize;
    for fact in facts {
        let Some([a, b]) = binary(terms, fact, "or") else {
            continue;
        };
        let (Some(left), Some(right)) =
            (branch_comparisons(terms, a), branch_comparisons(terms, b))
        else {
            continue;
        };
        // Each list has at most32 entries. The original257th header refuses
        // before from_guard; its single header is separately charged.
        let Some(product) = left.len().checked_mul(right.len()) else {
            return 256;
        };
        let Some(next) = candidates.checked_add(product) else {
            return 256;
        };
        candidates = next;
        if candidates >= 256 {
            return 256;
        }
    }
    candidates
}

fn facts(terms: &TermStore, root: TermId) -> Option<Vec<TermId>> {
    let mut pending = vec![root];
    let mut facts = Vec::new();
    while let Some(term) = pending.pop() {
        terms.entry_stamp(term)?;
        if facts.len() + pending.len() >= 64 || terms.sort(term) != &Sort::Bool {
            return None;
        }
        facts.push(term);
        if let Some(args) = conjuncts(terms, term) {
            pending.extend_from_slice(args);
        }
    }
    Some(facts)
}
