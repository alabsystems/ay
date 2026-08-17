// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact authored-root lineage for finite quantifier expansion.
//!
//! Proof export records only top-level universal instances. SAT publication
//! instead needs the exact semantic replacement of any supported authored
//! root, including the common `not (exists ...)` shell. Keep that additional
//! lineage separate from proof payload so neither role can impersonate the
//! other.

use ay_core::{Sort, TermData, TermId, TermStore};

use super::super::FiniteExpansionRecord;
use crate::ematching::contains_quantifier;

pub(super) fn exact_record(
    terms: &mut TermStore,
    original: TermId,
    assertion_index: usize,
    expanded: TermId,
    direct_expansion: Option<TermId>,
) -> Option<FiniteExpansionRecord> {
    let replayed = direct_expansion.or_else(|| replay_negated_existential(terms, original))?;
    (replayed == expanded).then_some(FiniteExpansionRecord {
        original,
        assertion_index,
        expanded,
    })
}

fn replay_negated_existential(terms: &mut TermStore, root: TermId) -> Option<TermId> {
    let TermData::Not(inner) = terms.get(root).clone() else {
        return None;
    };
    let TermData::Exists(vars, body, _) = terms.get(inner).clone() else {
        return None;
    };
    if vars.len() != 1 || vars[0].1 != Sort::Int || contains_quantifier(terms, body) {
        return None;
    }
    let (expanded, _) = crate::skolemize::finite_domain_expand_with_instances(terms, inner)?;
    if contains_quantifier(terms, expanded) {
        return None;
    }
    Some(terms.mk_not(expanded))
}

#[cfg(test)]
mod tests {
    use ay_core::term::Symbol;
    use num_bigint::BigInt;

    use super::*;

    fn negated_bounded_exists(terms: &mut TermStore) -> TermId {
        let name = "x".to_string();
        let x = terms.mk_var(&name, Sort::Int);
        let zero = terms.mk_int(BigInt::from(0));
        let three = terms.mk_int(BigInt::from(3));
        let lower = terms.mk_le(zero, x);
        let upper = terms.mk_le(x, three);
        let predicate = terms.mk_app(Symbol::named("P"), [x], Sort::Bool);
        let body = terms.mk_and(vec![lower, upper, predicate]);
        let exists = terms.mk_exists(vec![(name, Sort::Int)], body);
        terms.mk_not(exists)
    }

    #[test]
    fn records_the_exact_negated_existential_root() {
        let mut terms = TermStore::new();
        let root = negated_bounded_exists(&mut terms);
        let expanded = crate::skolemize::expand_finite_domain_subterms(&mut terms, root);
        let record = exact_record(&mut terms, root, 7, expanded, None)
            .expect("supported authored shell replays exactly");

        assert_eq!(record.original, root);
        assert_eq!(record.assertion_index, 7);
        assert_eq!(record.expanded, expanded);
        assert!(!contains_quantifier(&terms, expanded));
    }

    #[test]
    fn declines_ground_drift_and_non_int_shells() {
        let mut terms = TermStore::new();
        let root = negated_bounded_exists(&mut terms);
        let expanded = crate::skolemize::expand_finite_domain_subterms(&mut terms, root);
        let drift = terms.true_term();
        assert!(exact_record(&mut terms, root, 0, drift, None).is_none());

        let name = "b".to_string();
        let b = terms.mk_var(&name, Sort::Bool);
        let exists = terms.mk_exists(vec![(name, Sort::Bool)], b);
        let bool_root = terms.mk_not(exists);
        let bool_expanded = crate::skolemize::expand_finite_domain_subterms(&mut terms, bool_root);
        assert!(exact_record(&mut terms, bool_root, 0, bool_expanded, None).is_none());

        assert_ne!(expanded, root);
    }
}
