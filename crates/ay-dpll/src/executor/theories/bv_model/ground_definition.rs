// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Ground array definitions: recognizing a `store` chain or `const-array`
//! as the value an equality defines an array variable to.

use super::*;

impl Executor {
    /// Whether `term` is a ground array definition: a `store` chain or a
    /// `const-array`. The ONE predicate both for withholding a nested-only
    /// definition ([`Self::array_vars_defined_only_under_nested_equality`]) and
    /// for recognising the model-true definition that lifts the withholding.
    /// They used to disagree: the walk saw only `store`, so a `const-array`
    /// definition stayed withheld in a forced arm, and `mk_store` folds
    /// `(store (const v) i v)` into exactly that `const-array`.
    pub(super) fn is_array_ground_definition(terms: &TermStore, term: TermId) -> bool {
        matches!(terms.get(term), TermData::App(sym, _)
            if sym.name() == "store" || sym.name() == "const-array")
    }

    pub(super) fn store_chain_definition_from_equality(
        terms: &TermStore,
        term: TermId,
    ) -> Option<(TermId, TermId)> {
        let TermData::App(sym, args) = terms.get(term) else {
            return None;
        };
        if sym.name() != "=" || args.len() != 2 {
            return None;
        }

        let lhs = args[0];
        let rhs = args[1];
        if matches!(terms.get(lhs), TermData::Var(_, _))
            && matches!(terms.sort(lhs), Sort::Array(_))
            && Self::is_array_ground_definition(terms, rhs)
        {
            Some((lhs, rhs))
        } else if matches!(terms.get(rhs), TermData::Var(_, _))
            && matches!(terms.sort(rhs), Sort::Array(_))
            && Self::is_array_ground_definition(terms, lhs)
        {
            Some((rhs, lhs))
        } else {
            None
        }
    }

    pub(super) fn store_chain_base(terms: &TermStore, store_term: TermId) -> TermId {
        let mut base = store_term;
        // This is only a dependency hint. The complete builder separately
        // authenticates the chain and refuses an overflow or malformed store.
        for _ in 0..500 {
            match terms.get(base) {
                TermData::App(sym, args) if sym.name() == "store" && args.len() == 3 => {
                    base = args[0];
                }
                _ => return base,
            }
        }
        base
    }
}
