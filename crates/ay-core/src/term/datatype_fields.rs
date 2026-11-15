// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Field sorts of declared datatype carriers.
//!
//! A `declare-datatype` carrier reaches the store as a `Sort::Uninterpreted`
//! identity with no constructor table; only an inline `Sort::Datatype` carries
//! its fields. A consumer that holds nothing but the store therefore could not
//! tell what a declared carrier contains. `StaticFeatures` needs exactly that:
//! `(Array I Row)` whose `Row` has an array-valued field is nested array state,
//! and `has_nested_arrays` read it as flat, which let a declared record carrier
//! bypass the nested-array UNSAT quarantine that an inline carrier of the same
//! shape triggers (#nested-array-quarantine-datatype-fields).
//!
//! Like `constructor_fields`, the map is populated by the declaring layer,
//! append-only for the store's lifetime and keyed by NAME, so it survives
//! `rollback_to` and `mark_and_compact`. A carrier that was never registered
//! reads as having no fields: for the quarantine that is fail-OPEN, so every
//! declaring layer that mints a carrier identity must register it.

use super::TermStore;
use crate::sort::Sort;

impl TermStore {
    /// Record the field sorts of one constructor of the declared datatype
    /// `carrier`.
    ///
    /// Accumulates across constructors and skips a sort already recorded for
    /// the carrier, so re-declaring the same shape is a no-op.
    pub fn register_datatype_field_sorts(&mut self, carrier: &str, fields: &[Sort]) {
        let recorded = self
            .datatype_field_sorts
            .entry(carrier.to_string())
            .or_default();
        for field in fields {
            if !recorded.contains(field) {
                recorded.push(field.clone());
            }
        }
    }

    /// Every registered field sort of the declared datatype `carrier`, or
    /// `None` when no declaring layer registered it.
    #[must_use]
    pub fn datatype_field_sorts(&self, carrier: &str) -> Option<&[Sort]> {
        self.datatype_field_sorts.get(carrier).map(Vec::as_slice)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn carrier_field_sorts_accumulate_deduplicate_and_survive_clone() {
        let mut store = TermStore::new();
        assert_eq!(store.datatype_field_sorts("Row"), None);

        let cells = Sort::array(Sort::Int, Sort::Int);
        store.register_datatype_field_sorts("Row", &[cells.clone(), Sort::Int]);
        // A second constructor adds only the sort not yet recorded.
        store.register_datatype_field_sorts("Row", &[Sort::Int, Sort::Bool]);
        // An enum-like carrier with only nullary constructors is still known.
        store.register_datatype_field_sorts("Color", &[]);

        let expected = [cells, Sort::Int, Sort::Bool];
        assert_eq!(store.datatype_field_sorts("Row"), Some(&expected[..]));
        assert_eq!(store.datatype_field_sorts("Color"), Some(&[][..]));
        assert_eq!(store.datatype_field_sorts("Unrelated"), None);

        let cloned = store.clone();
        assert_eq!(cloned.datatype_field_sorts("Row"), Some(&expected[..]));
    }
}
