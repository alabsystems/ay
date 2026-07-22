// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Predicate storage for CEGAR abstraction
//!
//! Reference: `reference/eldarica/src/main/scala/lazabs/horn/bottomup/PredicateStore.scala`

use crate::{ChcExpr, PredicateId};
use ay_core::kani_compat::DetHashMap as FxHashMap;

/// A predicate associated with a relation symbol
///
/// These are the predicates used for predicate abstraction.
/// Each predicate is a formula over the relation's arguments.
#[derive(Clone, Debug)]
pub(super) struct RelationPredicate {
    /// The predicate formula (over the relation's argument variables)
    pub(super) formula: ChcExpr,
}

/// Store for predicates used in CEGAR abstraction
///
/// Manages predicates per relation symbol, supporting:
/// - Adding new predicates discovered through refinement
/// - Looking up predicates by relation
/// - Checking for duplicate predicates
pub(super) struct PredicateStore {
    /// All predicates, indexed by their global ID
    predicates: Vec<RelationPredicate>,

    /// Predicates grouped by relation symbol
    by_relation: FxHashMap<PredicateId, Vec<usize>>,

    /// Next predicate ID
    next_id: usize,
}

impl PredicateStore {
    /// Create a new empty predicate store
    pub(super) fn new() -> Self {
        Self {
            predicates: Vec::new(),
            by_relation: FxHashMap::default(),
            next_id: 0,
        }
    }

    /// Add a predicate for a relation
    ///
    /// Returns the predicate ID (index)
    pub(super) fn add_predicate(&mut self, relation: PredicateId, formula: ChcExpr) -> usize {
        let id = self.next_id;
        self.next_id += 1;

        self.predicates.push(RelationPredicate { formula });
        self.by_relation.entry(relation).or_default().push(id);

        id
    }

    /// Get all predicates for a relation
    pub(super) fn predicates_for_relation(&self, relation: PredicateId) -> &[usize] {
        self.by_relation.get(&relation).map_or(&[], Vec::as_slice)
    }

    /// Get a predicate by ID
    pub(super) fn get(&self, id: usize) -> Option<&RelationPredicate> {
        self.predicates.get(id)
    }

    /// Get the number of predicates.
    #[allow(clippy::len_without_is_empty)]
    pub(super) fn len(&self) -> usize {
        self.predicates.len()
    }

    /// Get predicates for a relation as formulas
    pub(super) fn get_formulas(&self, relation: PredicateId) -> Vec<&ChcExpr> {
        self.predicates_for_relation(relation)
            .iter()
            .filter_map(|&id| self.predicates.get(id))
            .map(|p| &p.formula)
            .collect()
    }
}

impl Default for PredicateStore {
    fn default() -> Self {
        Self::new()
    }
}

#[allow(clippy::unwrap_used)]
#[cfg(test)]
#[path = "predicate_store_tests.rs"]
mod tests;
