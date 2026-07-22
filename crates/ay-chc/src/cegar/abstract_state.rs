// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Abstract states and edges for CEGAR
//!
//! Reference: `reference/eldarica/src/main/scala/lazabs/horn/bottomup/AbstractState.scala`

use crate::PredicateId;
use ay_core::kani_compat::DetHashSet as FxHashSet;
use std::hash::{Hash, Hasher};

/// An abstract state in the CEGAR reachability graph
///
/// Each state represents a (relation symbol, set of predicates) pair.
/// The predicates are conjunctive - the state represents all concrete
/// states satisfying all the predicates.
///
/// Subsumption: state A subsumes state B if A.predicates ⊆ B.predicates
/// (fewer predicates = more general = subsumes more concrete states)
#[derive(Clone, Debug)]
pub(crate) struct AbstractState {
    /// The relation symbol (predicate) this state belongs to
    pub(crate) relation: PredicateId,

    /// The predicates assumed to hold in this state (sorted for deterministic hashing).
    /// These are indices into the PredicateStore.
    pub(super) predicates: Vec<usize>,

    /// Cached hash of predicates for quick subsumption checks
    predicate_hash_set: FxHashSet<usize>,

    /// Cached hash value, computed once at construction (#2673).
    /// Avoids Vec allocation + sort on every Hash::hash() call.
    cached_hash: u64,
}

impl AbstractState {
    /// Create a new abstract state
    pub(super) fn new(relation: PredicateId, mut predicates: Vec<usize>) -> Self {
        let predicate_hash_set: FxHashSet<usize> = predicates.iter().copied().collect();
        // Sort once at construction so Hash is deterministic without per-call allocation
        predicates.sort_unstable();
        // Pre-compute hash
        let cached_hash = {
            use std::collections::hash_map::DefaultHasher;
            let mut h = DefaultHasher::new();
            relation.hash(&mut h);
            predicates.hash(&mut h);
            h.finish()
        };
        Self {
            relation,
            predicates,
            predicate_hash_set,
            cached_hash,
        }
    }

    /// Check if this state subsumes another
    ///
    /// A subsumes B if A has fewer/equal predicates that are all in B
    /// (A is more general, represents more concrete states)
    pub(super) fn subsumes(&self, other: &Self) -> bool {
        self.relation == other.relation
            && self.predicates.len() <= other.predicates.len()
            && self.predicate_hash_set.is_subset(&other.predicate_hash_set)
    }
}

impl PartialEq for AbstractState {
    fn eq(&self, other: &Self) -> bool {
        self.relation == other.relation && self.predicate_hash_set == other.predicate_hash_set
    }
}

impl Eq for AbstractState {}

impl Hash for AbstractState {
    fn hash<H: Hasher>(&self, state: &mut H) {
        // Use pre-computed hash to avoid Vec allocation + sort per call (#2673)
        self.cached_hash.hash(state);
    }
}

/// An edge in the abstract reachability graph
///
/// Represents: (from_states, clause) => to_state
#[derive(Clone, Debug)]
pub(super) struct AbstractEdge {
    /// Source abstract states (for clause body predicates)
    pub(super) from: Vec<AbstractState>,

    /// Target abstract state (for clause head predicate)
    pub(super) to: AbstractState,

    /// The Horn clause that generated this edge
    pub(super) clause_index: usize,
}

impl AbstractEdge {
    /// Create a new abstract edge
    pub(super) fn new(from: Vec<AbstractState>, to: AbstractState, clause_index: usize) -> Self {
        Self {
            from,
            to,
            clause_index,
        }
    }
}

#[allow(clippy::unwrap_used)]
#[cfg(test)]
#[path = "abstract_state_tests.rs"]
mod tests;
