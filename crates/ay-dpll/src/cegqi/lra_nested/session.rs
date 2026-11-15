// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The nested search's SESSION cache (#qlra-nested-cegqi milestone M4).
//!
//! An incremental session asks the lane again after every `push`/`pop`, and
//! the authored roots of consecutive check-sats share quantified subterms
//! (an outer-scope universal stays asserted while inner scopes come and go).
//! The cache keeps, per node QUANTIFIER TERM (the key the tree builder
//! identifies a node by), what the search learned about that node:
//!
//! * its counterexample constants, so a later tree rebuilds the node — and,
//!   by hash-consing, every descendant's quantifier term — over the same
//!   constants and the logged instances keep their meaning;
//! * its instance log `Γ_N` (frozen instances);
//! * its exact flag.
//!
//! WHY THIS IS VALID ACROSS CONTEXTS. Every logged instance is frozen when
//! all children of its node are exact (`approx.rs`, Lemma 10.1), so it is
//! EQUIVALENT to the true instance `ψ_N[k, t]` — a consequence of the node
//! (authored `forall`) or a witness disjunct of it (authored `exists`) for
//! every environment `k`, whatever else is asserted. The exact flag is set
//! only from a context-free counterexample UNSAT (`nested.rs`: "a nested node
//! is exact only from a context-free UNSAT") and states `⌊N⌋Γ ⟺ N` for every
//! `k`; adding instances keeps it (a conjunction of more true instances of a
//! universal is still implied by it and still implies it). Neither depends on
//! the roots the earlier search ran for, so seeding a later search with them
//! is the same as continuing that search with different roots. TOP-LEVEL
//! saturation (the main query's `Sat`) is a claim about the roots and is NOT
//! cached: the main loop runs afresh every check-sat. And every verdict stays
//! a hint that a publication route re-derives.
//!
//! TERM LIFETIME. The cached `TermId`s are minted in the live store. The
//! cache is bound to the store's structural snapshot (identity, generation,
//! length) at the time it was written: any rollback below the cached prefix,
//! compaction or store replacement retires it, and [`NestedSessionCache::
//! validate`] then clears it. A lane rollback to a checkpoint ABOVE the
//! cached prefix leaves every cached id alive; the caller re-binds the
//! cache to the new generation ([`NestedSessionCache::rebind_after_rollback`]).

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::TermStoreSnapshotStamp;
use ay_core::{TermId, TermStore};

use super::approx::NInstance;
use super::ntree::NestedTree;

/// Quantifier nodes the cache keeps before it starts over.
pub(crate) const MAX_CACHED_NODES: usize = 4096;

/// What the search learned about one node.
#[derive(Clone, Debug)]
pub(crate) struct CachedNode {
    pub(crate) ce_vars: Vec<TermId>,
    pub(crate) gamma: Vec<NInstance>,
    pub(crate) exact: bool,
}

/// Per-node seed for a search: Γ and exact flags indexed like the tree.
#[derive(Clone, Debug, Default)]
pub(crate) struct NestedSeed {
    pub(crate) gamma: Vec<Vec<NInstance>>,
    pub(crate) exact: Vec<bool>,
    /// Nodes found in the cache.
    pub(crate) hits: usize,
}

/// See the module docs.
#[derive(Default)]
pub(crate) struct NestedSessionCache {
    nodes: HashMap<TermId, CachedNode>,
    /// The store snapshot every cached id lies below; `None` while empty.
    stamp: Option<TermStoreSnapshotStamp>,
    /// Store length when last written (every cached id is below it).
    len: usize,
}

impl NestedSessionCache {
    /// Cached nodes (for statistics and tests).
    pub(crate) fn len(&self) -> usize {
        self.nodes.len()
    }

    pub(crate) fn clear(&mut self) {
        self.nodes.clear();
        self.stamp = None;
        self.len = 0;
    }

    /// Whether every cached id still names the same term in `terms`.
    pub(crate) fn is_valid_for(&self, terms: &TermStore) -> bool {
        self.stamp
            .as_ref()
            .is_some_and(|stamp| stamp.is_append_only_prefix_of(terms))
    }

    /// Clear the cache unless it is still bound to `terms` (see the module
    /// docs). Returns whether anything survived.
    pub(crate) fn validate(&mut self, terms: &TermStore) -> bool {
        if !self.is_valid_for(terms) {
            self.clear();
        }
        !self.nodes.is_empty()
    }

    /// Before rolling `terms` back to a checkpoint taken at length
    /// `checkpoint_len`: whether the cache will survive it. Call
    /// [`Self::rebind_after_rollback`] with the answer afterwards.
    pub(crate) fn survives_rollback_to(&self, terms: &TermStore, checkpoint_len: usize) -> bool {
        self.is_valid_for(terms) && self.len <= checkpoint_len
    }

    /// After a rollback: re-bind a surviving cache to the store's new
    /// generation, or clear one that did not survive.
    pub(crate) fn rebind_after_rollback(&mut self, terms: &TermStore, survived: bool) {
        if survived && !self.nodes.is_empty() {
            self.stamp = Some(terms.snapshot_stamp());
        } else {
            self.clear();
        }
    }

    /// Counterexample constants cached for quantifier term `q`.
    pub(crate) fn ce_vars(&self, q: TermId) -> Option<&[TermId]> {
        self.nodes.get(&q).map(|node| node.ce_vars.as_slice())
    }

    /// The seed for a search over `tree`: cached Γ and exact flags of every
    /// node whose quantifier term AND counterexample constants match.
    pub(crate) fn seed(&self, tree: &NestedTree) -> NestedSeed {
        let mut seed = NestedSeed {
            gamma: vec![Vec::new(); tree.nodes.len()],
            exact: vec![false; tree.nodes.len()],
            hits: 0,
        };
        for (&q, &index) in &tree.node_of {
            let Some(cached) = self.nodes.get(&q) else {
                continue;
            };
            if cached.ce_vars != tree.nodes[index].ce_vars {
                continue;
            }
            seed.gamma[index].clone_from(&cached.gamma);
            seed.exact[index] = cached.exact;
            seed.hits += 1;
        }
        seed
    }

    /// Record a search's final state. The caller guarantees every id in
    /// `tree`, `gamma` is live in `terms` (the pass kept its terms).
    pub(crate) fn record(
        &mut self,
        terms: &TermStore,
        tree: &NestedTree,
        gamma: &[Vec<NInstance>],
        exact: &[bool],
    ) {
        if gamma.len() != tree.nodes.len() || exact.len() != tree.nodes.len() {
            return;
        }
        self.validate(terms);
        if self.nodes.len().saturating_add(tree.nodes.len()) > MAX_CACHED_NODES {
            self.clear();
        }
        for (&q, &index) in &tree.node_of {
            let node = &tree.nodes[index];
            match self.nodes.get_mut(&q) {
                // Same constants: Γ only grows within and across searches.
                Some(cached) if cached.ce_vars == node.ce_vars => {
                    if gamma[index].len() >= cached.gamma.len() {
                        cached.gamma.clone_from(&gamma[index]);
                        cached.exact = exact[index];
                    }
                }
                _ => {
                    self.nodes.insert(
                        q,
                        CachedNode {
                            ce_vars: node.ce_vars.clone(),
                            gamma: gamma[index].clone(),
                            exact: exact[index],
                        },
                    );
                }
            }
        }
        if !self.nodes.is_empty() {
            self.stamp = Some(terms.snapshot_stamp());
            self.len = terms.len();
        }
    }
}
