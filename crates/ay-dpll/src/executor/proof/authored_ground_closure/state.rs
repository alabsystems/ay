// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The union-find and justification graph behind the raw ground closure.
//!
//! Pure bookkeeping over [`TermId`]s: it decides nothing about any theory. An
//! edge is recorded only together with the reason its producer will later
//! prove, and classes merge ONLY through recorded edges, so class membership
//! is exactly connectivity in the edge graph. That is what makes every merge
//! explainable: [`GroundClosure::path`] recovers a chain of edges between two
//! members of one class, restricted to the edges recorded before a given one,
//! which keeps each explanation well founded (an edge is only ever explained
//! from strictly earlier edges).

use std::collections::VecDeque;

use ay_core::kani_compat::DetHashMap;
use ay_core::TermId;

/// Why two terms were merged. Each variant names the strict-checked lemma
/// family that proves the edge's equality; see `emit.rs`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum EdgeReason {
    /// An exact raw authored equality root.
    Authored(TermId),
    /// Two applications of one symbol whose arguments are pairwise merged.
    Congruent,
    /// A closed bit-vector term and the constant it evaluates to.
    Evaluated,
    /// A word-level wiring identity: a slice rewrite or multiplication
    /// by the literal bit-vector unit (`slice.rs`).
    SliceIdentity,
    /// A modular constant-offset identity proposed by the ordinary term
    /// constructor, independently replayed as a bit-vector lemma.
    ModularOffset,
    /// `select(store(A, i, e), j) = e` with `i` and `j` merged.
    ReadHit,
    /// `select(store(A, i, e), j) = select(A, j)` with `i` and `j` in classes
    /// holding two different bit-vector constants.
    ReadMiss,
    /// A direct read equality whose actual store-hit or tail and skipped keys
    /// are retained in the search's bounded read-chain witness table.
    ReadChain(usize),
    /// Full-width packing through earlier byte classes and a strict BV identity.
    Packing(usize),
    /// An equality literal the fact base derived (by index into its facts).
    Derived(usize),
}

/// One recorded merge: the equality `(= a b)` in exactly this orientation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) struct ClosureEdge {
    pub(super) a: TermId,
    pub(super) b: TermId,
    pub(super) reason: EdgeReason,
}

/// Union-find over the registered terms plus the justification edges.
#[derive(Default)]
pub(super) struct GroundClosure {
    nodes: Vec<TermId>,
    index: DetHashMap<TermId, usize>,
    parent: Vec<usize>,
    member_head: Vec<usize>,
    member_tail: Vec<usize>,
    member_next: Vec<Option<usize>>,
    edges: Vec<ClosureEdge>,
}

impl GroundClosure {
    /// Register `term`, returning whether it is new. Registration never
    /// merges anything.
    pub(super) fn register(&mut self, term: TermId) -> bool {
        if self.index.contains_key(&term) {
            return false;
        }
        let slot = self.nodes.len();
        self.nodes.push(term);
        self.parent.push(slot);
        self.member_head.push(slot);
        self.member_tail.push(slot);
        self.member_next.push(None);
        self.index.insert(term, slot);
        true
    }

    pub(super) fn nodes(&self) -> &[TermId] {
        &self.nodes
    }

    pub(super) fn edges(&self) -> &[ClosureEdge] {
        &self.edges
    }

    fn root_of_slot(&self, mut slot: usize) -> usize {
        while self.parent[slot] != slot {
            slot = self.parent[slot];
        }
        slot
    }

    /// The class representative slot of a registered term.
    pub(super) fn class(&self, term: TermId) -> Option<usize> {
        self.index.get(&term).map(|&slot| self.root_of_slot(slot))
    }

    pub(super) fn same_class(&self, left: TermId, right: TermId) -> bool {
        left == right
            || matches!(
                (self.class(left), self.class(right)),
                (Some(l), Some(r)) if l == r
            )
    }

    /// Exact current class members without inspecting unrelated classes.
    /// The list is only search bookkeeping: an emitted use must still recover
    /// its earlier-edge justification through `path`.
    pub(super) fn members(&self, term: TermId) -> impl Iterator<Item = TermId> + '_ {
        let mut cursor = self.class(term).map(|root| self.member_head[root]);
        std::iter::from_fn(move || {
            let slot = cursor?;
            cursor = self.member_next[slot];
            Some(self.nodes[slot])
        })
        .take(self.nodes.len())
    }

    /// Merge the classes of two registered terms through a recorded edge.
    /// Returns `false` (recording nothing) when they already share a class or
    /// either term is unregistered.
    pub(super) fn merge(&mut self, a: TermId, b: TermId, reason: EdgeReason) -> bool {
        let (Some(left), Some(right)) = (self.class(a), self.class(b)) else {
            return false;
        };
        if left == right {
            return false;
        }
        self.member_next[self.member_tail[right]] = Some(self.member_head[left]);
        self.member_tail[right] = self.member_tail[left];
        self.parent[left] = right;
        self.edges.push(ClosureEdge { a, b, reason });
        true
    }

    /// The shortest chain of edges with index `< limit` joining `from` to
    /// `to`, as edge indices in walk order. `Some(empty)` when the two are the
    /// same term; `None` when no such chain exists.
    pub(super) fn path(&self, from: TermId, to: TermId, limit: usize) -> Option<Vec<usize>> {
        if from == to {
            return Some(Vec::new());
        }
        let limit = limit.min(self.edges.len());
        let mut adjacency: DetHashMap<TermId, Vec<(TermId, usize)>> = DetHashMap::default();
        for (edge_index, edge) in self.edges[..limit].iter().enumerate() {
            adjacency
                .entry(edge.a)
                .or_default()
                .push((edge.b, edge_index));
            adjacency
                .entry(edge.b)
                .or_default()
                .push((edge.a, edge_index));
        }
        let mut reached: DetHashMap<TermId, (TermId, usize)> = DetHashMap::default();
        reached.insert(from, (from, usize::MAX));
        let mut queue = VecDeque::from([from]);
        while let Some(current) = queue.pop_front() {
            if current == to {
                break;
            }
            for &(next, edge_index) in adjacency.get(&current).map_or(&[][..], Vec::as_slice) {
                if !reached.contains_key(&next) {
                    reached.insert(next, (current, edge_index));
                    queue.push_back(next);
                }
            }
        }
        let mut walk = Vec::new();
        let mut current = to;
        while current != from {
            let &(previous, edge_index) = reached.get(&current)?;
            walk.push(edge_index);
            current = previous;
        }
        walk.reverse();
        Some(walk)
    }
}

#[cfg(test)]
mod member_tests {
    use super::*;

    #[test]
    fn member_views_follow_disjoint_unions_without_authorizing_future_paths() {
        let mut closure = GroundClosure::default();
        for id in 0..8 {
            assert!(closure.register(TermId(id)));
        }
        for (left, right) in [(0, 1), (2, 3), (1, 3), (5, 4), (4, 6), (0, 6)] {
            assert!(closure.merge(TermId(left), TermId(right), EdgeReason::Congruent));
            for id in 0..8 {
                let mut members: Vec<_> = closure.members(TermId(id)).collect();
                members.sort();
                let expected: Vec<_> = (0..8)
                    .map(TermId)
                    .filter(|&member| closure.same_class(TermId(id), member))
                    .collect();
                assert_eq!(members, expected);
            }
        }
        assert!(!closure.merge(TermId(3), TermId(5), EdgeReason::Congruent));
        assert_eq!(closure.members(TermId(0)).count(), 7);
        assert_eq!(closure.members(TermId(7)).collect::<Vec<_>>(), [TermId(7)]);
        assert_eq!(closure.members(TermId(u32::MAX)).count(), 0);
        assert!(closure.path(TermId(0), TermId(3), 2).is_none());
        assert!(closure.path(TermId(0), TermId(3), 3).is_some());
    }
}
