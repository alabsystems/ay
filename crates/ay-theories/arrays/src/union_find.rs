// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Backtrackable union-find over array-equality terms, M1 shadow build.
//!
//! Mirrors the EUF solver's proven design (`euf/src/solver.rs` `UnionFind` +
//! undo trail): union by rank, NO path compression (queries stay `&self` and
//! every union is invertible in O(1)), sparse lazy node insertion so only
//! equality-touched terms enter the structure — matching `eq_adj`'s sparsity.
//!
//! Each union records the concrete *proof-forest edge* that merged the two
//! classes: the asserted equality term, or the sentinel/external reason key —
//! with an asserted-preference flag so later explanation walks can prefer
//! asserted edges over reason-carrying sentinel edges (the
//! `explanation_better` discipline in equality_query.rs).
//!
//! M1 is a *shadow* structure: `eq_adj` remains the source of truth and no
//! solving behavior changes. The shadow is fed from the same three writer
//! sites as `eq_adj` (equality.rs incremental edge-add, `rebuild_assign_indices`,
//! bridge.rs `record_external_equality`) and is validated against the BFS
//! equivalence classes by `#[cfg(debug_assertions)]` invariants
//! (see equality.rs / equality_query.rs). M2 switches the read paths over.

use super::*;

/// Justification for one proof-forest edge.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum EqJustification {
    /// A SAT-visible equality atom asserted true.
    Asserted {
        /// The equality term `(= a b)` assigned true.
        eq_term: TermId,
    },
    /// External (cross-theory) sentinel equality; `key` is the canonical
    /// unordered pair indexing `external_eq_reasons`, `has_reasons` records
    /// whether reason literals were available when the edge was recorded.
    External {
        /// Canonical `ordered_pair` key into `external_eq_reasons`.
        key: (TermId, TermId),
        /// Whether SAT-visible reasons back this edge (reason-free sentinel
        /// edges are connectivity-only, like `WeakEdgeKind::StrongUnreasoned`).
        has_reasons: bool,
    },
}

impl EqJustification {
    /// Asserted-preference flag: asserted edges are preferred over sentinel
    /// edges when building explanations (equality_query.rs
    /// `explanation_better`).
    // M1 shadow API: exercised by debug asserts + unit tests; M2/M3 add the
    // production consumers (read-path switch, scoped pop, delta export).
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn is_asserted(&self) -> bool {
        matches!(self, Self::Asserted { .. })
    }
}

/// One proof-forest edge: the original equality endpoints (NOT the class
/// roots at merge time) plus the justification.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct EqEdge {
    /// Left endpoint of the merging equality.
    pub(crate) a: TermId,
    /// Right endpoint of the merging equality.
    pub(crate) b: TermId,
    /// Why `a = b` holds.
    pub(crate) just: EqJustification,
}

/// O(1)-invertible record of one `union`.
// Fields are read by `pop_scope`, itself M1 shadow API (test-only until the
// M2/M3 production consumers land), so non-test builds see them as dead.
#[cfg_attr(not(test), allow(dead_code))]
#[derive(Debug, Clone, Copy)]
enum Undo {
    Union {
        child_root: TermId,
        parent_root: TermId,
        parent_rank_bumped: bool,
        child_class_len: usize,
    },
}

/// Backtrackable union-find with proof-forest edges (see module docs).
#[derive(Debug, Default)]
pub(crate) struct ArrayUnionFind {
    /// Sparse parent pointers; roots map to themselves. Absent terms are
    /// implicit singleton roots.
    parent: HashMap<TermId, TermId>,
    rank: HashMap<TermId, u32>,
    /// Per non-root node (indexed by the absorbed child root): the edge that
    /// merged it into its parent's class.
    edge: HashMap<TermId, EqEdge>,
    /// Members per root; the absorbed class's members are appended on union
    /// (and split back off by exact count on undo).
    class_list: HashMap<TermId, Vec<TermId>>,
    undo: Vec<Undo>,
    scopes: Vec<usize>,
    /// Append-only within a scope era: `(root_kept, root_absorbed)` per union.
    /// Truncated exactly in step with the undo trail; cleared by `clear()`.
    /// This is the M3 delta-export surface.
    merge_log: Vec<(TermId, TermId)>,
}

impl ArrayUnionFind {
    /// Root of `t`'s class. O(log n) — union by rank, no path compression.
    pub(crate) fn find(&self, t: TermId) -> TermId {
        let mut current = t;
        while let Some(&p) = self.parent.get(&current) {
            if p == current {
                return current;
            }
            current = p;
        }
        current
    }

    /// Whether `a` and `b` are in the same class.
    pub(crate) fn same_class(&self, a: TermId, b: TermId) -> bool {
        a == b || self.find(a) == self.find(b)
    }

    fn ensure_node(&mut self, t: TermId) {
        if !self.parent.contains_key(&t) {
            self.parent.insert(t, t);
            self.rank.insert(t, 0);
            self.class_list.insert(t, vec![t]);
        }
    }

    /// Merge the classes of `a` and `b`, recording the proof-forest edge.
    /// Returns `false` (and records nothing) if they were already merged.
    pub(crate) fn union(&mut self, a: TermId, b: TermId, just: EqJustification) -> bool {
        self.ensure_node(a);
        self.ensure_node(b);
        let ra = self.find(a);
        let rb = self.find(b);
        if ra == rb {
            return false;
        }
        let rank_a = self.rank[&ra];
        let rank_b = self.rank[&rb];
        // Union by rank; ties keep the first argument's root (deterministic:
        // all writer sites feed edges in a deterministic order).
        let (parent_root, child_root) = if rank_a >= rank_b { (ra, rb) } else { (rb, ra) };
        let parent_rank_bumped = rank_a == rank_b;
        if parent_rank_bumped {
            *self.rank.get_mut(&parent_root).expect("node ensured") += 1;
        }
        self.parent.insert(child_root, parent_root);
        self.edge.insert(child_root, EqEdge { a, b, just });
        let moved = std::mem::take(self.class_list.get_mut(&child_root).expect("node ensured"));
        let child_class_len = moved.len();
        self.class_list
            .get_mut(&parent_root)
            .expect("node ensured")
            .extend(moved);
        self.merge_log.push((parent_root, child_root));
        self.undo.push(Undo::Union {
            child_root,
            parent_root,
            parent_rank_bumped,
            child_class_len,
        });
        debug_assert_eq!(
            self.merge_log.len(),
            self.undo.len(),
            "merge_log must grow monotonically, one entry per union, within an era"
        );
        true
    }

    /// Proof-forest edge recorded at absorbed root `t` (non-root nodes only).
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn edge(&self, t: TermId) -> Option<&EqEdge> {
        self.edge.get(&t)
    }

    /// Members of `t`'s class (singleton for terms never unioned).
    pub(crate) fn class_members(&self, t: TermId) -> Vec<TermId> {
        match self.class_list.get(&self.find(t)) {
            Some(members) => members.clone(),
            None => vec![t],
        }
    }

    /// Borrowed view of `t`'s class members, or `None` when `t` was never
    /// unioned (implicit singleton). Allocation-free variant of
    /// `class_members` for read-path scans.
    pub(crate) fn class_slice(&self, t: TermId) -> Option<&[TermId]> {
        self.class_list.get(&self.find(t)).map(Vec::as_slice)
    }

    /// Parent chain from `t` to its root, inclusive of both endpoints.
    fn chain_to_root(&self, t: TermId) -> Vec<TermId> {
        let mut chain = vec![t];
        let mut current = t;
        while let Some(&p) = self.parent.get(&current) {
            if p == current {
                break;
            }
            chain.push(p);
            current = p;
        }
        chain
    }

    /// Whether `t` lies in the (frozen) union-tree subtree rooted at `node`.
    ///
    /// Once a node stops being a root, later unions only attach to roots, so
    /// its subtree is exactly the class it represented at absorption time.
    fn in_subtree(&self, t: TermId, node: TermId) -> bool {
        let mut current = t;
        loop {
            if current == node {
                return true;
            }
            match self.parent.get(&current) {
                Some(&p) if p != current => current = p,
                _ => return false,
            }
        }
    }

    /// Proof-forest explanation of `a = b`: the set of recorded edges whose
    /// justifications, chained by transitivity, connect `a` to `b`.
    ///
    /// Nieuwenhuis–Oliveras-style walk over the union tree: cross the union
    /// edges between the two nodes and their LCA; each crossed edge `x = y`
    /// (original equality endpoints, not roots) spawns sub-explanations inside
    /// the strictly older frozen subtrees on each side. O(path · log n) per
    /// crossed edge (union by rank bounds every chain walk by the tree
    /// height), output-sensitive overall.
    ///
    /// Returns `None` when `a` and `b` are not in the same class, or when the
    /// (defensive) work budget is exceeded — callers must treat `None` as
    /// "no forest explanation available" and fall back, not as a
    /// distinctness verdict.
    // Validated + unit-tested in M2 (explain_soundness_stress); the production
    // reason path stays on the eq_adj BFS through M2 to preserve shortest-path
    // reason shapes, and M3's delta export becomes the consumer.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn explain(&self, a: TermId, b: TermId) -> Option<Vec<EqEdge>> {
        if a == b {
            return Some(Vec::new());
        }
        if self.find(a) != self.find(b) {
            return None;
        }
        let mut out: Vec<EqEdge> = Vec::new();
        let mut pending = vec![(a, b)];
        // Defensive fuel: the walk provably terminates (every sub-pair lives
        // in a strictly older frozen subtree), but an off-by-one here must
        // degrade to the BFS fallback, never hang the solver.
        let mut fuel = 8 * (self.undo.len() + 8);
        while let Some((u, v)) = pending.pop() {
            if u == v {
                continue;
            }
            fuel = fuel.checked_sub(1)?;
            // LCA of u and v in the union tree.
            let u_chain = self.chain_to_root(u);
            let mut v_hops = Vec::new();
            let mut v_cursor = v;
            let lca = loop {
                if u_chain.contains(&v_cursor) {
                    break v_cursor;
                }
                v_hops.push(v_cursor);
                let &p = self.parent.get(&v_cursor)?;
                if p == v_cursor {
                    // v's root is not on u's chain: different trees (should be
                    // unreachable after the find() check above).
                    return None;
                }
                v_cursor = p;
            };
            let lca_pos = u_chain.iter().position(|&n| n == lca)?;
            let u_hops = &u_chain[..lca_pos];

            // Cross the union edges from a start node up to the LCA. Each hop
            // child `n` carries the edge that absorbed n's class; one endpoint
            // is inside subtree(n) (the child side), the other on the parent
            // side. Connect: start ~ child_end (older sub-explanation), edge,
            // then continue from parent_end.
            let walk_side = |mut node: TermId,
                             hops: &[TermId],
                             pending: &mut Vec<(TermId, TermId)>,
                             out: &mut Vec<EqEdge>|
             -> Option<TermId> {
                for &n in hops {
                    let e = *self.edge.get(&n)?;
                    let (child_end, parent_end) = if self.in_subtree(e.a, n) {
                        (e.a, e.b)
                    } else {
                        debug_assert!(self.in_subtree(e.b, n));
                        (e.b, e.a)
                    };
                    if node != child_end {
                        pending.push((node, child_end));
                    }
                    out.push(e);
                    node = parent_end;
                }
                Some(node)
            };
            let nu = walk_side(u, u_hops, &mut pending, &mut out)?;
            let nv = walk_side(v, &v_hops, &mut pending, &mut out)?;
            if nu != nv {
                pending.push((nu, nv));
            }
        }
        Some(out)
    }

    /// All classes with ≥2 members, each sorted, ordered by first member.
    /// Singleton classes are omitted: an untouched term and an absent term are
    /// indistinguishable partitions (matches `eq_adj`, where every key has a
    /// neighbor).
    // M1 shadow API: exercised by debug asserts + unit tests; M2/M3 add the
    // production consumers (read-path switch, scoped pop, delta export).
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn non_singleton_classes(&self) -> Vec<Vec<TermId>> {
        let mut classes: Vec<Vec<TermId>> = self
            .class_list
            .iter()
            .filter(|&(root, members)| self.parent.get(root) == Some(root) && members.len() > 1)
            .map(|(_, members)| {
                let mut members = members.clone();
                members.sort_unstable_by_key(|t| t.0);
                members
            })
            .collect();
        classes.sort_unstable_by_key(|class| class[0].0);
        classes
    }

    /// Append-only merge log for the current era (M3 delta-export surface).
    // M1 shadow API: exercised by debug asserts + unit tests; M2/M3 add the
    // production consumers (read-path switch, scoped pop, delta export).
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn merge_log(&self) -> &[(TermId, TermId)] {
        &self.merge_log
    }

    /// Open an undo scope.
    // M1 shadow API: exercised by debug asserts + unit tests; M2/M3 add the
    // production consumers (read-path switch, scoped pop, delta export).
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn push_scope(&mut self) {
        self.scopes.push(self.undo.len());
    }

    /// Invert every union performed since the matching `push_scope`.
    // M1 shadow API: exercised by debug asserts + unit tests; M2/M3 add the
    // production consumers (read-path switch, scoped pop, delta export).
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn pop_scope(&mut self) {
        let mark = self.scopes.pop().unwrap_or(0);
        while self.undo.len() > mark {
            let Undo::Union {
                child_root,
                parent_root,
                parent_rank_bumped,
                child_class_len,
            } = self.undo.pop().expect("undo length checked above");
            self.parent.insert(child_root, child_root);
            self.edge.remove(&child_root);
            if parent_rank_bumped {
                *self
                    .rank
                    .get_mut(&parent_root)
                    .expect("parent existed at union") -= 1;
            }
            let parent_members = self
                .class_list
                .get_mut(&parent_root)
                .expect("parent existed at union");
            let split_at = parent_members.len() - child_class_len;
            let restored = parent_members.split_off(split_at);
            self.class_list.insert(child_root, restored);
            self.merge_log.pop();
        }
    }

    /// Drop everything: nodes, edges, undo trail, scopes, merge log.
    /// Starts a new merge-log era.
    pub(crate) fn clear(&mut self) {
        self.parent.clear();
        self.rank.clear();
        self.edge.clear();
        self.class_list.clear();
        self.undo.clear();
        self.scopes.clear();
        self.merge_log.clear();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn t(n: u32) -> TermId {
        TermId(n)
    }

    fn asserted(n: u32) -> EqJustification {
        EqJustification::Asserted { eq_term: t(n) }
    }

    #[test]
    fn union_find_round_trip() {
        let mut uf = ArrayUnionFind::default();
        assert_eq!(uf.find(t(1)), t(1));
        assert!(uf.union(t(1), t(2), asserted(100)));
        assert!(uf.same_class(t(1), t(2)));
        assert!(!uf.same_class(t(1), t(3)));
        // Duplicate union is a no-op.
        assert!(!uf.union(t(2), t(1), asserted(101)));
        assert_eq!(uf.merge_log().len(), 1);
        assert!(uf.union(t(3), t(4), asserted(102)));
        assert!(uf.union(t(1), t(3), asserted(103)));
        assert!(uf.same_class(t(2), t(4)));
        assert_eq!(uf.merge_log().len(), 3);
        let mut members = uf.class_members(t(4));
        members.sort_unstable_by_key(|x| x.0);
        assert_eq!(members, vec![t(1), t(2), t(3), t(4)]);
    }

    #[test]
    fn scope_push_pop_undoes_unions_exactly() {
        let mut uf = ArrayUnionFind::default();
        uf.union(t(1), t(2), asserted(100));
        uf.push_scope();
        uf.union(t(3), t(4), asserted(101));
        uf.union(t(1), t(4), asserted(102));
        assert!(uf.same_class(t(2), t(3)));
        assert_eq!(uf.merge_log().len(), 3);
        uf.pop_scope();
        // Scope contents inverted; pre-scope union intact.
        assert!(uf.same_class(t(1), t(2)));
        assert!(!uf.same_class(t(3), t(4)));
        assert!(!uf.same_class(t(1), t(4)));
        assert_eq!(uf.merge_log().len(), 1);
        assert_eq!(uf.class_members(t(3)), vec![t(3)]);
        assert_eq!(uf.class_members(t(4)), vec![t(4)]);
        // Nested scopes.
        uf.push_scope();
        uf.union(t(1), t(5), asserted(103));
        uf.push_scope();
        uf.union(t(6), t(7), asserted(104));
        uf.pop_scope();
        assert!(!uf.same_class(t(6), t(7)));
        assert!(uf.same_class(t(5), t(2)));
        uf.pop_scope();
        assert!(!uf.same_class(t(5), t(1)));
    }

    #[test]
    fn class_member_motion_absorbed_into_kept() {
        let mut uf = ArrayUnionFind::default();
        // Build a rank-1 class {1,2,3} and a rank-0 class {4}.
        uf.union(t(1), t(2), asserted(100));
        uf.union(t(1), t(3), asserted(101));
        let big_root = uf.find(t(1));
        uf.union(t(4), t(1), asserted(102));
        // The lower-rank singleton is absorbed into the bigger class's root.
        assert_eq!(uf.find(t(4)), big_root);
        assert_eq!(uf.merge_log().last(), Some(&(big_root, t(4))));
        let members = uf.class_members(t(4));
        assert_eq!(members.len(), 4);
        // Kept class's members stay in place; absorbed members are appended.
        assert_eq!(members.last(), Some(&t(4)));
    }

    #[test]
    fn proof_forest_edge_recording_asserted_vs_sentinel() {
        let mut uf = ArrayUnionFind::default();
        uf.union(t(1), t(2), asserted(100));
        let child = if uf.find(t(1)) == t(1) { t(2) } else { t(1) };
        let edge = uf.edge(child).expect("absorbed root has an edge");
        assert_eq!((edge.a, edge.b), (t(1), t(2)));
        assert!(edge.just.is_asserted());
        assert_eq!(edge.just, asserted(100));
        // Roots have no edge.
        assert!(uf.edge(uf.find(t(1))).is_none());

        let ext = EqJustification::External {
            key: (t(3), t(4)),
            has_reasons: true,
        };
        uf.union(t(3), t(4), ext);
        let child = if uf.find(t(3)) == t(3) { t(4) } else { t(3) };
        let edge = uf.edge(child).expect("absorbed root has an edge");
        assert!(!edge.just.is_asserted());
        assert_eq!(edge.just, ext);
    }

    #[test]
    fn deterministic_across_rebuild() {
        let edges = [(1u32, 2u32), (3, 4), (2, 3), (5, 6), (6, 1), (7, 8)];
        let build = || {
            let mut uf = ArrayUnionFind::default();
            for (i, &(a, b)) in edges.iter().enumerate() {
                uf.union(t(a), t(b), asserted(100 + i as u32));
            }
            uf
        };
        let uf1 = build();
        let uf2 = build();
        assert_eq!(uf1.merge_log(), uf2.merge_log());
        assert_eq!(uf1.non_singleton_classes(), uf2.non_singleton_classes());
        for n in 1..=8 {
            assert_eq!(uf1.find(t(n)), uf2.find(t(n)));
        }
        // clear() starts a fresh era.
        let mut uf3 = build();
        uf3.clear();
        assert!(uf3.merge_log().is_empty());
        assert!(!uf3.same_class(t(1), t(2)));
        assert!(uf3.non_singleton_classes().is_empty());
    }

    /// The explanation edges, viewed as an undirected relation, must connect
    /// the queried endpoints (transitive closure check).
    fn assert_edges_connect(edges: &[EqEdge], from: TermId, to: TermId) {
        let mut reached = vec![from];
        let mut changed = true;
        while changed && !reached.contains(&to) {
            changed = false;
            for e in edges {
                let has_a = reached.contains(&e.a);
                let has_b = reached.contains(&e.b);
                if has_a && !has_b {
                    reached.push(e.b);
                    changed = true;
                } else if has_b && !has_a {
                    reached.push(e.a);
                    changed = true;
                }
            }
        }
        assert!(
            reached.contains(&to),
            "explanation edges must connect {from:?} to {to:?}: {edges:?}"
        );
    }

    #[test]
    fn explain_connects_endpoints_on_chains_and_diamonds() {
        let mut uf = ArrayUnionFind::default();
        assert_eq!(uf.explain(t(1), t(1)), Some(vec![]));
        assert_eq!(uf.explain(t(1), t(2)), None);

        // Chain 1-2-3-4-5 built out of order, plus a diamond shortcut that is
        // a no-op union (not in the forest).
        uf.union(t(1), t(2), asserted(100));
        uf.union(t(4), t(5), asserted(101));
        uf.union(t(3), t(4), asserted(102));
        uf.union(t(2), t(3), asserted(103));
        assert!(!uf.union(t(1), t(5), asserted(104)));

        for (x, y) in [(1u32, 5u32), (5, 1), (2, 4), (1, 3), (3, 5)] {
            let edges = uf.explain(t(x), t(y)).expect("same class");
            assert_edges_connect(&edges, t(x), t(y));
            // Only recorded (forest) justifications appear.
            assert!(edges.iter().all(|e| e.just != asserted(104)));
        }
        assert_eq!(uf.explain(t(1), t(6)), None);
    }

    #[test]
    fn explain_crosses_class_merges_of_unrelated_endpoints() {
        // Merge two multi-member classes by an edge between non-root members;
        // explaining across it requires the recursive sub-explanations.
        let mut uf = ArrayUnionFind::default();
        uf.union(t(1), t(2), asserted(100));
        uf.union(t(2), t(3), asserted(101));
        uf.union(t(10), t(11), asserted(102));
        uf.union(t(11), t(12), asserted(103));
        uf.union(t(3), t(12), asserted(104)); // bridge between members
        let edges = uf.explain(t(1), t(10)).expect("same class");
        assert_edges_connect(&edges, t(1), t(10));

        // Mixed asserted/external justifications survive the walk.
        let ext = EqJustification::External {
            key: (t(20), t(1)),
            has_reasons: true,
        };
        uf.union(t(20), t(1), ext);
        let edges = uf.explain(t(20), t(10)).expect("same class");
        assert_edges_connect(&edges, t(20), t(10));
        assert!(edges.iter().any(|e| e.just == ext));
    }

    #[test]
    fn explain_soundness_stress() {
        // Randomized: many union sequences; every same-class pair's explanation
        // must (a) use only recorded union edges and (b) connect the endpoints.
        let mut state: u64 = 0x9E3779B97F4A7C15;
        let mut rand = || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        for _ in 0..400 {
            let mut uf = ArrayUnionFind::default();
            let n = 3 + (rand() % 12) as u32;
            let mut recorded: Vec<(TermId, TermId)> = Vec::new();
            let edge_count = 2 + (rand() % 20) as usize;
            for k in 0..edge_count {
                let a = t(1 + (rand() % n as u64) as u32);
                let b = t(1 + (rand() % n as u64) as u32);
                if uf.union(a, b, asserted(1000 + k as u32)) {
                    recorded.push((a, b));
                }
            }
            for x in 1..=n {
                for y in 1..=n {
                    let ex = uf.explain(t(x), t(y));
                    if uf.same_class(t(x), t(y)) {
                        let edges = ex.expect("same class must explain");
                        // (a) every returned edge is a recorded union edge.
                        for e in &edges {
                            assert!(
                                recorded.contains(&(e.a, e.b)) || recorded.contains(&(e.b, e.a)),
                                "explain returned a non-recorded edge {e:?}"
                            );
                        }
                        // (b) the edges connect x to y.
                        assert_edges_connect(&edges, t(x), t(y));
                    } else {
                        assert_eq!(ex, None, "distinct classes must not explain");
                    }
                }
            }
        }
    }

    #[test]
    fn non_singleton_classes_partitions() {
        let mut uf = ArrayUnionFind::default();
        uf.union(t(5), t(9), asserted(100));
        uf.union(t(2), t(3), asserted(101));
        uf.union(t(9), t(7), asserted(102));
        // Touch a singleton via a scoped union then undo it.
        uf.push_scope();
        uf.union(t(11), t(5), asserted(103));
        uf.pop_scope();
        assert_eq!(
            uf.non_singleton_classes(),
            vec![vec![t(2), t(3)], vec![t(5), t(7), t(9)]]
        );
    }
}
