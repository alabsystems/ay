// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Explanations from the proof forest (design §3.7, H1).
//!
//! Two nodes of one class are joined by a unique path in their proof tree.
//! Each edge on it is an assigned literal, a congruence (explained by the
//! arguments' paths, recursively) or an equality made true by its arguments.
//! A path, once it exists, never changes until a pop removes one of its
//! edges, so an explanation asked for late (a lazy reason during conflict
//! analysis) uses only literals that were assigned when the equality was
//! first derived.

use ay_core::TheoryLit;

use super::transitivity::PathEdge;
use super::{Hub, Just, NodeId};

impl Hub {
    /// The literals that make `a` and `b` equal. Deduplicated; every literal
    /// is currently true. `None` when the two do not share a class (a caller
    /// bug: the kernel fails closed on it).
    ///
    /// KC9: the literals are in the order of their nodes, which follows the
    /// canonical (content) order nodes are created in, never `TermId` order.
    pub(crate) fn explain(&mut self, a: NodeId, b: NodeId) -> Option<Vec<TheoryLit>> {
        self.explain_epoch = self.explain_epoch.wrapping_add(1).max(1);
        let epoch = self.explain_epoch;
        let mut lits: Vec<(NodeId, bool)> = Vec::new();
        let mut todo: Vec<(NodeId, NodeId)> = vec![(a, b)];
        while let Some((x, y)) = todo.pop() {
            if x == y {
                continue;
            }
            if self.root(x) != self.root(y) {
                return None;
            }
            let lca = self.lca(x, y);
            let recording = self.dack.recording;
            let mut sides: [Vec<PathEdge>; 2] = [Vec::new(), Vec::new()];
            for (side, start) in sides.iter_mut().zip([x, y]) {
                let mut n = start;
                while n != lca {
                    let idx = Self::idx(n);
                    let target = self.nodes[idx].target?;
                    if recording {
                        let just = self.nodes[idx].just;
                        side.push(PathEdge {
                            from: n,
                            to: target,
                            just,
                        });
                    }
                    if self.edge_mark[idx] != epoch {
                        self.edge_mark[idx] = epoch;
                        self.explain_edge(n, target, &mut lits, &mut todo);
                    }
                    n = target;
                }
            }
            if recording {
                self.note_path(&sides[0], &sides[1]);
            }
        }
        lits.sort_unstable();
        lits.dedup();
        Some(
            lits.into_iter()
                .map(|(n, value)| TheoryLit::new(self.term(n), value))
                .collect(),
        )
    }

    fn explain_edge(
        &self,
        n: NodeId,
        target: NodeId,
        lits: &mut Vec<(NodeId, bool)>,
        todo: &mut Vec<(NodeId, NodeId)>,
    ) {
        match self.node(n).just {
            Just::Lit(node, value) => lits.push((node, value)),
            Just::Congruence { crossed } => {
                let (xs, ys) = (&self.node(n).args, &self.node(target).args);
                if crossed {
                    // Commutative congruence of `=`: the sides matched
                    // crosswise when it was found.
                    todo.extend(xs.iter().copied().zip(ys.iter().rev().copied()));
                } else {
                    todo.extend(xs.iter().copied().zip(ys.iter().copied()));
                }
            }
            Just::EqTrue(eq) => {
                if let Some((x, y)) = self.eq_args(eq) {
                    todo.push((x, y));
                }
            }
            Just::Root => debug_assert!(false, "a proof edge without a justification"),
        }
    }

    /// The nearest common ancestor of two nodes of one proof tree.
    fn lca(&mut self, x: NodeId, y: NodeId) -> NodeId {
        self.lca_epoch = self.lca_epoch.wrapping_add(1).max(1);
        let mark = self.lca_epoch;
        let mut n = x;
        loop {
            self.lca_mark[Self::idx(n)] = mark;
            match self.node(n).target {
                Some(t) => n = t,
                None => break,
            }
        }
        let mut m = y;
        loop {
            if self.lca_mark[Self::idx(m)] == mark {
                return m;
            }
            match self.node(m).target {
                Some(t) => m = t,
                None => return m,
            }
        }
    }
}
