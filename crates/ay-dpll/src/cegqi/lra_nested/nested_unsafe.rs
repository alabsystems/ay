// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! When a counterexample UNSAT of the nested search may be trusted.
//!
//! UNSAFE CHILDREN. Fig. 8 assumes grammar (4): every child of a node
//! occurs in its body with the opposite effective kind, whose approximation
//! errs in the safe direction for Lemma 10.2 (a frozen universal is implied by
//! the truth, a frozen existential implies it). Boolean structure can put a
//! child of the SAME effective kind (`∀x (p ∨ ∀z q)`) or of both polarities
//! (under an iff) in the body; for such a child the parent's `CE` UNSAT means
//! nothing until the child itself is exact, so the parent recurses into it
//! first.
//!
//! STALE CHECKS. An UNSAT is a claim about the approximations it was ASKED
//! with. Nodes are shared by term, so an unsafe child `D` of `A` may also sit
//! below `A`'s other child `C`: the recursion into `C` logs `D`'s instance,
//! and `D` then answers "exact" at once — yet `A`'s UNSAT used `D`'s older,
//! non-exact approximation. So a node's UNSAT is trusted only when none of
//! its unsafe direct children changed between the check and the end of the
//! recursion into them ([`Search::unsafe_ready`]); the main query's UNSAT
//! only when no top node changed since it was built. Otherwise the query is
//! asked again. Each re-ask follows a logged instance, so the caps bound it.

use super::{Progress, Search};
use crate::cegqi::lra_nested::ntree::{Edge, Kind};
use crate::cegqi::lra_nested::{QlraDecline, QlraHost};

impl Search<'_> {
    /// An occurrence whose approximation may err in the direction that
    /// voids the parent's `CE` UNSAT (see the module docs).
    pub(super) fn is_unsafe(&self, parent: usize, edge: Edge) -> bool {
        if edge.pol.both() {
            return true;
        }
        let child = self.tree.nodes[edge.child].kind;
        let relative = match (child, edge.pol.neg) {
            (kind, false) => kind,
            (Kind::Forall, true) => Kind::Exists,
            (Kind::Exists, true) => Kind::Forall,
        };
        relative == self.tree.nodes[parent].kind
    }

    /// The instance counts of `node`'s unsafe direct children: the part of
    /// the state an UNSAT of `CE_node` rests on (see [`Search::unsafe_ready`]).
    pub(super) fn unsafe_marks(&self, node: usize) -> Vec<usize> {
        self.tree.nodes[node]
            .children
            .iter()
            .filter(|edge| self.is_unsafe(node, **edge))
            .map(|edge| self.gamma[edge.child].len())
            .collect()
    }

    /// After an UNSAT of `CE_node` taken when the unsafe children's instance
    /// counts were `marks`: `true` when that UNSAT may be trusted, i.e. every
    /// unsafe direct child is now exact AND none of them changed since the
    /// check, so the approximations the check used were already exact.
    /// `false`: ask `CE_node` again (a child logged, directly or — nodes
    /// being shared by term — through the recursion into a sibling).
    pub(super) fn unsafe_ready(
        &mut self,
        host: &mut dyn QlraHost,
        node: usize,
        marks: &[usize],
    ) -> Result<bool, QlraDecline> {
        Ok(!self.children_first(host, node, false)? && self.unsafe_marks(node) == marks)
    }

    /// Recurse into `node`'s children (`all`, or only the unsafe ones).
    /// `true` as soon as one child logged an instance of its OWN: `node`'s
    /// counterexample formula then changed and must be asked again.
    pub(super) fn children_first(
        &mut self,
        host: &mut dyn QlraHost,
        node: usize,
        all: bool,
    ) -> Result<bool, QlraDecline> {
        let edges = self.tree.nodes[node].children.clone();
        for edge in edges {
            if (all || self.is_unsafe(node, edge))
                && matches!(self.rec(host, edge.child)?, Progress::Logged)
            {
                return Ok(true);
            }
        }
        Ok(false)
    }
}
