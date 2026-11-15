// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Dynamic transitivity lemmas (z3's `dack_eq`, "dynamic Ackermannization"
//! for equalities).
//!
//! A conflict explained through a chain `a = b`, `b = c` of asserted
//! equalities can be re-derived along exponentially many paths when no atom
//! names `a = c` (the `eq_diamond` family: `2^n` paths through `n`
//! diamonds, every one a separate conflict). When two such literals are
//! adjacent on an explanation path in conflicts often enough, the kernel
//! adds the T-valid lemma `¬(a = b) ∨ ¬(b = c) ∨ (a = c)` over a minted
//! `a = c`, which the hub then watches: later conflicts are explained
//! through the new atom, and resolution can learn short clauses over it.
//!
//! Counting is a heuristic and survives backtracking (node ids are never
//! reused). The lemma is EUF-valid whatever the assignment (K4).

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{TermId, TheoryLit};

use super::{Hub, Just, NodeId};

/// Conflicts a pair must appear in before its lemma is added.
const THRESHOLD: u32 = 2;
/// Lemmas one check may add.
const BUDGET: usize = 50_000;

/// One edge of an explanation path, oriented along the path.
#[derive(Debug, Clone, Copy)]
pub(super) struct PathEdge {
    pub(super) from: NodeId,
    pub(super) to: NodeId,
    pub(super) just: Just,
}

/// A transitivity lemma to add: `¬first ∨ ¬second ∨ (= a b)`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct TransitivityLemma {
    pub(crate) a: NodeId,
    pub(crate) b: NodeId,
    pub(crate) first: TheoryLit,
    pub(crate) second: TheoryLit,
}

/// The counters (see the module docs).
#[derive(Debug, Default)]
pub(super) struct Transitivity {
    /// Count the explanations made while this is on (conflicts and the
    /// reasons conflict analysis asks for).
    pub(super) recording: bool,
    counts: HashMap<(NodeId, NodeId), u32>,
    done: HashSet<(NodeId, NodeId)>,
    out: Vec<TransitivityLemma>,
}

impl Hub {
    /// Count explanations from now on (`true`) or stop (`false`).
    pub(crate) fn record_transitivity(&mut self, on: bool) {
        self.dack.recording = on;
    }

    /// The transitivity lemmas due since the last call.
    pub(crate) fn take_transitivity(&mut self) -> Vec<TransitivityLemma> {
        std::mem::take(&mut self.dack.out)
    }

    /// An asserted equality between two non-Boolean nodes: the edge's
    /// literal.
    fn equality_lit(&self, edge: &PathEdge) -> Option<TermId> {
        match edge.just {
            Just::Lit(node, true)
                if !self.node(edge.from).is_bool && !self.node(edge.to).is_bool =>
            {
                Some(self.term(node))
            }
            _ => None,
        }
    }

    /// Count every two adjacent asserted equalities of one explanation path
    /// (`side_x` from `x` up to the common ancestor, `side_y` from `y` up to
    /// it).
    pub(super) fn note_path(&mut self, side_x: &[PathEdge], side_y: &[PathEdge]) {
        let path: Vec<PathEdge> = side_x
            .iter()
            .copied()
            .chain(side_y.iter().rev().map(|e| PathEdge {
                from: e.to,
                to: e.from,
                just: e.just,
            }))
            .collect();
        for pair in path.windows(2) {
            let (Some(first), Some(second)) =
                (self.equality_lit(&pair[0]), self.equality_lit(&pair[1]))
            else {
                continue;
            };
            let (a, b) = (pair[0].from, pair[1].to);
            if a == b {
                continue;
            }
            let key = (a.min(b), a.max(b));
            if self.dack.done.contains(&key) || self.dack.done.len() >= BUDGET {
                continue;
            }
            let count = self.dack.counts.entry(key).or_insert(0);
            *count += 1;
            if *count >= THRESHOLD {
                self.dack.done.insert(key);
                self.dack.out.push(TransitivityLemma {
                    a,
                    b,
                    first: TheoryLit::new(first, true),
                    second: TheoryLit::new(second, true),
                });
            }
        }
    }
}
