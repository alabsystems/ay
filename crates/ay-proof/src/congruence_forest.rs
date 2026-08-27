// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A **proof-producing** congruence closure over a clause's own sub-term DAG.
//!
//! [`super::checker::euf_congruence_explanation`] decides whether a packed EUF
//! explanation clause is valid; it computes a congruence closure and reports
//! only the VERDICT. This module computes the same kind of closure but records
//! WHY each merge happened, so a caller can turn the verdict into an Alethe
//! derivation the pinned external rules already cover.
//!
//! # The proof forest
//!
//! Every merge that actually joins two distinct classes is recorded as an
//! undirected edge between the two nodes that caused it, tagged with its
//! [`MergeReason`]. Because a merge is recorded ONLY when the two classes were
//! distinct, the recorded edges can never close a cycle: the edge set is a
//! FOREST whose trees are exactly the final classes. Two nodes are therefore
//! connected by a UNIQUE path, and that path is the explanation.
//!
//! # Why congruence is restricted to `App`
//!
//! The validator's closure also descends through `Not` and `Ite`. This one
//! does not, deliberately: the only Alethe rule available to justify a
//! congruence step is `eq_congruent`, whose validator
//! ([`super::checker::euf::validate_euf_congruent`]) requires BOTH sides of
//! its conclusion to be `TermData::App` with the same symbol. A `Not`/`Ite`
//! congruence could not be lowered, so deriving it here would only produce a
//! step that fails to validate. Being strictly WEAKER than the validator is
//! the fail-closed direction: a clause whose explanation needs one of those
//! merges is simply not derivable, and its caller keeps the certified lemma.
//!
//! Nothing in this module asserts anything. It proposes a derivation; every
//! step the caller emits from it is re-validated, independently, by the
//! untouched strict checker.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{Sort, Symbol, TermData, TermId, TermStore};

/// Largest sub-term DAG this closure will build. Mirrors the validator's own
/// bound; a larger clause is DECLINED, never derived unchecked.
pub(crate) const MAX_NODES: usize = 4096;

/// Largest number of congruence fixpoint rounds. Every round that changes
/// anything merges at least one pair, so a run needs at most `MAX_NODES` of
/// them.
pub(crate) const MAX_ROUNDS: usize = 256;

/// Why two nodes were merged — the justification an emitted step must carry.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum MergeReason {
    /// The clause's `.0`-th hypothesis equality states it.
    Hypothesis(usize),
    /// The two nodes are applications of the same head whose arguments were
    /// already pairwise equal.
    Congruence,
}

/// A congruence closure that records its merge justifications.
pub(crate) struct CongruenceForest {
    /// The term interned at each node.
    pub(crate) term: Vec<TermId>,
    /// Recorded merges, in the order they were made. Edge `k` connects
    /// `edges[k].0` and `edges[k].1`.
    pub(crate) edges: Vec<(usize, usize, MergeReason)>,
    /// `node -> [(other endpoint, edge index)]`.
    adjacency: Vec<Vec<(usize, usize)>>,
    index: HashMap<TermId, usize>,
    parent: Vec<usize>,
    weight: Vec<usize>,
    /// `None` for a node congruence never descends through.
    head: Vec<Option<usize>>,
    children: Vec<Vec<usize>>,
    heads: HashMap<(Symbol, Sort, usize), usize>,
}

impl CongruenceForest {
    pub(crate) fn new() -> Self {
        Self {
            term: Vec::new(),
            edges: Vec::new(),
            adjacency: Vec::new(),
            index: HashMap::default(),
            parent: Vec::new(),
            weight: Vec::new(),
            head: Vec::new(),
            children: Vec::new(),
            heads: HashMap::default(),
        }
    }

    /// The node interned for `term`, if any.
    pub(crate) fn node_of(&self, term: TermId) -> Option<usize> {
        self.index.get(&term).copied()
    }

    fn head_slot(&mut self, symbol: &Symbol, sort: &Sort, arity: usize) -> usize {
        let next = self.heads.len();
        *self
            .heads
            .entry((symbol.clone(), sort.clone(), arity))
            .or_insert(next)
    }

    /// Intern `root` and every sub-term reachable through an application.
    ///
    /// ITERATIVE on purpose: the measured QF_AX population carries `store`
    /// chains a dozen deep and the recursion depth would otherwise be the
    /// clause author's choice.
    pub(crate) fn add(&mut self, terms: &TermStore, root: TermId) -> Option<usize> {
        if let Some(&id) = self.index.get(&root) {
            return Some(id);
        }
        let mut stack: Vec<(TermId, bool)> = vec![(root, false)];
        while let Some((term, ready)) = stack.pop() {
            if self.index.contains_key(&term) {
                continue;
            }
            let args = match terms.get(term) {
                TermData::App(_, args) => Some(args.clone()),
                _ => None,
            };
            if !ready {
                stack.push((term, true));
                if let Some(args) = &args {
                    for &child in args {
                        if !self.index.contains_key(&child) {
                            stack.push((child, false));
                        }
                    }
                }
                if stack.len() > MAX_NODES {
                    return None;
                }
                continue;
            }
            self.intern_ready(terms, term, args.as_deref())?;
        }
        self.index.get(&root).copied()
    }

    /// Intern one node whose children are already interned.
    fn intern_ready(
        &mut self,
        terms: &TermStore,
        term: TermId,
        args: Option<&[TermId]>,
    ) -> Option<()> {
        if self.term.len() >= MAX_NODES {
            return None;
        }
        let id = self.term.len();
        self.term.push(term);
        self.parent.push(id);
        self.weight.push(1);
        self.adjacency.push(Vec::new());
        match args {
            Some(args) => {
                let symbol = match terms.get(term) {
                    TermData::App(symbol, _) => symbol.clone(),
                    // Unreachable: `args` is `Some` only for an application.
                    _ => return None,
                };
                let sort = terms.sort(term).clone();
                let head = self.head_slot(&symbol, &sort, args.len());
                let mut children = Vec::with_capacity(args.len());
                for arg in args {
                    // The interned term DAG is acyclic and every child was
                    // interned before this node was re-visited, so a miss is
                    // impossible; failing closed is the only safe answer to
                    // one.
                    children.push(*self.index.get(arg)?);
                }
                self.head.push(Some(head));
                self.children.push(children);
            }
            None => {
                self.head.push(None);
                self.children.push(Vec::new());
            }
        }
        self.index.insert(term, id);
        Some(())
    }

    fn find(&mut self, mut id: usize) -> usize {
        while self.parent[id] != id {
            self.parent[id] = self.parent[self.parent[id]];
            id = self.parent[id];
        }
        id
    }

    /// Merge the classes of `a` and `b`, RECORDING the reason when the merge
    /// actually joins two distinct classes. Returns `true` in that case.
    ///
    /// The recorded edge is what makes the forest a forest: a merge of two
    /// nodes already in one class adds no edge, so no cycle can form.
    pub(crate) fn merge(&mut self, a: usize, b: usize, reason: MergeReason) -> bool {
        let (mut ra, mut rb) = (self.find(a), self.find(b));
        if ra == rb {
            return false;
        }
        if self.weight[ra] > self.weight[rb] {
            std::mem::swap(&mut ra, &mut rb);
        }
        self.parent[ra] = rb;
        self.weight[rb] += self.weight[ra];
        let edge = self.edges.len();
        self.edges.push((a, b, reason));
        self.adjacency[a].push((b, edge));
        self.adjacency[b].push((a, edge));
        true
    }

    /// Close the current classes under congruence, recording every merge.
    ///
    /// Returns `false` when the fixpoint is not reached inside `MAX_ROUNDS`
    /// (fail closed: the caller derives nothing).
    pub(crate) fn close(&mut self) -> bool {
        for _round in 0..MAX_ROUNDS {
            let mut table: HashMap<(usize, Vec<usize>), usize> = HashMap::default();
            let mut changed = false;
            for id in 0..self.term.len() {
                let Some(head) = self.head[id] else {
                    continue;
                };
                let mut signature = Vec::with_capacity(self.children[id].len());
                for offset in 0..self.children[id].len() {
                    let child = self.children[id][offset];
                    signature.push(self.find(child));
                }
                match table.get(&(head, signature.clone())) {
                    Some(&other) => {
                        if self.merge(id, other, MergeReason::Congruence) {
                            changed = true;
                        }
                    }
                    None => {
                        table.insert((head, signature), id);
                    }
                }
            }
            if !changed {
                return true;
            }
        }
        false
    }

    /// The edges of the unique forest path from `from` to `to`, in path order.
    ///
    /// `None` when the two nodes are in different classes. An empty result
    /// means they are the SAME node.
    pub(crate) fn explain(&self, from: usize, to: usize) -> Option<Vec<usize>> {
        if from == to {
            return Some(Vec::new());
        }
        let mut previous: Vec<Option<(usize, usize)>> = vec![None; self.term.len()];
        let mut seen = vec![false; self.term.len()];
        let mut queue = std::collections::VecDeque::new();
        seen[from] = true;
        queue.push_back(from);
        while let Some(node) = queue.pop_front() {
            if node == to {
                break;
            }
            for &(next, edge) in &self.adjacency[node] {
                if !seen[next] {
                    seen[next] = true;
                    previous[next] = Some((node, edge));
                    queue.push_back(next);
                }
            }
        }
        if !seen[to] {
            return None;
        }
        let mut path = Vec::new();
        let mut current = to;
        while current != from {
            let (parent, edge) = previous[current]?;
            path.push(edge);
            current = parent;
        }
        path.reverse();
        Some(path)
    }
}
