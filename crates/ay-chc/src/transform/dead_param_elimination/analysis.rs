// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Liveness of predicate argument positions (DR-CHC-DPE-UNION-FIND-20261118).
//!
//! Liveness is reachability in an undirected graph whose nodes are argument
//! positions: two positions of one clause are linked when their arguments
//! share a variable, and a position is a SEED when its argument is not a plain
//! variable, mentions a constraint variable, or joins two distinct body
//! positions. A position is live iff its connected component holds a seed, so
//! the closure is a union-find over dense position ids: each clause unions
//! every occurrence of a variable with that variable's first occurrence (one
//! hash per occurrence, not one per position pair).
//!
//! Variables are collected with the exact DAG walk, which has no depth
//! cut-off: a variable reachable only below `MAX_EXPR_RECURSION_DEPTH` still
//! seeds and links, so a really live position is never dropped.
//!
//! Each distinct inner node is walked at most once per clause, even when many
//! argument positions share it. Skipping a repeat is exact: only non-variable
//! arguments are walked, and they are seeds, so the earlier walk already linked
//! every variable below the node to a seeded position, and a repeat could only
//! join further seeds to that live component.

use super::DeadParamEliminator;
use crate::expr::dag::{has_children, walk_distinct_preorder, Step};
use crate::{ChcExpr, ChcProblem, ChcVar, PredicateId};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};

/// Live argument positions, indexed by dense position id
/// (`offset[predicate] + position`).
pub(super) struct LivePositions {
    /// `offsets[i]` is the first id of the predicate with index `i`;
    /// `offsets[predicates]` is the total number of positions.
    offsets: Vec<u32>,
    live: Vec<bool>,
}

impl LivePositions {
    /// Whether argument `pos` of `pred` is live. Asserts that `pred` is
    /// declared and `pos` is within its arity.
    pub(super) fn is_live(&self, pred: PredicateId, pos: usize) -> bool {
        self.live[self.id(pred, pos) as usize]
    }

    fn id(&self, pred: PredicateId, pos: usize) -> u32 {
        let index = pred.index();
        assert!(
            index + 1 < self.offsets.len(),
            "dead-param-elim: predicate {pred} is not declared"
        );
        let (start, end) = (self.offsets[index], self.offsets[index + 1]);
        let arity = (end - start) as usize;
        assert!(
            pos < arity,
            "dead-param-elim: position {pos} out of arity {arity} of predicate {pred}"
        );
        // pos < arity <= u32::MAX, checked above.
        start + pos as u32
    }
}

/// Union-find over dense ids (union by size, path halving).
struct UnionFind {
    parent: Vec<u32>,
    size: Vec<u32>,
}

impl UnionFind {
    fn new(n: u32) -> Self {
        Self {
            parent: (0..n).collect(),
            size: vec![1; n as usize],
        }
    }

    fn find(&mut self, mut x: u32) -> u32 {
        while self.parent[x as usize] != x {
            let grandparent = self.parent[self.parent[x as usize] as usize];
            self.parent[x as usize] = grandparent;
            x = grandparent;
        }
        x
    }

    fn union(&mut self, a: u32, b: u32) {
        let (mut ra, mut rb) = (self.find(a), self.find(b));
        if ra == rb {
            return;
        }
        if self.size[ra as usize] < self.size[rb as usize] {
            std::mem::swap(&mut ra, &mut rb);
        }
        self.parent[rb as usize] = ra;
        self.size[ra as usize] += self.size[rb as usize];
    }
}

/// Per-clause occurrence index, reused across clauses.
#[derive(Default)]
struct ClauseScan<'a> {
    /// Variables of the clause constraint.
    constraint_vars: FxHashSet<&'a ChcVar>,
    /// Each variable's first position in the clause.
    first: FxHashMap<&'a ChcVar, u32>,
    /// Each variable's first BODY position in the clause.
    body_first: FxHashMap<&'a ChcVar, u32>,
    /// Inner nodes already walked from some argument of the clause.
    walked: FxHashSet<*const ChcExpr>,
}

impl<'a> ClauseScan<'a> {
    fn clear(&mut self) {
        self.constraint_vars.clear();
        self.first.clear();
        self.body_first.clear();
        self.walked.clear();
    }

    /// Record the argument `arg` at position `pid`: seed it when it is not a
    /// plain variable, then record each of its variables' occurrences,
    /// skipping inner nodes an earlier argument of the clause already walked
    /// (exact, see the module doc).
    fn position(
        &mut self,
        pid: u32,
        arg: &'a ChcExpr,
        is_body: bool,
        uf: &mut UnionFind,
        seed: &mut [bool],
    ) {
        // The common plain-variable argument skips the walk (and its stack
        // allocation): a wide transition has one such argument per position.
        if let ChcExpr::Var(var) = arg {
            self.occurrence(pid, var, is_body, uf, seed);
            return;
        }
        seed[pid as usize] = true;
        walk_distinct_preorder(arg, |node| {
            if has_children(node) && !self.walked.insert(std::ptr::from_ref(node)) {
                return Step::Skip;
            }
            if let ChcExpr::Var(var) = node {
                self.occurrence(pid, var, is_body, uf, seed);
            }
            Step::Descend
        });
    }

    /// Record that `var` occurs at position `pid`: seed the position when
    /// `var` is a constraint variable, union it with `var`'s first position,
    /// and, for a body position, seed it and the earlier body position when
    /// `var` already appeared at a different body position.
    fn occurrence(
        &mut self,
        pid: u32,
        var: &'a ChcVar,
        is_body: bool,
        uf: &mut UnionFind,
        seed: &mut [bool],
    ) {
        if self.constraint_vars.contains(var) {
            seed[pid as usize] = true;
        }
        match self.first.get(var) {
            Some(&first) => uf.union(first, pid),
            None => {
                self.first.insert(var, pid);
            }
        }
        if is_body {
            match self.body_first.get(var) {
                Some(&first) if first != pid => {
                    seed[first as usize] = true;
                    seed[pid as usize] = true;
                }
                Some(_) => {}
                None => {
                    self.body_first.insert(var, pid);
                }
            }
        }
    }
}

impl DeadParamEliminator {
    /// Compute the live argument positions of every predicate.
    ///
    /// A cooperative stop request (polled once per clause) answers "every
    /// position is live", so elimination removes nothing — always sound.
    pub(super) fn compute_live_positions(&self, problem: &ChcProblem) -> LivePositions {
        let mut offsets = Vec::with_capacity(problem.predicates().len() + 1);
        let mut total = 0u32;
        for (index, pred) in problem.predicates().iter().enumerate() {
            assert_eq!(
                pred.id.index(),
                index,
                "dead-param-elim: predicate ids are dense"
            );
            offsets.push(total);
            total = u32::try_from(pred.arity())
                .ok()
                .and_then(|arity| total.checked_add(arity))
                .expect("dead-param-elim: position count fits u32");
        }
        offsets.push(total);
        let mut result = LivePositions {
            offsets,
            live: vec![true; total as usize],
        };

        let mut uf = UnionFind::new(total);
        let mut seed = vec![false; total as usize];
        let mut scan = ClauseScan::default();
        for clause in problem.clauses() {
            if ay_core::resource::check_stop_requested() {
                return result;
            }
            scan.clear();
            if let Some(constraint) = clause.body.constraint.as_ref() {
                walk_distinct_preorder(constraint, |node| {
                    if let ChcExpr::Var(var) = node {
                        scan.constraint_vars.insert(var);
                    }
                    Step::Descend
                });
            }
            for (pred, args) in &clause.body.predicates {
                for (pos, arg) in args.iter().enumerate() {
                    let pid = result.id(*pred, pos);
                    scan.position(pid, arg, true, &mut uf, &mut seed);
                }
            }
            if let crate::ClauseHead::Predicate(pred, args) = &clause.head {
                for (pos, arg) in args.iter().enumerate() {
                    let pid = result.id(*pred, pos);
                    scan.position(pid, arg, false, &mut uf, &mut seed);
                }
            }
        }

        let mut root_live = vec![false; total as usize];
        for pid in 0..total {
            if seed[pid as usize] {
                root_live[uf.find(pid) as usize] = true;
            }
        }
        for pid in 0..total {
            result.live[pid as usize] = root_live[uf.find(pid) as usize];
        }
        result
    }
}
