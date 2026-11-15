// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! CASE SPLITTING ON GUARDS: a refutation of a circuit whose root forces
//! GUARDED facts — a disjunction such as `(or (not g) fact)`, or a defined
//! word's guarded equality, with nothing in it yet true — as a decision tree
//! over those guards, each leaf refuted over what its case leaves in force.
//!
//! ## Why this exists
//!
//! external-codegen's lowered queries spell a partial operator by cases:
//! `f2i(i2f(a))` becomes `t0 = ite(a's leading one is at 53, …, ite(… at
//! 0, …))` and, per exponent `e` of `t0`, `(or (not (= exp(t0) e)) (= t1
//! decode_e(t0)))`. The theorem `a = t1` holds case by case, and in each
//! case it is a small identity; no single CDCL search and no sweep sees
//! that. Measured 2026-09-30 on proof_gate_strict row 1257 (`i64 → f64 →
//! i64`): the strict checker's monolithic refutation passed its 32 MiB
//! output cap and its sweep spent its 200,000 conflicts without closing, and
//! the query ended at its 120 s timeout; split, the checker admits the lemma
//! in about 4 s and the printer's document is 63 MB.
//!
//! ## What it does
//!
//! At each node, unit propagation over the pool (`pool.rs`) under the
//! node's path, then what the node must still refute (`relevance.rs`): the
//! clauses in force that can still constrain the roots. Of the
//! disjunctions among them that no other one lies above, the node splits on
//! the literal with the smallest cone — first false, which forces the rest
//! of its disjunction, then true. A node with none is a leaf, refuted over
//! its core (`leaf.rs`): the clauses no case can do without (`prune.rs`),
//! with the wiring its values leave between equal literals collapsed, swept
//! when its gates line up (`core_sweep.rs`) and searched otherwise. A node
//! propagation alone refutes needs neither.
//!
//! ## Why the result is a refutation of the SAME CNF
//!
//! Every step is an ordinary RUP step over the CNF's own clauses and
//! earlier steps, widened by the negation of the path it was derived under
//! and recorded as the resolvent its chain actually derives: a propagated
//! value from its reason, a conflict from its clause and values, a leaf's
//! refutation stitched as the sweep stitches a lemma, and each internal
//! node's clause by resolving its two children's clauses on the split
//! literal. A child whose clause does not mention its case literal already
//! closes the parent, and the other child is never visited. Nothing about
//! the search is trusted: the caller replays the whole DAG.

use super::*;

mod core_sweep;
mod implications;
mod leaf;
pub(super) mod node;
mod pool;
mod prune;
mod relevance;
#[cfg(test)]
mod tests;
mod units;

use node::{Propagated, Up};
pub(crate) use pool::Definition;
use pool::Pool;

/// Conflicts one leaf's refutation may spend. Measured on row 1257: every
/// exponent's leaf closed within 220.
const LEAF_CONFLICTS: u64 = 5_000;
/// Deepest path a split follows (the widened units index it by bit).
const MAX_DEPTH: usize = 128;
/// Nodes a split visits at most: each is a propagation over the whole pool.
/// Row 1257's split visits about 300.
const MAX_NODES: usize = 4_096;

/// Leaf cores at most this large are refuted where a [`Leaves::Small`]
/// split meets them.
///
/// Measured 2026-10-01 (load average ~100 on 18 cores): proof_gate_strict
/// row 1257's leaves have cores of 4 to 1,537 variables (median 124), each a
/// small identity. external-codegen's 64-bit `SDIV`/`IDIV` definitional rows 0300,
/// 0311 and 1375 split on the dividend's sign into a leaf that keeps a whole
/// 64-bit divider, 26,083 to 26,582 variables, whose core sweep declined
/// after 15 to 30 s (0300's at the split's 30 s wall), while the sweep of the
/// whole circuit, both dividers, refuted it in 6 to 8 s.
pub(crate) const SMALL_LEAF_VARS: usize = 8_192;

/// Which leaves a split refutes where it meets them.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Leaves {
    /// Every leaf.
    All,
    /// A leaf whose core has at most [`SMALL_LEAF_VARS`] variables. The
    /// first larger one ends the split as [`Outcome::deferred`]: a caller
    /// with the sweep of the whole circuit to try sweeps first, and splits
    /// over every leaf only if that does not refute it.
    Small,
}

/// What a split did.
pub(crate) struct Outcome {
    /// The refutation, or `None`.
    pub(crate) refutation: Option<ResolutionDag>,
    /// The conflicts its solver calls spent.
    pub(crate) spent: u64,
    /// The literals its candidate attempts read (`work.rs`).
    pub(crate) worked: u64,
    /// It ended at a leaf [`Leaves::Small`] does not refute.
    pub(crate) deferred: bool,
}

/// A refutation of `cnf` by splitting on the guards its roots leave open,
/// or `None` — also when no guard is open, where splitting cannot help —
/// with the conflicts its solver calls spent either way.
pub(crate) fn refute(
    gates: Vec<Gate>,
    cnf: &[Vec<Literal>],
    roots: &[usize],
    transport_root: bool,
    definitions: &[Definition],
    implied: &[usize],
    leaves: Leaves,
    limits: SweepLimits,
    keep_going: &mut dyn FnMut() -> bool,
) -> Outcome {
    let Some(mut sweep) = Sweep::new(gates, cnf, roots, transport_root, limits, keep_going) else {
        return Outcome {
            refutation: None,
            spent: 0,
            worked: 0,
            deferred: false,
        };
    };
    if leaves == Leaves::Small {
        sweep.largest_leaf = SMALL_LEAF_VARS;
    }
    sweep.split(definitions, implied, limits)
}

impl Sweep<'_, '_> {
    fn split(
        mut self,
        definitions: &[Definition],
        implied: &[usize],
        limits: SweepLimits,
    ) -> Outcome {
        let refutation = self.split_refutation(definitions, implied);
        let spent = self.spent(limits);
        Outcome {
            refutation,
            spent: spent.conflicts,
            worked: spent.work,
            deferred: self.deferred_leaf,
        }
    }

    fn split_refutation(
        &mut self,
        definitions: &[Definition],
        implied: &[usize],
    ) -> Option<ResolutionDag> {
        let mut pool = self.pool(definitions, implied);
        let Up::Settled(root) = self.propagate(&pool, &[]) else {
            // A root refuted by propagation alone needs no split, and the
            // monolithic refutation finds it at once.
            return None;
        };
        let relevant = self.relevance(&pool, &root);
        let guard = self.open_guard(&pool, &root, &relevant);
        guard?;
        drop((root, relevant));
        let empty = self.split_node(&mut pool, &mut Vec::new())?;
        if !self.clause_of(empty)?.is_empty() {
            return None;
        }
        self.inline_degenerate_final()?;
        let derived = close::reachable(std::mem::take(&mut self.derived), &self.derived_at, empty);
        Some(ResolutionDag {
            num_vars: self.nodes.len(),
            original_clauses: self
                .cnf
                .iter()
                .enumerate()
                .map(|(index, clause)| (index as u64 + 1, clause.clone()))
                .collect(),
            derived,
            empty_clause_id: empty,
        })
    }

    /// The clause refuting `path` (a subset of its negation), or `None`.
    fn split_node(&mut self, pool: &mut Pool, path: &mut Vec<Literal>) -> Option<u64> {
        // The split asks the sweep for no lemma; its count is the nodes.
        self.lemma_calls += 1;
        if path.len() > MAX_DEPTH || self.lemma_calls > MAX_NODES || self.out_of_budget() {
            return None;
        }
        let prop = match self.propagate(pool, path) {
            Up::Conflict(conflict) => {
                let (clause, state) = conflict?;
                return self.refute_by_propagation(pool, &state, path, clause);
            }
            Up::Settled(prop) => prop,
        };
        let mark = pool.len();
        let refuted = self.split_settled(pool, path, prop);
        pool.truncate(mark);
        refuted
    }

    fn split_settled(
        &mut self,
        pool: &mut Pool,
        path: &mut Vec<Literal>,
        mut prop: Propagated,
    ) -> Option<u64> {
        let relevant = self.relevance(pool, &prop);
        if let Some(guard) = self.open_guard(pool, &prop, &relevant) {
            drop((prop, relevant));
            return self.split_on(pool, path, guard);
        }
        if let Some(id) = self.refute_leaf(pool, &prop, path, &relevant, LEAF_CONFLICTS) {
            return Some(id);
        }
        if self.deferred_leaf {
            return None;
        }
        // The leaf over everything in force, uncompressed: every value its
        // clauses mention as a widened unit, and one solver call.
        self.derive_units(pool, &mut prop, path, &relevant)?;
        let local = self.relevant_local(pool, &prop, path, &relevant);
        drop((prop, relevant));
        let widen: Vec<Literal> = path.iter().map(|lit| lit.negated()).collect();
        match self.solve(local.global.len(), &local.clauses, LEAF_CONFLICTS)? {
            ResolutionSolveOutcome::Unsat(dag) => self.stitch(&local, &dag, &widen),
            ResolutionSolveOutcome::Sat(_) => None,
        }
    }

    /// Both cases of `guard`: false first (its disjunction's other operands
    /// must then hold), then true.
    fn split_on(
        &mut self,
        pool: &mut Pool,
        path: &mut Vec<Literal>,
        guard: Literal,
    ) -> Option<u64> {
        let widen: Vec<Literal> = path.iter().map(|lit| lit.negated()).collect();
        let (first_case, second_case) = (guard.negated(), guard);
        path.push(first_case);
        let first = self.split_node(pool, path);
        path.pop();
        let first = first?;
        if !self.clause_of(first)?.contains(&second_case) {
            return Some(first);
        }
        path.push(second_case);
        let second = self.split_node(pool, path);
        path.pop();
        let second = second?;
        if !self.clause_of(second)?.contains(&first_case) {
            return Some(second);
        }
        self.record_chain(&widen, &[first, second])
    }
}
