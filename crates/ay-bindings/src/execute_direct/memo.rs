// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

//! Scope-truncated per-node tables keyed by allocation identity.
//!
//! [`Expr`] is an `Arc`-shared DAG. A table keyed by node IDENTITY visits each
//! distinct node once, where a walk of the unfolded tree can be exponential in
//! the DAG's depth. Two tables use it:
//!
//! * the Expr-to-Term translation memo ([`TranslationMemo`]), so a DAG-shaped
//!   assertion lowers once per node and a node shared by many assertions of one
//!   session lowers once per session;
//! * the Merkle digests of a session's live scope (`digest.rs`).
//!
//! A node's identity is the PAIR of its value and sort allocations
//! ([`node_key`]): an `Expr` and its clones share both, and a value paired
//! with a different sort is a different entry, so no entry ever stands for two
//! different terms. Every entry keeps its key's allocations alive, so an
//! address it is keyed by cannot be freed and reused for a different node
//! while the entry exists.
//!
//! Every insert made while a scope is open is logged with the entry it
//! replaced, and a `pop` undoes the scope's inserts in reverse order —
//! removing a new key, restoring a replaced one — so nothing a popped scope
//! did survives it, by construction rather than by an argument about which
//! inserts can happen. The tables' size follows the live stack, not the
//! session's history.

use std::collections::HashMap;
use std::hash::Hash;
use std::sync::Arc;

use ay_dpll::api::Term;

use crate::expr::Expr;
use crate::sort::Sort;

/// Identity of a node: the addresses of its shared value and sort
/// allocations.
pub(super) type NodeKey = (usize, usize);

pub(super) fn sort_key(sort: &Sort) -> usize {
    std::ptr::from_ref(sort.inner()).cast::<()>() as usize
}

pub(super) fn node_key(expr: &Expr) -> NodeKey {
    (
        Arc::as_ptr(&expr.value).cast::<()>() as usize,
        sort_key(expr.sort()),
    )
}

/// An identity-keyed table whose entries are scoped like the assertion stack.
/// `Keep` is what pins the key's allocations (the `Expr` or `Sort` itself).
#[derive(Debug)]
pub(super) struct ScopedTable<K, Keep, V> {
    entries: HashMap<K, (Keep, V)>,
    /// One record per insert made inside an open scope: the key and the
    /// entry it replaced. Inserts at depth 0 are never undone, so they are
    /// not logged.
    log: Vec<(K, Option<(Keep, V)>)>,
    marks: Vec<usize>,
}

impl<K: Copy + Eq + Hash, Keep, V: Copy> ScopedTable<K, Keep, V> {
    pub(super) fn new() -> Self {
        Self {
            entries: HashMap::new(),
            log: Vec::new(),
            marks: Vec::new(),
        }
    }

    pub(super) fn get(&self, key: &K) -> Option<V> {
        self.entries.get(key).map(|(_, value)| *value)
    }

    pub(super) fn insert(&mut self, key: K, keep: Keep, value: V) {
        let replaced = self.entries.insert(key, (keep, value));
        if !self.marks.is_empty() {
            self.log.push((key, replaced));
        }
    }

    pub(super) fn push(&mut self) {
        self.marks.push(self.log.len());
    }

    pub(super) fn pop(&mut self) {
        let Some(mark) = self.marks.pop() else {
            return;
        };
        while self.log.len() > mark {
            let Some((key, replaced)) = self.log.pop() else {
                break;
            };
            match replaced {
                Some(entry) => {
                    self.entries.insert(key, entry);
                }
                None => {
                    self.entries.remove(&key);
                }
            }
        }
    }

    pub(super) fn len(&self) -> usize {
        self.entries.len()
    }
}

/// Expr-to-Term translation memo (#session-translation-memo).
///
/// Consulted only while no binder overlay is active: under a quantifier or a
/// `define-fun` body a `Var` resolves to a bound term, so the same node can
/// lower differently there. Outside binders a node's translation depends only
/// on the declarations it names, and a declaration is never re-bound
/// (`try_get_or_declare` returns the existing symbol or refuses), so a memo
/// hit is exactly the term a fresh translation would build.
#[derive(Debug)]
pub(super) struct TranslationMemo {
    table: ScopedTable<NodeKey, Expr, Term>,
}

impl TranslationMemo {
    pub(super) fn new() -> Self {
        Self {
            table: ScopedTable::new(),
        }
    }

    pub(super) fn get(&self, expr: &Expr) -> Option<Term> {
        self.table.get(&node_key(expr))
    }

    pub(super) fn insert(&mut self, expr: &Expr, term: Term) {
        self.table.insert(node_key(expr), expr.clone(), term);
    }

    pub(super) fn push(&mut self) {
        self.table.push();
    }

    pub(super) fn pop(&mut self) {
        self.table.pop();
    }

    /// Distinct nodes currently memoized, for the linearity tests.
    pub(super) fn len(&self) -> usize {
        self.table.len()
    }
}

#[cfg(test)]
mod tests {
    use super::ScopedTable;

    #[test]
    fn a_pop_restores_an_entry_its_scope_replaced() {
        let mut table: ScopedTable<u32, (), u32> = ScopedTable::new();
        table.insert(1, (), 10);
        table.push();
        table.insert(1, (), 11);
        table.insert(2, (), 20);
        assert_eq!((table.get(&1), table.get(&2)), (Some(11), Some(20)));
        table.pop();
        assert_eq!((table.get(&1), table.get(&2)), (Some(10), None));
    }

    #[test]
    fn nested_scopes_unwind_in_order() {
        let mut table: ScopedTable<u32, (), u32> = ScopedTable::new();
        table.push();
        table.insert(1, (), 1);
        table.push();
        table.insert(1, (), 2);
        table.pop();
        assert_eq!(table.get(&1), Some(1));
        table.pop();
        assert_eq!(table.get(&1), None);
        assert_eq!(table.len(), 0);
    }
}
