// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Global hash-cons (interning) table for `ChcExpr` — fast-core rewrite P1.
//!
//! See the development design notes. This module is
//! the keystone component: a single GLOBAL, sharded, concurrent table that maps
//! a freshly-built node to a canonical `Arc<ChcExpr>`, so that structurally
//! equal subterms share one allocation.
//!
//! ## The Decoupling invariant (soundness)
//! `intern(node)` ALWAYS returns an `Arc` that is structurally `== node`.
//! Interning only changes *which* `Arc` is returned (and thus how much sharing /
//! how often `Arc::ptr_eq` succeeds) — never the structural value. Correctness
//! therefore never depends on interning being applied: any node built without
//! interning is still compared 100% structurally. This module adds NO new
//! axiom to the solver; it is a performance layer only.
//!
//! ## Global, not thread-local
//! The portfolio runs engines on multiple threads and passes `ChcExpr` across
//! channels, so canonical pointers must be valid across all lanes (a
//! thread-local table would make `ptr_eq` meaningless cross-thread). The table
//! is `[RwLock<Shard>; SHARDS]`; `Arc<ChcExpr>` is `Send + Sync`.
//!
//! ## Memory
//! The table holds `Weak` references with lazy cleanup on probe, so it adds NO
//! work to the (hot) `Drop` path and can never keep a node alive. A recycled
//! address can never produce a false match: `Weak::upgrade` returns `None` for
//! a dead node, and a live upgrade is always re-validated with structural `==`.

#![allow(dead_code)] // wired into constructors in a follow-up P1 commit

use std::sync::{Arc, OnceLock, RwLock, Weak};

use rustc_hash::FxHashMap;

use super::ChcExpr;

/// Number of lock shards (power of two; selected by the low bits of the hash).
const SHARDS: usize = 64;

#[derive(Default)]
struct Shard {
    /// Structural-hash -> collision chain of weak canonical refs.
    map: FxHashMap<u64, Vec<Weak<ChcExpr>>>,
}

fn table() -> &'static [RwLock<Shard>; SHARDS] {
    static TABLE: OnceLock<[RwLock<Shard>; SHARDS]> = OnceLock::new();
    TABLE.get_or_init(|| std::array::from_fn(|_| RwLock::new(Shard::default())))
}

#[inline]
fn shard_for(hash: u64) -> &'static RwLock<Shard> {
    &table()[(hash as usize) & (SHARDS - 1)]
}

/// Canonicalize `node`: return an `Arc<ChcExpr>` that is structurally `== node`.
///
/// If a structurally-equal node is already interned (and still alive), its
/// canonical `Arc` is returned (a refcount bump); otherwise `node` is allocated,
/// recorded, and returned. SOUND for any input — see the module invariant.
pub(crate) fn intern(node: ChcExpr) -> Arc<ChcExpr> {
    let h = node.structural_hash();
    let shard = shard_for(h);

    // Fast path: shared read lock, probe the chain.
    {
        let guard = shard.read().expect("intern shard read poisoned");
        if let Some(chain) = guard.map.get(&h) {
            for weak in chain {
                if let Some(arc) = weak.upgrade() {
                    if *arc == node {
                        return arc;
                    }
                }
            }
        }
    }

    // Slow path: exclusive write lock; re-probe (another thread may have raced
    // us), reclaim dead weaks opportunistically, then insert.
    let mut guard = shard.write().expect("intern shard write poisoned");
    let chain = guard.map.entry(h).or_default();
    let mut i = 0;
    while i < chain.len() {
        match chain[i].upgrade() {
            Some(arc) => {
                if *arc == node {
                    return arc;
                }
                i += 1;
            }
            // Dead weak: reclaim without growing the chain.
            None => {
                chain.swap_remove(i);
            }
        }
    }
    let arc = Arc::new(node);
    chain.push(Arc::downgrade(&arc));
    arc
}

/// Whether interning is active. Off by default while the fast core is rolled
/// out and measured; set `AY_CHC_INTERN=1` to enable (kill switch =0). Read
/// once and cached so the per-construction check is a single atomic load.
fn intern_enabled() -> bool {
    static ON: OnceLock<bool> = OnceLock::new();
    *ON.get_or_init(|| {
        std::env::var("AY_CHC_INTERN")
            .ok()
            .map(|v| v == "1" || v.eq_ignore_ascii_case("true"))
            .unwrap_or(false)
    })
}

/// Wrap an about-to-be-child expression in an `Arc`, interning it when it is a
/// LEAF (and interning is enabled). Leaves (`Int`/`Bool`/`Var`/…) have O(1)
/// structural hash, so interning them adds no construction slowdown while
/// deduplicating the ubiquitous shared leaves — which shrinks Drop worklists
/// (shared leaf `Arc`s fail `try_unwrap`, so the tree drop never recurses into
/// them) and lets the custom `PartialEq` ptr-eq fast path fire. Interior nodes
/// are NOT interned here (their O(subtree) hash would add an O(log N) factor to
/// construction without cached hashes — deferred to a later phase); they get a
/// plain `Arc::new`. SOUND either way: the returned `Arc` is structurally
/// `== node` (see the module invariant).
pub(crate) fn arc(node: ChcExpr) -> Arc<ChcExpr> {
    let is_leaf = matches!(
        node,
        ChcExpr::Bool(_)
            | ChcExpr::Int(_)
            | ChcExpr::Real(_, _)
            | ChcExpr::BitVec(_, _)
            | ChcExpr::Var(_)
            | ChcExpr::ConstArrayMarker(_)
            | ChcExpr::IsTesterMarker(_)
    );
    if is_leaf && intern_enabled() {
        intern(node)
    } else {
        Arc::new(node)
    }
}

/// Drop dead `Weak` entries across all shards (call at solve boundaries to bound
/// table size). Optional: clearing only loses sharing, never changes any `==`.
/// Returns the number of dead entries reclaimed.
pub(crate) fn sweep() -> usize {
    let mut removed = 0usize;
    for shard in table().iter() {
        let mut guard = shard.write().expect("sweep shard write poisoned");
        guard.map.retain(|_, chain| {
            let before = chain.len();
            chain.retain(|weak| weak.strong_count() > 0);
            removed += before - chain.len();
            !chain.is_empty()
        });
    }
    removed
}

/// Live (upgradable) interned-node count across all shards. Test/telemetry only.
pub(crate) fn live_count() -> usize {
    table()
        .iter()
        .map(|shard| {
            let guard = shard.read().expect("live_count shard read poisoned");
            guard
                .map
                .values()
                .flat_map(|chain| chain.iter())
                .filter(|weak| weak.strong_count() > 0)
                .count()
        })
        .sum()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::expr::{ChcOp, ChcSort, ChcVar};
    use std::sync::Arc;

    fn op(o: ChcOp, args: Vec<ChcExpr>) -> ChcExpr {
        ChcExpr::Op(o, args.into_iter().map(Arc::new).collect())
    }

    #[test]
    fn intern_returns_structurally_equal_node() {
        let e = op(ChcOp::Add, vec![ChcExpr::Int(1), ChcExpr::Int(2)]);
        let a = intern(e.clone());
        assert_eq!(*a, e, "intern must return a structurally-equal node");
    }

    #[test]
    fn structurally_equal_nodes_share_one_arc() {
        // Two independently-built but structurally-identical nodes.
        let e1 = op(
            ChcOp::Le,
            vec![
                ChcExpr::var(ChcVar::new("x", ChcSort::Int)),
                ChcExpr::Int(7),
            ],
        );
        let e2 = op(
            ChcOp::Le,
            vec![
                ChcExpr::var(ChcVar::new("x", ChcSort::Int)),
                ChcExpr::Int(7),
            ],
        );
        let a1 = intern(e1);
        let a2 = intern(e2);
        assert!(
            Arc::ptr_eq(&a1, &a2),
            "structurally-equal nodes must intern to the SAME Arc"
        );
    }

    #[test]
    fn distinct_nodes_get_distinct_arcs() {
        let a = intern(op(ChcOp::Le, vec![ChcExpr::Int(1), ChcExpr::Int(2)]));
        let b = intern(op(ChcOp::Le, vec![ChcExpr::Int(1), ChcExpr::Int(3)]));
        assert!(!Arc::ptr_eq(&a, &b));
        assert_ne!(*a, *b);
    }

    #[test]
    fn dead_entries_are_reclaimed() {
        // A uniquely-shaped node so it can't collide with other tests' nodes.
        let mk = || {
            op(
                ChcOp::Eq,
                vec![
                    ChcExpr::var(ChcVar::new("intern_reclaim_probe", ChcSort::Int)),
                    ChcExpr::Int(424242),
                ],
            )
        };
        {
            let a = intern(mk());
            assert!(Arc::strong_count(&a) >= 1);
        } // a dropped here -> the only strong ref gone
        let reclaimed = sweep();
        assert!(
            reclaimed >= 1,
            "sweep should reclaim the now-dead weak (got {reclaimed})"
        );
        // Re-interning after death yields a structurally-equal (fresh) Arc.
        let b = intern(mk());
        assert_eq!(*b, mk());
    }

    #[test]
    fn concurrent_interning_is_consistent() {
        // Many threads interning the SAME node must all converge to one Arc
        // (global table) and never corrupt the chain.
        use std::thread;
        let shared = op(
            ChcOp::And,
            vec![
                op(
                    ChcOp::Ge,
                    vec![
                        ChcExpr::var(ChcVar::new("c", ChcSort::Int)),
                        ChcExpr::Int(0),
                    ],
                ),
                op(
                    ChcOp::Le,
                    vec![
                        ChcExpr::var(ChcVar::new("c", ChcSort::Int)),
                        ChcExpr::Int(99),
                    ],
                ),
            ],
        );
        let handles: Vec<_> = (0..16)
            .map(|_| {
                let n = shared.clone();
                thread::spawn(move || {
                    let mut last: Option<Arc<ChcExpr>> = None;
                    for _ in 0..200 {
                        let a = intern(n.clone());
                        assert_eq!(*a, n);
                        if let Some(prev) = &last {
                            assert!(
                                Arc::ptr_eq(prev, &a),
                                "same node must stay one canonical Arc"
                            );
                        }
                        last = Some(a);
                    }
                    last.unwrap()
                })
            })
            .collect();
        let arcs: Vec<Arc<ChcExpr>> = handles.into_iter().map(|h| h.join().unwrap()).collect();
        // All threads' canonical Arcs must be the same allocation.
        for a in &arcs[1..] {
            assert!(
                Arc::ptr_eq(&arcs[0], a),
                "global table must canonicalize across threads"
            );
        }
    }
}
