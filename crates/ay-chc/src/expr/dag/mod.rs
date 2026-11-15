// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! DAG-linear structural support for [`ChcExpr`] (WP-F, F0a/F0e).
//!
//! `ChcExpr` children are `Arc`s, and `let` expansion and substitution
//! preserve sharing, so an expression is a DAG whose *tree* expansion can be
//! exponentially larger (sally `oral_messages`: 10^8–10^16 tree nodes from a
//! 30–60 KB file). Any walk that recurses per incoming edge — the derived
//! `Hash`, structural `==`, `vars()` — therefore costs the tree size.
//!
//! This module holds the pieces that make those walks linear in the number of
//! DISTINCT nodes:
//!
//! * [`structural_digest`]: a 64-bit structural digest computed bottom-up,
//!   memoised per `Arc` node in a bounded thread-local cache. It is a pure
//!   function of structure, so structurally equal expressions always get the
//!   same digest; distinct expressions may collide, which is why every user
//!   confirms with `==` (the digest is only ever a bucket key).
//! * [`DagDigester`]: the same digest with a caller-owned memo and seed, for a
//!   long-lived structural key (Workstream A's `ConvertMemo::key_of`, F0e).
//! * [`longest_path_at_least`]: whether some root-to-node path reaches a given
//!   depth, computed on the DAG. Tree walks that truncate at
//!   `MAX_EXPR_RECURSION_DEPTH` use it to reproduce their exact result.
//!
//! ## Cache validity (why a pointer key is sound here)
//! The thread-local cache keys a node by its `Arc` address and stores a
//! `Weak` to it. A `Weak` keeps the allocation (not the value) alive, so the
//! address cannot be reused by another allocation while the entry exists. A
//! lookup always comes from a live `Arc`, and a live `Arc` at that address is
//! the very node the entry was made for. `ChcExpr` is immutable, so an entry
//! never needs invalidation. The cache is bounded ([`DIGEST_CACHE_CAP`]):
//! when full, dead entries are swept and, if that does not free half, the
//! cache is cleared — losing entries only costs recomputation.

use std::cell::RefCell;
use std::hash::{Hash, Hasher};
use std::sync::{Arc, Weak};

use ay_core::kani_compat::DetHashMap as FxHashMap;
use rustc_hash::FxHasher;

use super::ChcExpr;

// F0e hook for Workstream A: no production caller on this branch yet.
#[allow(dead_code)]
mod digester;
pub(crate) mod eval_memo;
mod walk;

pub(crate) use walk::*;

/// Seed of the default digest (the one [`ChcExpr`]'s `Hash` writes once its
/// exact-derive budget is spent). Any fixed value works; it only has to be
/// the same everywhere the default digest is used.
pub(crate) const DEFAULT_DIGEST_SEED: usize = 0x5EED_DA60_F0A0_0001;

/// Upper bound on thread-local digest-cache entries. Each entry pins one
/// node allocation (about 100 bytes) through its `Weak`, so the bound caps
/// the memory a thread can retain for dead nodes at a few tens of MiB.
const DIGEST_CACHE_CAP: usize = 1 << 18;

#[derive(Default)]
struct DigestCache {
    map: FxHashMap<usize, (Weak<ChcExpr>, u64)>,
}

impl DigestCache {
    fn make_room(&mut self) {
        if self.map.len() < DIGEST_CACHE_CAP {
            return;
        }
        self.map.retain(|_, (weak, _)| weak.strong_count() > 0);
        if self.map.len() >= DIGEST_CACHE_CAP / 2 {
            self.map.clear();
        }
    }
}

thread_local! {
    static DIGEST_CACHE: RefCell<DigestCache> = RefCell::new(DigestCache::default());
}

/// A memo the digest walk can consult and fill. Keys are node addresses of
/// nodes that the implementor keeps from being reused (see module docs).
trait DigestMemo {
    fn get(&self, node: &Arc<ChcExpr>) -> Option<u64>;
    fn insert(&mut self, node: &Arc<ChcExpr>, digest: u64);
}

impl DigestMemo for DigestCache {
    fn get(&self, node: &Arc<ChcExpr>) -> Option<u64> {
        self.map
            .get(&(Arc::as_ptr(node) as usize))
            .map(|(_, digest)| *digest)
    }

    fn insert(&mut self, node: &Arc<ChcExpr>, digest: u64) {
        self.make_room();
        self.map
            .insert(Arc::as_ptr(node) as usize, (Arc::downgrade(node), digest));
    }
}

/// Whether a node has `Arc` children (leaves are digested directly and never
/// memoised: their digest is O(1)).
#[inline]
pub(crate) fn has_children(node: &ChcExpr) -> bool {
    match node {
        ChcExpr::Op(_, args) | ChcExpr::PredicateApp(_, _, args) | ChcExpr::FuncApp(_, _, args) => {
            !args.is_empty()
        }
        ChcExpr::ConstArray(..) | ChcExpr::ArrayLambda(_) => true,
        ChcExpr::Bool(_)
        | ChcExpr::Int(_)
        | ChcExpr::Real(_, _)
        | ChcExpr::BitVec(_, _)
        | ChcExpr::Var(_)
        | ChcExpr::ConstArrayMarker(_)
        | ChcExpr::IsTesterMarker(_) => false,
    }
}

/// The `Arc` children of a node, in order (a `ConstArray`'s value is its one
/// child; leaves have none).
pub(crate) fn children(node: &ChcExpr) -> &[Arc<ChcExpr>] {
    match node {
        ChcExpr::Op(_, args) | ChcExpr::PredicateApp(_, _, args) | ChcExpr::FuncApp(_, _, args) => {
            args
        }
        ChcExpr::ConstArray(_, value) => std::slice::from_ref(value),
        ChcExpr::ArrayLambda(lambda) => lambda.captures(),
        ChcExpr::Bool(_)
        | ChcExpr::Int(_)
        | ChcExpr::Real(_, _)
        | ChcExpr::BitVec(_, _)
        | ChcExpr::Var(_)
        | ChcExpr::ConstArrayMarker(_)
        | ChcExpr::IsTesterMarker(_) => &[],
    }
}

/// Digest of one node given its children's digests (`child` must be able to
/// answer for every `Arc` child of `node`).
fn node_digest(node: &ChcExpr, seed: usize, mut child: impl FnMut(&Arc<ChcExpr>) -> u64) -> u64 {
    let mut h = FxHasher::with_seed(seed);
    std::mem::discriminant(node).hash(&mut h);
    match node {
        ChcExpr::Bool(b) => b.hash(&mut h),
        ChcExpr::Int(n) => n.hash(&mut h),
        ChcExpr::Real(n, d) => {
            n.hash(&mut h);
            d.hash(&mut h);
        }
        ChcExpr::BitVec(v, w) => {
            v.hash(&mut h);
            w.hash(&mut h);
        }
        ChcExpr::Var(v) => v.hash(&mut h),
        ChcExpr::Op(op, args) => {
            op.hash(&mut h);
            h.write_usize(args.len());
            for arg in args {
                h.write_u64(child(arg));
            }
        }
        ChcExpr::PredicateApp(name, id, args) => {
            name.hash(&mut h);
            id.hash(&mut h);
            h.write_usize(args.len());
            for arg in args {
                h.write_u64(child(arg));
            }
        }
        ChcExpr::FuncApp(name, sort, args) => {
            name.hash(&mut h);
            sort.hash(&mut h);
            h.write_usize(args.len());
            for arg in args {
                h.write_u64(child(arg));
            }
        }
        ChcExpr::ArrayLambda(lambda) => {
            lambda.binder().hash(&mut h);
            lambda.formals().hash(&mut h);
            lambda.sort().hash(&mut h);
            h.write_u64(child(lambda.body()));
            for value in lambda.captures() {
                h.write_u64(child(value));
            }
        }
        ChcExpr::ConstArrayMarker(sort) => sort.hash(&mut h),
        ChcExpr::IsTesterMarker(name) => name.hash(&mut h),
        ChcExpr::ConstArray(sort, value) => {
            sort.hash(&mut h);
            h.write_u64(child(value));
        }
    }
    h.finish()
}

/// Digest of an `Arc`-held node, memoised in `memo` (leaves are digested
/// directly). Deep DAGs recurse on a growable stack.
fn arc_digest(node: &Arc<ChcExpr>, seed: usize, memo: &mut impl DigestMemo) -> u64 {
    if !has_children(node) {
        return node_digest(node, seed, |_| 0);
    }
    if let Some(digest) = memo.get(node) {
        return digest;
    }
    let digest = super::maybe_grow_expr_stack(|| {
        node_digest(node, seed, |child| arc_digest(child, seed, memo))
    });
    memo.insert(node, digest);
    digest
}

/// Structural digest of an `Arc`-held expression with the default seed,
/// memoised in the bounded thread-local cache. Linear in the number of
/// distinct uncached nodes; O(1) for a node digested before on this thread.
pub(crate) fn structural_digest(node: &Arc<ChcExpr>) -> u64 {
    DIGEST_CACHE.with(|cache| {
        let mut cache = cache.borrow_mut();
        arc_digest(node, DEFAULT_DIGEST_SEED, &mut *cache)
    })
}

/// Structural digest of a borrowed expression (the root need not be in an
/// `Arc`): its children go through [`structural_digest`].
#[cfg(test)]
pub(crate) fn structural_digest_of(node: &ChcExpr) -> u64 {
    node_digest(node, DEFAULT_DIGEST_SEED, structural_digest)
}

#[cfg(test)]
pub(crate) mod test_support;

#[cfg(test)]
mod tests;

#[cfg(test)]
mod front_end_tests;
