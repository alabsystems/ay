// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Caller-owned, seeded structural digests (WP-F F0e hook).

use std::sync::Arc;

use ay_core::kani_compat::DetHashMap as FxHashMap;

use super::{arc_digest, node_digest, DigestMemo};
use crate::expr::ChcExpr;

/// A caller-owned structural digester (F0e hook for Workstream A's
/// `ConvertMemo::key_of`).
///
/// Same digest function as [`structural_digest`] but with a caller-chosen
/// seed and a memo whose lifetime the caller controls: two digesters with
/// different seeds give two independent 64-bit keys. The memo retains an
/// `Arc` to every node it has digested, so addresses cannot be reused while
/// it lives; call [`DagDigester::clear`] (or drop it) to release them.
///
/// No production caller yet: this is the F0e hook Workstream A's
/// `ConvertMemo::key_of` switches to (it currently hashes the tree twice).
pub(crate) struct DagDigester {
    seed: usize,
    memo: DigesterMemo,
}

#[derive(Default)]
struct DigesterMemo {
    map: FxHashMap<usize, (Arc<ChcExpr>, u64)>,
}

impl DigestMemo for DigesterMemo {
    fn get(&self, node: &Arc<ChcExpr>) -> Option<u64> {
        self.map
            .get(&(Arc::as_ptr(node) as usize))
            .map(|(_, digest)| *digest)
    }

    fn insert(&mut self, node: &Arc<ChcExpr>, digest: u64) {
        self.map
            .insert(Arc::as_ptr(node) as usize, (Arc::clone(node), digest));
    }
}

impl DagDigester {
    pub(crate) fn new(seed: usize) -> Self {
        Self {
            seed,
            memo: DigesterMemo::default(),
        }
    }

    /// Digest of `node`; linear in the distinct nodes not digested before by
    /// this digester.
    pub(crate) fn digest(&mut self, node: &Arc<ChcExpr>) -> u64 {
        arc_digest(node, self.seed, &mut self.memo)
    }

    /// Digest of a borrowed root (children memoised as in [`Self::digest`]).
    pub(crate) fn digest_of(&mut self, node: &ChcExpr) -> u64 {
        let seed = self.seed;
        let memo = &mut self.memo;
        node_digest(node, seed, |child| arc_digest(child, seed, memo))
    }

    /// Number of memoised (retained) inner nodes.
    pub(crate) fn len(&self) -> usize {
        self.memo.map.len()
    }

    pub(crate) fn clear(&mut self) {
        self.memo.map.clear();
    }
}
