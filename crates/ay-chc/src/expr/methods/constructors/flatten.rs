// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! N-ary `and`/`or` flattening: [`ChcExpr::and_all_checked`] and
//! [`ChcExpr::or_all`] flatten nested conjunctions/disjunctions into one
//! deduplicated operand list, keeping the operands' `Arc`s (WP-F F0a) and
//! expanding each shared nested node once ([`FlattenedNodes`]).

use std::collections::VecDeque;
use std::sync::Arc;

use ay_core::kani_compat::DetHashSet as FxHashSet;

use super::pending::{FlattenedNodes, Pending};
use super::{ChcExpr, ChcOp};

/// Conjuncts processed between two `should_stop` polls in
/// [`ChcExpr::and_all_checked`].
///
/// A power of two well above the cost of one `Instant::now()` (tens of ns) so
/// the poll is noise, yet small enough that a tripped deadline is observed
/// within a few hundred microseconds of hash-consing.
const AND_ALL_POLL_STRIDE: u32 = 512;

impl ChcExpr {
    /// [`Self::and_all`], interruptible on a caller-supplied stop predicate.
    ///
    /// The flattening loop below is the hot spot when a synthesis stage builds
    /// one very large conjunction: every conjunct is deep-hashed into `seen`,
    /// so the loop can run for seconds while the *outer* iteration count stays
    /// at one. A caller under a deadline therefore cannot bound this work by
    /// polling between calls — it has to poll inside.
    ///
    /// `should_stop` is consulted every [`AND_ALL_POLL_STRIDE`] conjuncts, which
    /// keeps the clock read off the per-conjunct path while bounding overshoot
    /// to one stride's worth of hash-consing. Returning `None` means the stop
    /// predicate tripped: the partial conjunction is DISCARDED rather than
    /// returned, so no caller can mistake a truncated (weaker) formula for the
    /// conjunction it asked for.
    pub(crate) fn and_all_checked<F: FnMut() -> bool>(
        conjuncts: impl IntoIterator<Item = Self>,
        mut should_stop: F,
    ) -> Option<Self> {
        let mut out: Vec<Arc<Self>> = Vec::new();
        let mut seen: FxHashSet<Arc<Self>> = FxHashSet::default();
        let mut pending: VecDeque<Pending> = conjuncts.into_iter().map(Pending::Owned).collect();
        let mut flattened = FlattenedNodes::default();
        let mut since_poll: u32 = 0;

        while let Some(item) = pending.pop_front() {
            since_poll += 1;
            if since_poll >= AND_ALL_POLL_STRIDE {
                since_poll = 0;
                if should_stop() {
                    return None;
                }
            }
            match item.as_expr() {
                Self::Bool(true) => {}
                Self::Bool(false) => return Some(Self::Bool(false)),
                Self::Op(ChcOp::And, args) => {
                    if !flattened.first_visit(&item) {
                        continue;
                    }
                    // Maintain left-to-right order while flattening deeply
                    // nested And trees, keeping the children's `Arc`s (F0a).
                    for arg in args.iter().rev() {
                        pending.push_front(Pending::Shared(Arc::clone(arg)));
                    }
                }
                _ => {
                    // Exact duplicate conjuncts are idempotent. Compiler-
                    // generated CHCs often repeat identical array bounds many
                    // times after inlining; retaining one copy avoids sending
                    // a much larger but equivalent formula to every engine.
                    // (`seen` hashes/compares DAG-linearly: WP-F F0a.)
                    let arc = item.into_arc();
                    if seen.insert(arc.clone()) {
                        out.push(arc);
                    }
                }
            }
        }

        Some(match out.len() {
            0 => Self::Bool(true),
            1 => out.pop().map_or(Self::Bool(true), Arc::unwrap_or_clone),
            _ => Self::Op(ChcOp::And, out),
        })
    }

    /// Build an n-ary disjunction from an iterator with constant folding.
    ///
    /// - Returns `false` for empty input
    /// - Skips `false` literals
    /// - Short-circuits on `true` literals
    /// - Recursively flattens nested `Or` operations
    ///
    /// This is the canonical version used throughout CHC solving.
    pub fn or_all(disjuncts: impl IntoIterator<Item = Self>) -> Self {
        let mut out: Vec<Arc<Self>> = Vec::new();
        let mut seen: FxHashSet<Arc<Self>> = FxHashSet::default();
        let mut pending: VecDeque<Pending> = disjuncts.into_iter().map(Pending::Owned).collect();
        let mut flattened = FlattenedNodes::default();

        while let Some(item) = pending.pop_front() {
            match item.as_expr() {
                Self::Bool(false) => {}
                Self::Bool(true) => return Self::Bool(true),
                Self::Op(ChcOp::Or, args) => {
                    if !flattened.first_visit(&item) {
                        continue;
                    }
                    // Maintain left-to-right order while flattening deeply
                    // nested Or trees, keeping the children's `Arc`s (F0a).
                    for arg in args.iter().rev() {
                        pending.push_front(Pending::Shared(Arc::clone(arg)));
                    }
                }
                _ => {
                    // #5877: Deduplicate repeated disjuncts. Interpolation
                    // produces massive Or expressions with identical repeated
                    // literals (e.g., `(<= x -1)` appearing 11 times).
                    //
                    // #9076 soundness: dedup by EXACT identity, not by hash
                    // alone. The previous `FxHashSet<u64>` of the disjunct's
                    // hash silently DROPPED a structurally-distinct disjunct on
                    // any 64-bit hash collision — weakening the Or, a latent
                    // unsound (unsat->sat) path. `FxHashSet<Arc<Self>>` hashes
                    // for bucketing then confirms with structural Eq, so a
                    // collision can never drop a distinct literal. The Arc clone
                    // is a refcount bump.
                    let arc = item.into_arc();
                    if seen.insert(arc.clone()) {
                        out.push(arc);
                    }
                }
            }
        }

        match out.len() {
            0 => Self::Bool(false),
            1 => out.pop().map_or(Self::Bool(false), Arc::unwrap_or_clone),
            _ => Self::Op(ChcOp::Or, out),
        }
    }
}
