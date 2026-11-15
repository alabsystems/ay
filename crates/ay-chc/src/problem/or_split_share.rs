// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Process-wide sharing of OR-split results
//! (`ChcProblem::try_split_ors_in_clauses`).
//!
//! Measured on DRAGON_4 (PERF_vs_winners_2026-09-25): each portfolio PDR
//! engine spent 5.7-11.6 s of its window in `PdrSolver::new` splitting the
//! same preprocessed clauses, both at once. An entry is exact: it matches only
//! structurally identical input clauses (shallow fingerprint first, then full
//! equality, near-O(shallow) for clones through shared `Arc` children) under
//! the same per-clause cap, and the split is a deterministic function of
//! exactly those inputs, so a hit returns what a recompute would.

use std::sync::{Arc, Mutex, OnceLock, PoisonError};

use super::identity::{clauses_identical, hash_clause_shapes};
use crate::HornClause;

/// The split output for one input (the clauses and each one's source clause
/// index), filled once by whichever caller gets there first; concurrent
/// callers with the same input wait for it.
pub(super) type SharedSplit = Arc<OnceLock<(Vec<HornClause>, Vec<usize>)>>;

struct OrSplitShare {
    fingerprint: u64,
    cap: usize,
    input: Vec<HornClause>,
    output: SharedSplit,
}

/// Bounded FIFO: a solve builds PDR solvers over a handful of problems.
const OR_SPLIT_SHARE_CAP: usize = 8;

static OR_SPLIT_SHARE: OnceLock<Mutex<Vec<OrSplitShare>>> = OnceLock::new();

/// The shared slot for splitting `clauses` under `cap` (created empty on a
/// miss; the caller fills it).
pub(super) fn shared_split(clauses: &[HornClause], cap: usize) -> SharedSplit {
    let fingerprint = fingerprint(clauses, cap);
    let mut entries = OR_SPLIT_SHARE
        .get_or_init(|| Mutex::new(Vec::new()))
        .lock()
        .unwrap_or_else(PoisonError::into_inner);
    if let Some(entry) = entries.iter().find(|entry| {
        entry.fingerprint == fingerprint
            && entry.cap == cap
            && clauses_identical(&entry.input, clauses)
    }) {
        return Arc::clone(&entry.output);
    }
    if entries.len() >= OR_SPLIT_SHARE_CAP {
        entries.remove(0);
    }
    let output = SharedSplit::default();
    entries.push(OrSplitShare {
        fingerprint,
        cap,
        input: clauses.to_vec(),
        output: Arc::clone(&output),
    });
    output
}

/// Cheap pre-filter (shape only); [`clauses_identical`] is authoritative.
fn fingerprint(clauses: &[HornClause], cap: usize) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut h = std::collections::hash_map::DefaultHasher::new();
    cap.hash(&mut h);
    hash_clause_shapes(clauses, &mut h);
    h.finish()
}
