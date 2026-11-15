// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Typed, query-owned DAG census for a future counted SMT entrypoint.
//!
//! This is admission data, NOT a solve or proof. One supplied owner pays for
//! all visits, edges, table growth and name bytes; no clock or local grant is
//! created. Pointer keys identify nodes kept alive by the original borrow,
//! never structural equality or equivalence. The iterative postorder is the
//! usual memoized DAG traversal (Cormen et al., Introduction to Algorithms,
//! 4th ed., graph traversal); shared children are typed once, not unfolded.

use ay_core::kani_compat::DetHashMap;
use ay_core::original_query::{CountedAdmission, CountedAdmissionError};

use crate::ChcExpr;

mod allocation;
mod convert;
mod types;
mod walk;

#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
pub(super) enum Error {
    #[error("the query contains a sort or operation outside the counted fragment")]
    Unsupported,
    #[error("the original query is ill-typed")]
    IllTyped,
    #[error("the scalar candidate does not satisfy its exact source encoding")]
    InvalidCandidate,
    #[error(transparent)]
    Stopped(#[from] CountedAdmissionError),
}

type Result<T> = std::result::Result<T, Error>;

/// Counts describe the ORIGINAL graph, including dead Boolean/ITE arms.
/// A supported array census does not imply an effort-accounted array solver.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub(super) struct Census {
    pub(super) nodes: usize,
    pub(super) edges: usize,
    pub(super) variable_occurrences: usize,
    pub(super) name_bytes: usize,
    pub(super) bitvector_nodes: usize,
    pub(super) bitvector_width_sum: u64,
    pub(super) max_bitvector_width: u32,
    pub(super) has_arrays: bool,
}

/// A complete typed postorder over one borrowed original expression.
/// Node and sort IDs are local to this value, not portable solver identities.
pub(super) struct Query<'a> {
    pub(super) original: &'a ChcExpr,
    pub(super) census: Census,
    nodes: Vec<(&'a ChcExpr, types::Type)>,
    types: types::Types,
    node_ids: DetHashMap<usize, Option<usize>>,
    owner: CountedAdmission,
}

impl Query<'_> {
    /// Reuse the original paid identity table; do not rescan shared children
    /// or use an expression digest as a node/type identity.
    pub(super) fn node_index(&self, node: &ChcExpr) -> Result<usize> {
        self.owner.admit(1, 0)?;
        self.node_ids
            .get(&(std::ptr::from_ref(node) as usize))
            .copied()
            .flatten()
            .ok_or(Error::IllTyped)
    }
}

pub(super) fn read<'a>(original: &'a ChcExpr, owner: &CountedAdmission) -> Result<Query<'a>> {
    // Even a literal true/false must not bypass zero-effort refusal.
    owner.admit(1, 0)?;
    let result = walk::read(original, owner);
    // Walk scratch is gone before this fence. Returned graph disposal, and
    // every later solver phase, remain the same owner's responsibility.
    owner.check()?;
    result
}

fn exhausted(owner: &CountedAdmission) -> Error {
    Error::Stopped(owner.refuse(CountedAdmissionError::WorkExhausted))
}

#[cfg(test)]
mod tests;
