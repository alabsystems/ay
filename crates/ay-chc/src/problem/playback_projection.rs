// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Positional witness projection through query slicing and nullary unfolding.
//!
//! The source is borrowed immutably. Clause origins are recorded when clauses
//! are selected, never reconstructed by structural equality or digest matching.
//! All ground authority comes from the existing typed V2 decoder, including a
//! second validation against the exact original source after reconstruction.
//!
//! Polls share one caller-owned endpoint and sticky callback across operations.
//! Existing finite V2 source/value/step bounds admit remaining opaque source
//! clones, numeric operations, normalization, hash-table operations, serde and
//! destruction. These bounds are not cumulative allocation/RSS accounting or a
//! hard cancellation-latency guarantee. No solver or completion search runs.

use super::{ChcProblem, ChcQueryObligationId, HornClause};
use crate::{ChcGroundDerivationArtifactError, ChcProofRunArtifact, ChcValidatedGroundDerivation};

mod control;
mod expand;
mod lift;
mod slicing;
#[cfg(test)]
mod tests;

pub use control::ChcQueryPlaybackControl;

/// Projection refusal carries neither partial transformed source nor evidence.
#[derive(Debug, thiserror::Error)]
pub enum ChcQueryPlaybackError {
    #[error("query playback cancelled")]
    Cancelled,
    #[error("query playback original deadline expired")]
    DeadlineExceeded,
    #[error("query playback belongs to a different invocation control")]
    ForeignControl,
    #[error("query playback source is invalid")]
    InvalidSource,
    #[error("query playback cannot reconstruct erased bindings or a constrained marker")]
    UnsupportedProjection,
    #[error("query playback exceeded the existing ground-artifact shape envelope")]
    LimitExceeded,
    #[error("query playback allocation failed")]
    AllocationFailed,
    #[error(transparent)]
    Artifact(#[from] ChcGroundDerivationArtifactError),
}

type Result<T> = std::result::Result<T, ChcQueryPlaybackError>;

/// An original clause followed by zero or more nullary consumers. This flat
/// representation composes multiple unfoldings without recursive map owners.
struct Origin {
    first: usize,
    consumers: Vec<usize>,
}

/// One prepared query paired with its exact, immutably borrowed original source.
///
/// There is no public constructor, mutable problem accessor, Clone or serde
/// implementation. Additional unrecorded rewrites are not admitted: their V2
/// bytes will not authenticate against `problem()`. A successful lift returns
/// only evidence revalidated against `original_problem()`.
#[must_use]
pub struct ChcQueryPlayback<'source> {
    original: &'source ChcProblem,
    owner: std::sync::Arc<()>,
    id: ChcQueryObligationId,
    problem: ChcProblem,
    origins: Vec<Origin>,
}

impl ChcQueryPlayback<'_> {
    /// Identity of the initially sliced source obligation. Later supported
    /// unfolding changes `problem()`; it does not rewrite this original id.
    pub fn obligation_id(&self) -> &ChcQueryObligationId {
        &self.id
    }

    pub fn original_problem(&self) -> &ChcProblem {
        self.original
    }

    pub fn problem(&self) -> &ChcProblem {
        &self.problem
    }

    /// Consume the row and apply one ordinary nullary-query expansion pass.
    ///
    /// Constrained marker consumers are refused, since the historical pass
    /// drops their guard and cannot reconstruct its erased bindings. On any
    /// refusal the entire owned row is dropped; no half-updated map is exposed.
    /// The same control must be used for preparation, expansion and lifting.
    pub fn expand_nullary_queries(
        self,
        control: &mut ChcQueryPlaybackControl<'_>,
    ) -> Result<(Self, bool)> {
        control.require_owner(&self.owner)?;
        let result = expand::expand(self, control);
        control.finish(result)
    }

    /// Validate exact prepared-row V2 bytes, project their complete typed
    /// environments and ordered premises, and encode/revalidate original V2.
    /// No missing variable is assigned a default and no SAT query is issued.
    pub fn lift_ground_derivation_v2(
        &self,
        bytes: &[u8],
        control: &mut ChcQueryPlaybackControl<'_>,
    ) -> Result<(ChcProofRunArtifact, ChcValidatedGroundDerivation)> {
        control.require_owner(&self.owner)?;
        let result = lift::lift(self, bytes, control);
        control.finish(result)
    }
}

impl ChcProblem {
    /// Prepare the same independent obligations as `query_obligations`, while
    /// recording original ordinals at selection time for later Unsafe playback.
    ///
    /// Source shape/semantics first pass the existing finite V2 admission.
    /// Inputs without a live query (including vacuous pruned-only problems)
    /// and sources marked as having stripped negative quantifiers are refused.
    /// This narrower, fallible diagnostic route does not alter ordinary query
    /// solving and does not claim a cumulative allocator or process RSS bound.
    pub fn query_obligations_with_playback<'source>(
        &'source self,
        control: &mut ChcQueryPlaybackControl<'_>,
    ) -> Result<Vec<ChcQueryPlayback<'source>>> {
        let result = slicing::prepare(self, control);
        control.finish(result)
    }
}

fn marker(clause: &HornClause) -> Option<crate::PredicateId> {
    if !clause.is_query() {
        return None;
    }
    match clause.body.predicates.as_slice() {
        [(predicate, arguments)] if arguments.is_empty() => Some(*predicate),
        _ => None,
    }
}
