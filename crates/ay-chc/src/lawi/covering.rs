// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::lawi::art::{AbstractReachabilityTree, ArtVertexId};
use ay_core::kani_compat::DetHashSet as FxHashSet;

/// Element `(coveree, coverer)` in the LAWI covering relation.
///
/// Semantics: `coveree` is directly covered by `coverer`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct CoveringElement {
    pub(crate) coveree: ArtVertexId,
    pub(crate) coverer: ArtVertexId,
}

/// Covering relation for LAWI pruning.
///
/// Mirrors Golem's relation semantics (`reference/golem/src/engine/Lawi.cc:591-618`):
/// if a node is covered then all of its descendants are implicitly pruned.
#[derive(Debug, Clone, Default)]
pub(crate) struct CoveringRelation {
    elements: Vec<CoveringElement>,
}

impl CoveringRelation {
    #[cfg(test)]
    pub(crate) fn len(&self) -> usize {
        self.elements.len()
    }

    pub(crate) fn is_covered(&self, vertex: ArtVertexId, art: &AbstractReachabilityTree) -> bool {
        let ancestors = art.ancestors_including(vertex);
        ancestors
            .iter()
            .any(|ancestor| self.elements.iter().any(|elem| elem.coveree == *ancestor))
    }

    pub(crate) fn update_with(
        &mut self,
        art: &AbstractReachabilityTree,
        coveree: ArtVertexId,
        coverer: ArtVertexId,
    ) {
        if coveree == coverer
            || !art.same_location(coveree, coverer)
            || art.is_ancestor(coveree, coverer)
        {
            return;
        }

        let new_elem = CoveringElement { coveree, coverer };
        if self.elements.contains(&new_elem) {
            return;
        }

        // Descendants of a covered node cannot validly cover others anymore.
        let descendants: FxHashSet<_> = art.descendants_including(coveree).into_iter().collect();
        self.elements
            .retain(|elem| !descendants.contains(&elem.coverer));
        self.elements.push(new_elem);
    }

    /// Invalidate covering pairs where `vertex` is the coverer.
    ///
    /// Called when a vertex label is strengthened (conjuncted with an interpolant).
    /// Since the coverer's label is now stronger, previous implications
    /// `label(coveree) => label(coverer)` may no longer hold.
    /// Reference: `reference/golem/src/engine/Lawi.cc:613-618`.
    pub(crate) fn vertex_strengthened(&mut self, vertex: ArtVertexId) {
        self.elements.retain(|elem| elem.coverer != vertex);
    }
}
