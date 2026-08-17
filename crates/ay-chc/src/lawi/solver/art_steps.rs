// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! ART initialization, traversal, and refinement-path construction for LAWI.

use super::{LabelingFunction, LawiSolver};
use crate::lawi::art::{ArtEdgeId, ArtVertexId};
use crate::lawi::path_encoding::art_edge_formula_at;
use crate::transition_system::TransitionSystem;
use crate::ChcExpr;

impl LawiSolver {
    pub(super) fn initial_worklist(
        labels: &mut LabelingFunction,
        root: ArtVertexId,
        init: &ChcExpr,
    ) -> Vec<ArtVertexId> {
        // Initialize root label to the init constraint.
        // Without this, root's label stays TRUE, allowing spurious covering:
        // any vertex at the same location with label TRUE would be covered by root
        // (TRUE ⇒ TRUE), preventing exploration of deeper error paths.
        // Reference: In Golem's LAWI, the root corresponds to the source vertex
        // of the CHC graph; the init constraint flows through the first edge.
        // Since our ART root is placed at the predicate location (not a source),
        // we embed the init constraint directly in the root's label.
        labels.strengthen(root, init.clone());
        vec![root]
    }

    pub(super) fn expand_worklist(&mut self, vertex: ArtVertexId, worklist: &mut Vec<ArtVertexId>) {
        // Non-error vertex: expand and push children to worklist.
        let children = self.art_mut().expand(vertex);

        // Initialize children labels to `true` (implicit in LabelingFunction).
        // Push children in reverse order for DFS (last child processed first).
        worklist.extend(children.into_iter().rev());
    }

    /// Build the concrete ART path formula:
    /// `init@0 ∧ edge_0@0 ∧ edge_1@1 ∧ ... ∧ edge_{k-1}@(k-1)`.
    ///
    /// Each ART edge stores the original clause index selected during
    /// expansion. LAWI refinement must assert those selected edge formulas,
    /// not the whole transition relation, otherwise a spurious ART branch is
    /// checked against an over-approximate k-step reachability query.
    pub(super) fn refinement_path_parts(
        &self,
        ts: &TransitionSystem,
        path_edges: &[ArtEdgeId],
        k: usize,
    ) -> Option<Vec<ChcExpr>> {
        let init = ts.init_at(0);
        let mut path_parts: Vec<ChcExpr> = Vec::with_capacity(k + 1);
        path_parts.push(init);

        for (step, edge_id) in path_edges.iter().enumerate() {
            let edge = self.art().edge(*edge_id)?;
            let step_formula = art_edge_formula_at(ts, &self.problem, edge.clause_idx, step)?;
            path_parts.push(step_formula);
        }

        Some(path_parts)
    }
}
