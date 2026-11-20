// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Test-only fault injection for LAWI refinement, and an independent check
//! that the final labeling is well-labeled.

use super::LawiSolver;
use crate::lawi::art::ArtVertexId;
use crate::lawi::path_encoding::art_edge_formula_at;
use crate::smt::{SmtContext, SmtResult};
use crate::ChcExpr;
use std::cell::Cell;

/// Which interpolation calls a test forces to answer `Unknown`.
#[derive(Debug, Clone, Copy)]
pub(crate) struct ForcedItpUnknown {
    /// Every interpolation call at this boundary answers `Unknown`.
    pub(crate) boundary: usize,
    /// Also refuse the last-boundary `¬query` fallback.
    pub(crate) suppress_fallback: bool,
    /// Answer `Unknown` this many times at most, then interpolate normally.
    pub(crate) max_fires: usize,
}

thread_local! {
    static FORCED: Cell<Option<ForcedItpUnknown>> = const { Cell::new(None) };
    static FIRED: Cell<usize> = const { Cell::new(0) };
}

/// Install (or clear, with `None`) the fault on this thread and reset the
/// fired count. LAWI runs on the calling thread in unit tests.
pub(crate) fn force_itp_unknown(forced: Option<ForcedItpUnknown>) {
    FORCED.with(|cell| cell.set(forced));
    FIRED.with(|cell| cell.set(0));
}

/// How many interpolation calls the installed fault answered `Unknown`.
pub(crate) fn forced_unknown_fired() -> usize {
    FIRED.with(Cell::get)
}

pub(super) fn interpolation_forced_unknown(boundary: usize) -> bool {
    let fired = FIRED.with(Cell::get);
    let forced = FORCED.with(|cell| {
        cell.get()
            .is_some_and(|f| f.boundary == boundary && fired < f.max_fires)
    });
    if forced {
        FIRED.with(|cell| cell.set(cell.get() + 1));
    }
    forced
}

pub(super) fn fallback_suppressed() -> bool {
    FORCED.with(|cell| cell.get().is_some_and(|f| f.suppress_fallback))
}

impl LawiSolver {
    /// Tree edges whose labeling is not well-labeled: for a predicate child,
    /// `label(parent) ∧ edge ∧ ¬label(child)'` is not UNSAT; for a refuted
    /// error child, `label(parent) ∧ query` is not UNSAT.
    pub(crate) fn well_labeling_violations(&self) -> Vec<ArtVertexId> {
        let (Some(art), Some(ts)) = (self.art.as_ref(), self.ts.as_ref()) else {
            return Vec::new();
        };
        let mut violations = Vec::new();
        for id in 1..art.vertex_count() as u32 {
            let child = ArtVertexId(id);
            let Some(edge) = art.parent_edge(child) else {
                continue;
            };
            let is_error = art.is_error_location(child);
            if is_error && !self.refuted_errors.contains(&child) {
                continue;
            }
            let Some(edge_formula) = art_edge_formula_at(ts, &self.problem, edge.clause_idx, 0)
            else {
                violations.push(child);
                continue;
            };
            let parent_label = self.labels.get(edge.source).clone();
            let query = if is_error {
                ChcExpr::and(parent_label, edge_formula)
            } else {
                let child_next = ts.rename_state_vars_at(self.labels.get(child), 0, 1);
                ChcExpr::and_all([parent_label, edge_formula, ChcExpr::not(child_next)])
            };
            let mut smt = SmtContext::new();
            if !matches!(
                smt.check_sat(&query),
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_)
            ) {
                violations.push(child);
            }
        }
        violations
    }

    /// The last-boundary fallback candidate LAWI would check on an error path
    /// of length `k` ending in the query clause `query_clause`.
    pub(crate) fn last_boundary_fallback_for(
        &self,
        query_clause: usize,
        k: usize,
    ) -> Option<ChcExpr> {
        let ts = self.ts.as_ref()?;
        let edge = art_edge_formula_at(ts, &self.problem, query_clause, k - 1)?;
        Self::last_boundary_fallback_candidate(&edge, &ts.state_var_names_at(k - 1), k - 1, k)
    }

    /// Error vertices LAWI abandoned and could not refute afterwards.
    pub(crate) fn abandoned_error_count(&self) -> usize {
        self.abandoned_errors.len()
    }

    /// Uncovered vertices LAWI has not finished (see `unfinished_vertices`).
    pub(crate) fn unfinished_vertex_count(&self) -> usize {
        self.unfinished_vertices().len()
    }
}
