// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! ART initialization, traversal, and refinement-path construction for LAWI.

use super::{LabelingFunction, LawiSolver};
use crate::ground_derivation::linear_trace::{
    engine_trace_counterexample, ts_locals_with_suffix, LinearTrace, TraceEdgeHint,
};
use crate::lawi::art::{ArtEdgeId, ArtVertexId};
use crate::lawi::path_encoding::art_edge_formula_at;
use crate::pdr::Counterexample;
use crate::smt::SmtValue;
use crate::transition_system::TransitionSystem;
use crate::ChcExpr;
use ay_core::kani_compat::DetHashMap as FxHashMap;

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

    /// The concrete trace a SAT model of the ART path formula
    /// (`refinement_path_parts`) describes: the state at every step and, per
    /// edge, the fired clause with its locals under the names
    /// `art_edge_formula_at` gave them (`__lawi_tr{c}_{x}__t{step}`,
    /// `__lawi_qry{c}_{x}__q{step}`; init locals `{ts prefix}{x}__i0`).
    ///
    /// `path_edges` holds the transitions followed by the query edge.
    pub(super) fn path_trace(
        &self,
        ts: &TransitionSystem,
        path_edges: &[ArtEdgeId],
        model: &FxHashMap<String, SmtValue>,
    ) -> LinearTrace {
        let transitions = path_edges.len().saturating_sub(1);
        let mut edges = Vec::with_capacity(path_edges.len() + 1);
        edges.push(TraceEdgeHint {
            ts_locals: ts_locals_with_suffix(model, "__i0"),
            ..TraceEdgeHint::default()
        });
        for (step, edge_id) in path_edges.iter().enumerate() {
            let Some(edge) = self.art().edge(*edge_id) else {
                edges.push(TraceEdgeHint::default());
                continue;
            };
            let clause_idx = edge.clause_idx;
            let (prefix, suffix) = if step < transitions {
                (format!("__lawi_tr{clause_idx}_"), format!("__t{step}"))
            } else {
                (format!("__lawi_qry{clause_idx}_"), format!("__q{step}"))
            };
            let clause_values = self
                .problem
                .clauses()
                .get(clause_idx)
                .map(|clause| {
                    clause
                        .vars()
                        .into_iter()
                        .filter_map(|var| {
                            let value = model.get(&format!("{prefix}{}{suffix}", var.name))?;
                            Some((var.name, value.clone()))
                        })
                        .collect()
                })
                .unwrap_or_default();
            edges.push(TraceEdgeHint {
                clause: Some(clause_idx),
                clause_values,
                ..TraceEdgeHint::default()
            });
        }
        LinearTrace {
            predicate: ts.predicate,
            states: LinearTrace::states_from_ts_model(ts, model, transitions),
            edges,
        }
    }

    /// The counterexample LAWI reports for a SAT path (see
    /// [`engine_trace_counterexample`]).
    pub(super) fn trace_counterexample(&self, trace: &LinearTrace, depth: usize) -> Counterexample {
        engine_trace_counterexample(
            &self.problem,
            trace,
            depth,
            self.config.base.cancellation_token.as_ref(),
            "LAWI",
        )
    }
}
