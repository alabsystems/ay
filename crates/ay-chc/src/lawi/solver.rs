// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! LAWI (Lazy Abstraction With Interpolants) solver.
//!
//! Implements McMillan's IMPACT algorithm (CAV 2006) for CHC solving.
//! Port of Golem's LAWI engine (`reference/golem/src/engine/Lawi.cc`).
//!
//! Algorithm overview:
//! 1. Build an Abstract Reachability Tree (ART) rooted at the initial state
//! 2. DFS-expand the tree; when an error leaf is reached, check the path
//! 3. If path is satisfiable → Unsafe (real counterexample)
//! 4. If path is unsatisfiable → compute path interpolants, strengthen labels
//! 5. Attempt covering: if label(coveree) ⇒ label(coverer), prune subtree
//! 6. When all leaves are covered → Safe (invariant = ∨ of uncovered labels)

use crate::engine_config::ChcEngineConfig;
use crate::engine_result::{build_single_pred_model, ChcEngineResult};
use crate::ground_derivation::linear_trace::LinearTrace;
use crate::interpolant_validation::collect_conjuncts_for_interpolation;
use crate::interpolation::stats::{self, EngineTag, ExitReason};
use crate::interpolation::{interpolating_sat_constraints_lra_proof_first, InterpolatingSatResult};
use crate::lawi::art::{AbstractReachabilityTree, ArtVertexId};
use crate::lawi::covering::CoveringRelation;
use crate::lawi::path_encoding::art_edge_formula_at;
use crate::pdr::Counterexample;
use crate::smt::{SmtContext, SmtResult};
use crate::transition_system::TransitionSystem;
use crate::{ChcExpr, ChcProblem, ChcSort};
use ay_core::kani_compat::DetHashMap as FxHashMap;
use ay_core::kani_compat::DetHashSet as FxHashSet;

mod art_steps;
#[cfg(test)]
pub(crate) mod test_hooks;

/// LAWI solver configuration.
#[derive(Debug, Clone)]
pub struct LawiConfig {
    /// Common engine settings (verbose, cancellation).
    pub(crate) base: ChcEngineConfig,
    /// Hard cap on ART vertices to avoid unbounded growth.
    pub(crate) max_vertices: usize,
    /// Hard cap on solver iterations.
    pub(crate) max_iterations: usize,
    /// Number of previous same-location vertices to consider for covering.
    pub(crate) covering_candidate_limit: usize,
}

impl Default for LawiConfig {
    fn default() -> Self {
        Self {
            base: ChcEngineConfig::default(),
            max_vertices: 20_000,
            max_iterations: 50_000,
            covering_candidate_limit: 8,
        }
    }
}

/// Per-vertex labeling function.
///
/// Each vertex starts with label `true`. Labels are monotonically strengthened
/// (conjuncted with interpolants) during refinement. A label represents an
/// over-approximation of the reachable states at that tree vertex.
///
/// Reference: Golem `LabelingFunction` in `Lawi.cc:81-142`.
struct LabelingFunction {
    labels: FxHashMap<ArtVertexId, ChcExpr>,
}

impl LabelingFunction {
    fn new() -> Self {
        Self {
            labels: FxHashMap::default(),
        }
    }

    fn get(&self, vertex: ArtVertexId) -> &ChcExpr {
        static TRUE: ChcExpr = ChcExpr::Bool(true);
        self.labels.get(&vertex).unwrap_or(&TRUE)
    }

    /// Strengthen the label by conjoining with `conjunct`.
    /// Returns true if the label actually changed.
    fn strengthen(&mut self, vertex: ArtVertexId, conjunct: ChcExpr) -> bool {
        if conjunct == ChcExpr::Bool(true) {
            return false;
        }
        let current = self.labels.remove(&vertex);
        let new_label = match current {
            Some(ChcExpr::Bool(true)) | None => conjunct,
            Some(existing) => ChcExpr::and(existing, conjunct),
        };
        self.labels.insert(vertex, new_label);
        true
    }
}

/// Why an error vertex was abandoned: its path was not refuted, so it keeps
/// LAWI from answering Safe, but the search goes on past it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum AbandonReason {
    /// A boundary got no interpolant (and no `¬query` fallback).
    ItpGap,
    /// The path check itself answered `Unknown`.
    PathUnknown,
    /// The path has no edge encoding.
    NoEncoding,
}

/// Result of attempting to refine a spurious error path.
enum RefineResult {
    /// The error path is satisfiable — real counterexample found, carrying
    /// the path model's ground evidence when it validates.
    Unsafe(Counterexample),
    /// The path was spurious and every boundary got its interpolant; labels
    /// were strengthened at these vertices. Only a complete, chained
    /// interpolant sequence produces this (see [`LawiSolver::refine`]).
    Refined(Vec<ArtVertexId>),
    /// The path was not refuted. The chained interpolants computed before
    /// the gap were applied (`strengthened`; they keep the labeling
    /// well-labeled), the error vertex stays open.
    Abandoned {
        reason: AbandonReason,
        strengthened: Vec<ArtVertexId>,
    },
    /// LAWI was cancelled during refinement; no label was changed.
    Cancelled,
}

/// What LAWI did, reported on its `[D-EXIT]` line.
#[derive(Debug, Default)]
struct LawiCounts {
    refined: usize,
    itp_gap: usize,
    path_unknown: usize,
    no_encoding: usize,
    /// Last boundaries filled by the checked `¬query` fallback.
    fallback: usize,
    /// Abandoned error vertices refuted at the end by their parent's label.
    rerefuted: usize,
    iterations: usize,
    /// Deepest error path refined or abandoned.
    max_k: usize,
}

/// LAWI solver implementing the IMPACT algorithm.
///
/// Reference: `reference/golem/src/engine/Lawi.cc:385-847`.
pub(crate) struct LawiSolver {
    art: Option<AbstractReachabilityTree>,
    covering: CoveringRelation,
    labels: LabelingFunction,
    /// Error vertices whose path was refuted: the parent's label excludes
    /// the query edge.
    refuted_errors: FxHashSet<ArtVertexId>,
    /// Error vertices whose path was neither refuted nor shown feasible.
    /// The search continues past them; an uncovered one forbids Safe.
    abandoned_errors: FxHashMap<ArtVertexId, AbandonReason>,
    counts: LawiCounts,
    ts: Option<TransitionSystem>,
    problem: ChcProblem,
    config: LawiConfig,
}

impl Drop for LawiSolver {
    fn drop(&mut self) {
        std::mem::take(&mut self.problem).iterative_drop();
    }
}

impl LawiSolver {
    pub(crate) fn new(problem: ChcProblem, config: LawiConfig) -> Self {
        let art = AbstractReachabilityTree::try_new(&problem);
        let ts = TransitionSystem::from_chc_problem(&problem).ok();
        Self {
            art,
            covering: CoveringRelation::default(),
            labels: LabelingFunction::new(),
            refuted_errors: FxHashSet::default(),
            abandoned_errors: FxHashMap::default(),
            counts: LawiCounts::default(),
            ts,
            problem,
            config,
        }
    }

    /// Borrow the ART. Valid only after `solve()` checks `self.art.is_none()`.
    fn art(&self) -> &AbstractReachabilityTree {
        self.art
            .as_ref()
            .expect("invariant: art checked in solve()")
    }

    /// Mutably borrow the ART. Valid only after `solve()` checks `self.art.is_none()`.
    fn art_mut(&mut self) -> &mut AbstractReachabilityTree {
        self.art
            .as_mut()
            .expect("invariant: art checked in solve()")
    }

    /// Main solve loop implementing `LawiContext::unwind()`.
    ///
    /// Reference: `reference/golem/src/engine/Lawi.cc:386-432`.
    pub(crate) fn solve(&mut self) -> ChcEngineResult {
        if self.art.is_none() || self.ts.is_none() {
            return ChcEngineResult::Unknown;
        }

        if !self.art().is_linear() {
            return ChcEngineResult::Unknown;
        }

        let ts = self.ts.as_ref().expect("checked above");
        // F1 (LRA-Lin unlock): admit Bool state vars. Mixed Bool+Real predicates
        // dominate the track and previously made LAWI self-skip. Soundness is
        // preserved by the portfolio acceptance pipeline, which replays every
        // Safe/Unsafe result against the ORIGINAL clauses (#5660/#5877).
        if ts
            .find_unsupported_interpolation_state_sort_allowing_bool()
            .is_some()
        {
            return ChcEngineResult::NotApplicable;
        }
        // LAWI-local guard: reject BitVec state sorts (interpolation backend has
        // no BV path). Bool is now admitted (F1).
        for var in ts.state_vars() {
            if matches!(&var.sort, ChcSort::BitVec(_)) {
                return ChcEngineResult::NotApplicable;
            }
        }

        // Precheck: SAT(init ∧ query) ⇒ unsafe at depth 0.
        let init_and_query = ChcExpr::and(ts.init.clone(), ts.query.clone());
        let mut smt = SmtContext::new_search();
        match smt.check_sat(&init_and_query) {
            SmtResult::Sat(model) => {
                let trace = LinearTrace::from_ts_unrolling(ts, &model, 0);
                let cex = self.trace_counterexample(&trace, 0);
                return self.exit(ExitReason::Unsafe, "", ChcEngineResult::Unsafe(cex));
            }
            SmtResult::Unknown => {
                return self.exit(
                    ExitReason::BaseUnknown,
                    "precheck=unknown",
                    ChcEngineResult::Unknown,
                );
            }
            _ => {}
        }

        let root = self.art().root();
        let mut worklist = Self::initial_worklist(&mut self.labels, root, &ts.init);

        loop {
            if self.config.base.is_cancelled() {
                return self.exit(ExitReason::Cancelled, "", ChcEngineResult::Unknown);
            }
            let Some(vertex) = worklist.pop() else {
                // A vertex popped while covered was dropped; strengthening its
                // coverer may have uncovered it since. Safe needs every
                // uncovered vertex finished, so re-queue the ones that are not.
                let unfinished = self.unfinished_vertices();
                if unfinished.is_empty() {
                    break;
                }
                worklist.extend(unfinished.into_iter().rev());
                continue;
            };

            let vertex_count = self.art().vertex_count();
            if self.counts.iterations >= self.config.max_iterations
                || vertex_count >= self.config.max_vertices
            {
                if self.config.base.verbose {
                    safe_eprintln!(
                        "LAWI: resource limit (iter={}, vertices={})",
                        self.counts.iterations,
                        vertex_count
                    );
                }
                return self.exit(ExitReason::Other, "limit=art", ChcEngineResult::Unknown);
            }
            self.counts.iterations += 1;

            // Try to cover ancestors before processing the vertex.
            self.close_all_ancestors(vertex);

            if self.covering.is_covered(vertex, self.art()) {
                continue;
            }

            let is_error = self.art().is_error_location(vertex);

            if is_error {
                // Error leaf reached — attempt refinement.
                let strengthened = match self.refine(vertex) {
                    RefineResult::Unsafe(cex) => {
                        return self.exit(ExitReason::Unsafe, "", ChcEngineResult::Unsafe(cex));
                    }
                    RefineResult::Refined(strengthened) => {
                        self.refuted_errors.insert(vertex);
                        strengthened
                    }
                    RefineResult::Abandoned {
                        reason,
                        strengthened,
                    } => {
                        // The path is undecided, not refuted: keep searching
                        // (a later path may be a real counterexample), but
                        // this vertex keeps LAWI from answering Safe unless
                        // its parent's label comes to exclude the query.
                        self.abandoned_errors.insert(vertex, reason);
                        strengthened
                    }
                    RefineResult::Cancelled => {
                        return self.exit(ExitReason::Cancelled, "", ChcEngineResult::Unknown);
                    }
                };
                // Re-attempt covering for strengthened vertices.
                for v in &strengthened {
                    self.close(*v);
                }
                // Do not add error vertex to worklist.
                continue;
            }

            self.expand_worklist(vertex, &mut worklist);
        }

        // Every uncovered vertex is expanded, refuted, or abandoned.
        let open = match self.open_abandoned_errors() {
            Some(open) => open,
            None => return self.exit(ExitReason::Cancelled, "", ChcEngineResult::Unknown),
        };
        if let Some(&first) = open.first() {
            let reason = if open.contains(&AbandonReason::ItpGap) {
                ExitReason::ItpFail
            } else if open.contains(&AbandonReason::PathUnknown) {
                ExitReason::BaseUnknown
            } else {
                ExitReason::Other
            };
            let detail = format!("open_abandoned={} first={first:?}", open.len());
            return self.exit(reason, &detail, ChcEngineResult::Unknown);
        }

        // No uncovered error vertex is open, and the labeling is well-labeled
        // by construction (chained refinement) — the disjunction of uncovered
        // labels is an inductive invariant.
        match self.build_safe_model() {
            safe @ ChcEngineResult::Safe(_) => self.exit(ExitReason::Safe, "", safe),
            other => self.exit(ExitReason::Other, "safe_model=none", other),
        }
    }

    /// Record LAWI's exit (`[D-EXIT]` under `--chc-proof-itp-stats`) with its
    /// counters, and return `result`.
    fn exit(&self, reason: ExitReason, extra: &str, result: ChcEngineResult) -> ChcEngineResult {
        let c = &self.counts;
        let vertices = self
            .art
            .as_ref()
            .map_or(0, AbstractReachabilityTree::vertex_count);
        let mut detail = format!(
            "refined={} itp_gap={} path_unknown={} no_encoding={} fallback={} rerefuted={} \
             iterations={} vertices={vertices}",
            c.refined,
            c.itp_gap,
            c.path_unknown,
            c.no_encoding,
            c.fallback,
            c.rerefuted,
            c.iterations,
        );
        if !extra.is_empty() {
            detail.push(' ');
            detail.push_str(extra);
        }
        stats::record_engine_exit_detail(EngineTag::Lawi, reason, c.max_k, &detail);
        result
    }

    /// Uncovered vertices the ART is not finished with: predicate vertices not
    /// yet expanded, and error vertices neither refuted nor abandoned.
    fn unfinished_vertices(&self) -> Vec<ArtVertexId> {
        let art = self.art();
        let covered = self.covering.covered_flags(art);
        (0..art.vertex_count() as u32)
            .map(ArtVertexId)
            .filter(|&v| {
                let finished = if art.is_error_location(v) {
                    self.refuted_errors.contains(&v) || self.abandoned_errors.contains_key(&v)
                } else {
                    art.is_expanded(v)
                };
                !finished && !covered[v.0 as usize]
            })
            .collect()
    }

    /// Reasons of the abandoned error vertices still uncovered once the ART
    /// is finished (`None` when cancelled). One whose parent's label now
    /// excludes its query edge — later refinements strengthened the parent —
    /// is refuted after all and moves to `refuted_errors`.
    fn open_abandoned_errors(&mut self) -> Option<Vec<AbandonReason>> {
        let covered = self.covering.covered_flags(self.art());
        let mut candidates: Vec<(ArtVertexId, AbandonReason)> = self
            .abandoned_errors
            .iter()
            .filter(|(vertex, _)| !covered[vertex.0 as usize])
            .map(|(vertex, reason)| (*vertex, *reason))
            .collect();
        candidates.sort_by_key(|(vertex, _)| vertex.0);
        let mut open = Vec::new();
        for (vertex, reason) in candidates {
            if self.config.base.is_cancelled() {
                return None;
            }
            if self.parent_label_refutes(vertex) {
                self.abandoned_errors.remove(&vertex);
                self.refuted_errors.insert(vertex);
                self.counts.rerefuted += 1;
            } else {
                open.push(reason);
            }
        }
        Some(open)
    }

    /// Whether `label(parent) ∧ query edge` is UNSAT for an error vertex —
    /// the well-labeling condition that makes it refuted.
    fn parent_label_refutes(&self, error_vertex: ArtVertexId) -> bool {
        let (Some(art), Some(ts)) = (self.art.as_ref(), self.ts.as_ref()) else {
            return false;
        };
        let Some(edge) = art.parent_edge(error_vertex) else {
            return false;
        };
        let Some(query_edge) = art_edge_formula_at(ts, &self.problem, edge.clause_idx, 0) else {
            return false;
        };
        let formula = ChcExpr::and(self.labels.get(edge.source).clone(), query_edge);
        let mut smt = SmtContext::new_search();
        matches!(
            smt.check_sat(&formula),
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_)
        )
    }

    /// Attempt to cover a single vertex by finding an earlier same-location
    /// vertex whose label implies this vertex's label.
    ///
    /// Reference: `reference/golem/src/engine/Lawi.cc:374-383`.
    fn close(&mut self, coveree: ArtVertexId) {
        let art = match self.art.as_ref() {
            Some(a) => a,
            None => return,
        };

        // Error vertices must not participate in covering. They represent the
        // bad-state location and their reachability is checked via path
        // refinement, not subsumption. Since error vertices always have label
        // `true`, covering would trivially succeed (true => true) and prevent
        // the solver from checking deeper error paths for satisfiability.
        if art.is_error_location(coveree) {
            return;
        }

        if self.covering.is_covered(coveree, art) {
            return;
        }

        let candidates =
            art.earlier_at_same_location(coveree, self.config.covering_candidate_limit);
        for coverer in candidates {
            if self.covering.is_covered(coverer, art) {
                continue;
            }
            if self.can_cover(coveree, coverer) {
                self.covering.update_with(art, coveree, coverer);
                return;
            }
        }
    }

    /// Try to cover each ancestor of the given vertex.
    ///
    /// Reference: `reference/golem/src/engine/Lawi.cc:505-511`.
    fn close_all_ancestors(&mut self, vertex: ArtVertexId) {
        let ancestors = self.art().ancestors_including(vertex);
        // Process from root down (ancestors is vertex→root, so reverse).
        for ancestor in ancestors.into_iter().rev() {
            self.close(ancestor);
        }
    }

    /// Check if label(coveree) ⇒ label(coverer) via SMT.
    ///
    /// Returns true if `label(coveree) ∧ ¬label(coverer)` is UNSAT,
    /// meaning the coveree's label implies the coverer's label.
    ///
    /// Reference: `reference/golem/src/engine/Lawi.cc:232-267` (ImplicationChecker).
    fn can_cover(&self, coveree: ArtVertexId, coverer: ArtVertexId) -> bool {
        let art = match self.art.as_ref() {
            Some(a) => a,
            None => return false,
        };

        if !art.same_location(coveree, coverer) || art.is_ancestor(coveree, coverer) {
            return false;
        }

        let label_coveree = self.labels.get(coveree).clone();
        let label_coverer = self.labels.get(coverer).clone();

        // Check: is label(coveree) ∧ ¬label(coverer) unsatisfiable?
        let negated = ChcExpr::not(label_coverer);
        let query = ChcExpr::and(label_coveree, negated);

        let mut smt = SmtContext::new_search();
        matches!(
            smt.check_sat(&query),
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_)
        )
    }

    /// Refine a spurious error path using Craig interpolation.
    ///
    /// Given an error-location vertex, collect the path from root,
    /// build the path formula, check satisfiability, and if UNSAT,
    /// compute interpolants to strengthen vertex labels.
    ///
    /// Reference: `reference/golem/src/engine/Lawi.cc:513-549`.
    fn refine(&mut self, error_vertex: ArtVertexId) -> RefineResult {
        let Some(ts) = self.ts.as_ref() else {
            // `solve` checked the transition system before searching.
            return RefineResult::Abandoned {
                reason: AbandonReason::NoEncoding,
                strengthened: Vec::new(),
            };
        };

        let path_vertices = self.art().path_vertices_from_root(error_vertex);
        let path_edges = self.art().path_from_root(error_vertex);

        // Path length = number of edges = vertices - 1.
        // Root is at position 0, error vertex is at position k.
        let k = path_vertices.len() - 1;
        self.counts.max_k = self.counts.max_k.max(k);
        let abandon = |counts: &mut LawiCounts, reason, strengthened| {
            match reason {
                AbandonReason::ItpGap => counts.itp_gap += 1,
                AbandonReason::PathUnknown => counts.path_unknown += 1,
                AbandonReason::NoEncoding => counts.no_encoding += 1,
            }
            RefineResult::Abandoned {
                reason,
                strengthened,
            }
        };
        let path_parts = match self.refinement_path_parts(ts, &path_edges, k) {
            // k = 0 would make the root an error location; it is a predicate.
            Some(parts) if k > 0 => parts,
            _ => return abandon(&mut self.counts, AbandonReason::NoEncoding, Vec::new()),
        };

        // Check satisfiability of the full path.
        let full_path = ChcExpr::and_all(path_parts.iter().cloned());
        let mut smt = SmtContext::new_search();
        match smt.check_sat(&full_path) {
            SmtResult::Sat(model) => {
                // Real counterexample: its model is the witness.
                let trace = self.path_trace(ts, &path_edges, &model);
                return RefineResult::Unsafe(self.trace_counterexample(&trace, k));
            }
            SmtResult::Unknown => {
                if self.config.base.is_cancelled() {
                    return RefineResult::Cancelled;
                }
                stats::record_engine_event(EngineTag::Lawi, "path_unknown", k, "abandoned=1");
                return abandon(&mut self.counts, AbandonReason::PathUnknown, Vec::new());
            }
            _ => {
                // UNSAT — path is spurious. Compute interpolants.
            }
        }

        // Compute the path interpolant sequence I_1..I_{k-1} (I_b over the
        // state at time b), CHAINED so the labeling is well-labeled by
        // construction:
        //   b = 1: A_1 = init@0 ∧ edge_0
        //   b > 1: A_b = I_{b-1}@(b-1) ∧ edge_{b-1}
        //   B_b   = edge_b ∧ ... ∧ edge_{k-2} ∧ query@(k-1)
        // A_1 ∧ B_1 is the (UNSAT) path; A_b ∧ B_b = I_{b-1} ∧ B_{b-1} is UNSAT
        // because I_{b-1} blocks B_{b-1}. So every pair is a valid Craig
        // problem, and A_b ⇒ I_b is exactly I_{b-1} ∧ edge_{b-1} ⇒ I_b'.
        // Independently computed prefix/suffix interpolants (the Golem
        // reference gets this from sequence interpolation over one proof) do
        // not have that property.
        //
        // A boundary without an interpolant stops the sequence: I_1..I_{b-1}
        // (the chained prefix) are applied — each still satisfies its edge's
        // well-labeling condition, and the edge into v_b keeps its old,
        // weaker target — and the error vertex is abandoned, not refuted.
        // Before, a gap left label(v_b) unrefined while the error vertex was
        // discarded, and covering then closed the ART over a non-inductive
        // labeling (cav12 transmitter.5: LAWI reported Safe with invariant
        // `true`).
        let mut interpolants: Vec<ChcExpr> = Vec::with_capacity(k - 1);
        let mut gap_at = None;
        for boundary in 1..k {
            // Each boundary runs an interpolation call: stop once cancelled.
            if self.config.base.is_cancelled() {
                return RefineResult::Cancelled;
            }
            let a_formula = match interpolants.last() {
                None => ChcExpr::and(path_parts[0].clone(), path_parts[1].clone()),
                Some(previous) => ChcExpr::and(previous.clone(), path_parts[boundary].clone()),
            };
            let b_formula = ChcExpr::and_all(path_parts[boundary + 1..].iter().cloned());
            let shared_vars = ts.state_var_names_at(boundary);

            let mut a_constraints = Vec::new();
            collect_conjuncts_for_interpolation(&a_formula, &mut a_constraints);
            let mut b_constraints = Vec::new();
            collect_conjuncts_for_interpolation(&b_formula, &mut b_constraints);

            let interpolant = match Self::boundary_interpolant(
                &a_constraints,
                &b_constraints,
                &shared_vars,
                boundary,
            ) {
                InterpolatingSatResult::Unsat(itp) => Some(itp),
                InterpolatingSatResult::Unknown => {
                    Self::last_boundary_fallback_candidate(
                        &path_parts[k],
                        &shared_vars,
                        boundary,
                        k,
                    )
                    .filter(|_| {
                        // Checked, not derived: ¬query is an interpolant
                        // exactly when A ∧ query is UNSAT.
                        let mut smt = SmtContext::new_search();
                        matches!(
                            smt.check_sat(&ChcExpr::and(a_formula.clone(), path_parts[k].clone())),
                            SmtResult::Unsat
                                | SmtResult::UnsatWithCore(_)
                                | SmtResult::UnsatWithFarkas(_)
                        )
                    })
                    .inspect(|_| self.counts.fallback += 1)
                }
            };
            match interpolant {
                Some(interpolant) => interpolants.push(interpolant),
                None => {
                    gap_at = Some(boundary);
                    break;
                }
            }
        }

        // Normalize I_b from time b back to time 0 (Golem `Lawi.cc:791-798`).
        let mut strengthened = Vec::new();
        for (index, interpolant) in interpolants.iter().enumerate() {
            let boundary = index + 1;
            let normalized = ts.rename_state_vars_at(interpolant, boundary, 0);
            let vertex = path_vertices[boundary];
            if self.labels.strengthen(vertex, normalized) {
                // Label changed — invalidate covering pairs where this vertex is coverer.
                self.covering.vertex_strengthened(vertex);
                strengthened.push(vertex);
            }
        }

        if let Some(boundary) = gap_at {
            if self.config.base.verbose {
                safe_eprintln!(
                    "LAWI: interpolation failed at boundary {}; error path abandoned",
                    boundary
                );
            }
            stats::record_engine_event(
                EngineTag::Lawi,
                "itp_gap",
                k,
                &format!("boundary={boundary} applied={} abandoned=1", boundary - 1),
            );
            return abandon(&mut self.counts, AbandonReason::ItpGap, strengthened);
        }
        self.counts.refined += 1;

        if self.config.base.verbose {
            safe_eprintln!(
                "LAWI: refined path of length {}, strengthened {} vertices",
                k,
                strengthened.len()
            );
        }

        RefineResult::Refined(strengthened)
    }

    /// One boundary's Craig interpolant (contract: A ⇒ I, I ∧ B UNSAT, I over
    /// `shared_vars`; see `interpolating_sat_constraints`).
    fn boundary_interpolant(
        a_constraints: &[ChcExpr],
        b_constraints: &[ChcExpr],
        shared_vars: &FxHashSet<String>,
        boundary: usize,
    ) -> InterpolatingSatResult {
        #[cfg(test)]
        if test_hooks::interpolation_forced_unknown(boundary) {
            return InterpolatingSatResult::Unknown;
        }
        #[cfg(not(test))]
        let _ = boundary;
        interpolating_sat_constraints_lra_proof_first(
            a_constraints,
            b_constraints,
            shared_vars,
            None,
        )
    }

    /// At the last boundary (b = k-1) B is the query edge alone, versioned at
    /// time k-1. When it mentions only state variables at k-1 (no
    /// clause-local variable), ¬query is over the shared variables and is the
    /// weakest interpolant — provided A ∧ query is UNSAT, which `refine`
    /// checks before using it (the chain argument says it is; the check keeps
    /// the fallback independent of the earlier interpolants' validation).
    /// With a local `l` the interpolant would be ¬∃l. query, which needs
    /// quantifier elimination; no candidate is offered then.
    fn last_boundary_fallback_candidate(
        query_edge: &ChcExpr,
        shared_vars: &FxHashSet<String>,
        boundary: usize,
        k: usize,
    ) -> Option<ChcExpr> {
        if boundary + 1 != k {
            return None;
        }
        #[cfg(test)]
        if test_hooks::fallback_suppressed() {
            return None;
        }
        if !query_edge
            .vars()
            .iter()
            .all(|var| shared_vars.contains(&var.name))
        {
            return None;
        }
        Some(ChcExpr::not(query_edge.clone()))
    }

    /// Build the Safe result: for each location, disjoin labels of uncovered vertices.
    ///
    /// Reference: `reference/golem/src/engine/Lawi.cc:401-432`.
    fn build_safe_model(&self) -> ChcEngineResult {
        let art = match self.art.as_ref() {
            Some(a) => a,
            None => return ChcEngineResult::Unknown,
        };

        // Collect labels of uncovered vertices, grouped by location.
        let mut labels_by_pred: FxHashMap<crate::PredicateId, Vec<ChcExpr>> = FxHashMap::default();

        let covered = self.covering.covered_flags(art);
        for vertex_id in 0..art.vertex_count() as u32 {
            let vertex = ArtVertexId(vertex_id);
            if covered[vertex_id as usize] {
                continue;
            }
            if art.is_error_location(vertex) {
                continue;
            }
            if let crate::lawi::art::ArtLocation::Predicate(pred) = art.location(vertex) {
                let label = self.labels.get(vertex).clone();
                labels_by_pred.entry(pred).or_default().push(label);
            }
        }

        // For single-predicate systems: invariant = ∨ of all uncovered vertex labels.
        if let Some(pred_labels) = labels_by_pred.values().next() {
            let invariant = ChcExpr::or_all(pred_labels.iter().cloned());
            if let Some(model) = build_single_pred_model(&self.problem, invariant) {
                return ChcEngineResult::Safe(model);
            }
        }

        // Fallback: no predicates or model construction failed.
        ChcEngineResult::Unknown
    }
}
