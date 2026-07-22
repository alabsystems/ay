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
use crate::engine_result::{build_single_pred_model, skeleton_counterexample, ChcEngineResult};
use crate::interpolant_validation::collect_conjuncts_for_interpolation;
use crate::interpolation::{interpolating_sat_constraints, InterpolatingSatResult};
use crate::lawi::art::{AbstractReachabilityTree, ArtVertexId};
use crate::lawi::covering::CoveringRelation;
use crate::lawi::path_encoding::art_edge_formula_at;
use crate::smt::{SmtContext, SmtResult};
use crate::transition_system::TransitionSystem;
use crate::{ChcExpr, ChcProblem, ChcSort};
use ay_core::kani_compat::DetHashMap as FxHashMap;

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

/// Result of attempting to refine a spurious error path.
enum RefineResult {
    /// The error path is satisfiable — real counterexample found.
    Unsafe(usize),
    /// The path was spurious; labels were strengthened at these vertices.
    Refined(Vec<ArtVertexId>),
    /// Interpolation failed; cannot determine safety.
    Failed,
}

/// LAWI solver implementing the IMPACT algorithm.
///
/// Reference: `reference/golem/src/engine/Lawi.cc:385-847`.
pub(crate) struct LawiSolver {
    art: Option<AbstractReachabilityTree>,
    covering: CoveringRelation,
    labels: LabelingFunction,
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
        let mut smt = SmtContext::new();
        match smt.check_sat(&init_and_query) {
            SmtResult::Sat(_) => {
                return ChcEngineResult::Unsafe(skeleton_counterexample(&self.problem, 0));
            }
            SmtResult::Unknown => return ChcEngineResult::Unknown,
            _ => {}
        }

        let mut iterations = 0usize;
        let root = self.art().root();

        // Initialize root label to the init constraint.
        // Without this, root's label stays TRUE, allowing spurious covering:
        // any vertex at the same location with label TRUE would be covered by root
        // (TRUE ⇒ TRUE), preventing exploration of deeper error paths.
        // Reference: In Golem's LAWI, the root corresponds to the source vertex
        // of the CHC graph; the init constraint flows through the first edge.
        // Since our ART root is placed at the predicate location (not a source),
        // we embed the init constraint directly in the root's label.
        self.labels.strengthen(root, ts.init.clone());

        let mut worklist = vec![root];

        while let Some(vertex) = worklist.pop() {
            if self.config.base.is_cancelled() {
                return ChcEngineResult::Unknown;
            }

            let vertex_count = self.art().vertex_count();
            if iterations >= self.config.max_iterations || vertex_count >= self.config.max_vertices
            {
                if self.config.base.verbose {
                    safe_eprintln!(
                        "LAWI: resource limit (iter={}, vertices={})",
                        iterations,
                        vertex_count
                    );
                }
                return ChcEngineResult::Unknown;
            }
            iterations += 1;

            // Try to cover ancestors before processing the vertex.
            self.close_all_ancestors(vertex);

            if self.covering.is_covered(vertex, self.art()) {
                continue;
            }

            let is_error = self.art().is_error_location(vertex);

            if is_error {
                // Error leaf reached — attempt refinement.
                match self.refine(vertex) {
                    RefineResult::Unsafe(depth) => {
                        return ChcEngineResult::Unsafe(skeleton_counterexample(
                            &self.problem,
                            depth,
                        ));
                    }
                    RefineResult::Refined(strengthened) => {
                        // Re-attempt covering for strengthened vertices.
                        for v in &strengthened {
                            self.close(*v);
                        }
                        // Do not add error vertex to worklist.
                        continue;
                    }
                    RefineResult::Failed => {
                        return ChcEngineResult::Unknown;
                    }
                }
            }

            // Non-error vertex: expand and push children to worklist.
            let children = self.art_mut().expand(vertex);

            // Initialize children labels to `true` (implicit in LabelingFunction).
            // Push children in reverse order for DFS (last child processed first).
            worklist.extend(children.into_iter().rev());
        }

        // No uncovered leaves remain — system is Safe.
        self.build_safe_model()
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

        let mut smt = SmtContext::new();
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
        let ts = match self.ts.as_ref() {
            Some(ts) => ts,
            None => return RefineResult::Failed,
        };

        let path_vertices = self.art().path_vertices_from_root(error_vertex);
        let path_edges = self.art().path_from_root(error_vertex);

        // Path length = number of edges = vertices - 1.
        // Root is at position 0, error vertex is at position k.
        let k = path_vertices.len() - 1;
        if k == 0 {
            // Root is the error location — trivially unsafe if init ∧ query is SAT,
            // but we already checked this in the precheck. Return Unknown.
            return RefineResult::Failed;
        }

        // Build the concrete ART path formula:
        //   init@0 ∧ edge_0@0 ∧ edge_1@1 ∧ ... ∧ edge_{k-1}@(k-1)
        //
        // Each ART edge stores the original clause index selected during
        // expansion. LAWI refinement must assert those selected edge formulas,
        // not the whole transition relation, otherwise a spurious ART branch is
        // checked against an over-approximate k-step reachability query.
        let init = ts.init_at(0);
        let mut path_parts: Vec<ChcExpr> = Vec::with_capacity(k + 1);
        path_parts.push(init);

        for (step, edge_id) in path_edges.iter().enumerate() {
            let Some(edge) = self.art().edge(*edge_id) else {
                return RefineResult::Failed;
            };
            let Some(step_formula) = art_edge_formula_at(ts, &self.problem, edge.clause_idx, step)
            else {
                return RefineResult::Failed;
            };
            path_parts.push(step_formula);
        }

        // Check satisfiability of the full path.
        let full_path = ChcExpr::and_all(path_parts.iter().cloned());
        let mut smt = SmtContext::new();
        match smt.check_sat(&full_path) {
            SmtResult::Sat(_) => {
                // Real counterexample.
                return RefineResult::Unsafe(k);
            }
            SmtResult::Unknown => return RefineResult::Failed,
            _ => {
                // UNSAT — path is spurious. Compute interpolants.
            }
        }

        // Compute path interpolants.
        //
        // For each boundary i (1 ≤ i ≤ k-1), compute an interpolant between:
        //   A = init@0 ∧ trans@(0→1) ∧ ... ∧ trans@((i-1)→i)
        //   B = trans@(i→(i+1)) ∧ ... ∧ query@(k-1)
        //
        // The interpolant I_i is over variables at time i.
        // Normalize I_i back to time-0 variables to get the label for vertex i.
        //
        // Reference: `reference/golem/src/engine/Lawi.cc:551-565`.
        let mut strengthened = Vec::new();

        for boundary in 1..k {
            let a_formula = ChcExpr::and_all(path_parts[..=boundary].iter().cloned());
            let b_formula = ChcExpr::and_all(path_parts[boundary + 1..].iter().cloned());

            // Include the transition into boundary as part of A,
            // and the transition out of boundary as part of B.
            // Shared variables are at time `boundary`.
            let shared_vars = ts.state_var_names_at(boundary);

            let mut a_constraints = Vec::new();
            collect_conjuncts_for_interpolation(&a_formula, &mut a_constraints);
            let mut b_constraints = Vec::new();
            collect_conjuncts_for_interpolation(&b_formula, &mut b_constraints);

            let interpolant =
                match interpolating_sat_constraints(&a_constraints, &b_constraints, &shared_vars) {
                    InterpolatingSatResult::Unsat(itp) => itp,
                    InterpolatingSatResult::Unknown => {
                        if self.config.base.verbose {
                            safe_eprintln!("LAWI: interpolation failed at boundary {}", boundary);
                        }
                        continue;
                    }
                };

            // Normalize interpolant from time `boundary` back to time 0.
            // Reference: `reference/golem/src/engine/Lawi.cc:791-798`.
            let normalized = ts.rename_state_vars_at(&interpolant, boundary, 0);

            let vertex = path_vertices[boundary];
            if self.labels.strengthen(vertex, normalized) {
                // Label changed — invalidate covering pairs where this vertex is coverer.
                self.covering.vertex_strengthened(vertex);
                strengthened.push(vertex);
            }
        }

        if self.config.base.verbose {
            safe_eprintln!(
                "LAWI: refined path of length {}, strengthened {} vertices",
                k,
                strengthened.len()
            );
        }

        RefineResult::Refined(strengthened)
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

        for vertex_id in 0..art.vertex_count() as u32 {
            let vertex = ArtVertexId(vertex_id);
            if self.covering.is_covered(vertex, art) {
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
