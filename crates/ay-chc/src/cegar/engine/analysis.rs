// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Counterexample analysis: trace extraction, tree building, and feasibility checking.

use super::*;

/// Red zone size for `stacker::maybe_grow` in trace tree extraction (#8570).
const TRACE_TREE_STACK_RED_ZONE: usize = 32 * 1024;

/// Stack segment size allocated by stacker for trace tree extraction recursion.
const TRACE_TREE_STACK_SIZE: usize = 1024 * 1024;

impl CegarEngine {
    pub(super) fn analyze_counterexample(&mut self, cex_edge_idx: usize) -> CexAnalysis {
        let trace = self.extract_trace(cex_edge_idx);
        self.last_cex_trace = Some(trace.clone());
        if trace.is_empty() {
            return CexAnalysis::AnalysisFailed;
        }
        let trace_tree = self.extract_trace_tree(cex_edge_idx);
        if trace_tree.is_empty() {
            return CexAnalysis::AnalysisFailed;
        }
        if self.config.base.verbose {
            safe_eprintln!(
                "CEGAR: analyzing counterexample trace (linear={}, tree_nodes={})",
                trace.len(),
                trace_tree.len()
            );
        }
        let (_, tree_constraints, tree_links) =
            match self.build_tree_symbolic_constraints(&trace_tree, "_cex") {
                Some(data) => data,
                None => return CexAnalysis::AnalysisFailed,
            };
        let mut all_constraints = tree_constraints;
        for link in &tree_links {
            all_constraints.extend(link.equalities.iter().cloned());
        }
        let cex_formula = ChcExpr::and_all(all_constraints);
        // #7165: Use executor fallback for feasibility checks. The internal
        // DPLL(T) is incomplete on disequality-heavy QF_LIA and mod/div
        // queries, causing CEGAR to loop on Unknown feasibility results.
        let cex_result = self
            .smt
            .check_sat_with_executor_fallback_timeout(&cex_formula, self.config.query_timeout);

        if self.config.base.verbose {
            safe_eprintln!(
                "CEGAR: cex feasibility check: {:?}",
                if cex_result.is_unsat() {
                    "Unsat (spurious)"
                } else if cex_result.is_sat() {
                    "Sat (genuine)"
                } else {
                    "Unknown"
                }
            );
        }

        match cex_result {
            SmtResult::Sat(_) => {
                let trace_info: Vec<_> = trace
                    .iter()
                    .map(|&ei| {
                        let edge = &self.edges[ei];
                        (edge.clause_index, Some(edge.to.clone()))
                    })
                    .collect();

                CexAnalysis::Genuine(trace_info)
            }
            SmtResult::Unknown => CexAnalysis::AnalysisFailed,
            _ => self.refine_from_trace(&trace, &trace_tree),
        }
    }

    /// Validate a counterexample against the original problem constraints.
    ///
    /// Creates a fresh PdrSolver and uses its BMC-style reachability encoding
    /// to check whether the counterexample trace is concretely feasible.
    /// Returns true if valid (genuinely unsafe), false if spurious.
    ///
    /// This catches false genuines where the abstract feasibility check passes
    /// but the concrete trace is infeasible (#3156).
    ///
    /// For multi-predicate problems the direct transition-system encoding is
    /// unavailable; the verifier instead replays the problem with bounded BMC
    /// (inc-9, `replay_unencodable_counterexample`): a complete verified
    /// derivation of false on the problem clauses confirms the
    /// counterexample, anything else rejects it. Replays are budgeted, so
    /// attempts are capped per engine run and failed depths are memoized —
    /// previously this branch unconditionally rejected EVERY multipred cex
    /// ("no BMC encoding for N predicates"), making CEGAR re-find the same
    /// genuine refutation indefinitely (gate g1; 011c-horn: 116×/run).
    pub(super) fn validate_counterexample(
        &mut self,
        trace: &[(usize, Option<AbstractState>)],
    ) -> bool {
        let num_preds = self.problem.predicates().len();
        // Zero-predicate problems (fact => false): no abstraction involved,
        // counterexample is trivially concrete — trust the feasibility check.
        if num_preds == 0 {
            return true;
        }
        let multipred = num_preds > 1;
        if multipred && !self.multipred_replay_allowed(trace.len()) {
            if self.config.base.verbose {
                safe_eprintln!(
                    "CEGAR: multi-predicate validation: rejecting counterexample \
                     (replay budget exhausted for depth {}, attempts {})",
                    trace.len(),
                    self.multipred_replay_attempts
                );
            }
            return false;
        }
        if multipred {
            self.multipred_replay_attempts += 1;
        }

        let steps: Vec<CounterexampleStep> = trace
            .iter()
            .map(|(_, state)| {
                let predicate = state.as_ref().map_or(PredicateId(0), |s| s.relation);
                CounterexampleStep::new(predicate, FxHashMap::default())
            })
            .collect();
        let cex = Counterexample {
            steps,
            witness: None,
            ground_derivation: None,
        };

        // #8630: Propagate cancellation token and add solve_timeout so
        // verification bails when the portfolio is cancelled or timed out.
        let config = PdrConfig {
            verbose: self.config.base.verbose,
            cancellation_token: self.config.base.cancellation_token.clone(),
            solve_timeout: Some(std::time::Duration::from_secs(30)),
            ..PdrConfig::default()
        };
        let mut verifier = PdrSolver::new(self.problem.clone(), config);
        match verifier.verify_counterexample(&cex) {
            CexVerificationResult::Valid => true,
            CexVerificationResult::Spurious => {
                if self.config.base.verbose {
                    safe_eprintln!("CEGAR: internal validation: counterexample is SPURIOUS");
                }
                if multipred {
                    self.note_multipred_replay_failure(trace.len());
                }
                false
            }
            CexVerificationResult::Unknown => {
                // Inconclusive — reject to be safe (#1288 soundness policy)
                if self.config.base.verbose {
                    safe_eprintln!(
                        "CEGAR: internal validation: counterexample verification UNKNOWN, rejecting"
                    );
                }
                if multipred {
                    self.note_multipred_replay_failure(trace.len());
                }
                false
            }
        }
    }

    /// Whether another multipred bounded-BMC replay validation may run
    /// (inc-9). Replays cost up to ~10s each; cap attempts per engine run and
    /// skip depths at or below a memoized failed depth so the refinement loop
    /// is never starved by repeated replays of the same refutation.
    fn multipred_replay_allowed(&self, depth: usize) -> bool {
        const MAX_MULTIPRED_REPLAY_ATTEMPTS: usize = 2;
        if self.multipred_replay_attempts >= MAX_MULTIPRED_REPLAY_ATTEMPTS {
            return false;
        }
        self.multipred_replay_failed_depth
            .is_none_or(|failed| depth > failed)
    }

    /// Record a failed multipred replay validation at `depth` (inc-9).
    fn note_multipred_replay_failure(&mut self, depth: usize) {
        self.multipred_replay_failed_depth = Some(
            self.multipred_replay_failed_depth
                .map_or(depth, |failed| failed.max(depth)),
        );
    }

    fn extract_trace(&self, cex_edge_idx: usize) -> Vec<usize> {
        let mut trace = vec![cex_edge_idx];
        let mut visited = FxHashSet::default();
        visited.insert(cex_edge_idx);

        while let Some(&current_idx) = trace.last() {
            let current_edge = &self.edges[current_idx];
            if current_edge.from.is_empty() {
                break;
            }

            let mut found_parent = false;
            for from_state in &current_edge.from {
                for (idx, edge) in self.edges.iter().enumerate() {
                    if !visited.contains(&idx) && edge.to == *from_state {
                        trace.push(idx);
                        visited.insert(idx);
                        found_parent = true;
                        break;
                    }
                }
                if found_parent {
                    break;
                }
            }

            if !found_parent {
                break;
            }
        }

        trace.reverse();
        trace
    }

    fn find_predecessor_edge(
        &self,
        target_state: &AbstractState,
        before_edge_idx: usize,
    ) -> Option<usize> {
        (0..before_edge_idx)
            .rev()
            .find(|&idx| self.edges[idx].to == *target_state)
    }

    fn extract_trace_tree_rec(
        &self,
        edge_idx: usize,
        parent: Option<usize>,
        parent_body_pos: Option<usize>,
        nodes: &mut Vec<TraceTreeNode>,
    ) -> usize {
        stacker::maybe_grow(TRACE_TREE_STACK_RED_ZONE, TRACE_TREE_STACK_SIZE, || {
            let node_idx = nodes.len();
            nodes.push(TraceTreeNode {
                edge_idx,
                parent,
                parent_body_pos,
                children: Vec::new(),
            });

            let edge = &self.edges[edge_idx];
            for (body_pos, from_state) in edge.from.iter().enumerate() {
                if let Some(pred_edge_idx) = self.find_predecessor_edge(from_state, edge_idx) {
                    let child_idx = self.extract_trace_tree_rec(
                        pred_edge_idx,
                        Some(node_idx),
                        Some(body_pos),
                        nodes,
                    );
                    nodes[node_idx].children.push(child_idx);
                }
            }

            node_idx
        }) // stacker::maybe_grow
    }

    pub(super) fn extract_trace_tree(&self, cex_edge_idx: usize) -> Vec<TraceTreeNode> {
        let mut nodes = Vec::new();
        self.extract_trace_tree_rec(cex_edge_idx, None, None, &mut nodes);
        nodes
    }

    pub(super) fn build_tree_symbolic_constraints(
        &self,
        tree: &[TraceTreeNode],
        prefix: &str,
    ) -> Option<TreeSymbolicResult> {
        if tree.is_empty() {
            return None;
        }

        let mut node_substs: Vec<Vec<(ChcVar, ChcExpr)>> = Vec::with_capacity(tree.len());
        let mut node_constraints: Vec<ChcExpr> = Vec::with_capacity(tree.len());

        for (node_idx, node) in tree.iter().enumerate() {
            let edge = &self.edges[node.edge_idx];
            let clause = &self.problem.clauses()[edge.clause_index];
            let subst = rename_clause_vars(clause, prefix, node_idx);
            node_constraints.push(
                clause
                    .body
                    .constraint
                    .as_ref()
                    .map_or(ChcExpr::Bool(true), |c| c.substitute(&subst)),
            );
            node_substs.push(subst);
        }

        let mut links = Vec::new();
        for (child_idx, node) in tree.iter().enumerate() {
            let (Some(parent_idx), Some(parent_body_pos)) = (node.parent, node.parent_body_pos)
            else {
                continue;
            };

            let child_clause =
                &self.problem.clauses()[self.edges[tree[child_idx].edge_idx].clause_index];
            let parent_clause =
                &self.problem.clauses()[self.edges[tree[parent_idx].edge_idx].clause_index];
            let Some((_, parent_body_args)) = parent_clause.body.predicates.get(parent_body_pos)
            else {
                continue;
            };
            let ClauseHead::Predicate(_, ref child_head_args) = child_clause.head else {
                continue;
            };
            if child_head_args.len() != parent_body_args.len() {
                continue;
            }

            let mut eqs = Vec::new();
            for (h_arg, p_arg) in child_head_args.iter().zip(parent_body_args.iter()) {
                let child_renamed = h_arg.substitute(&node_substs[child_idx]);
                let parent_renamed = p_arg.substitute(&node_substs[parent_idx]);
                eqs.push(ChcExpr::eq(child_renamed, parent_renamed));
            }

            links.push(TraceTreeLink {
                child: child_idx,
                parent: parent_idx,
                equalities: eqs,
            });
        }

        Some((node_substs, node_constraints, links))
    }

    pub(super) fn collect_subtree_nodes(
        tree: &[TraceTreeNode],
        root: usize,
        out: &mut FxHashSet<usize>,
    ) {
        if !out.insert(root) {
            return;
        }
        for &child in &tree[root].children {
            Self::collect_subtree_nodes(tree, child, out);
        }
    }
}
