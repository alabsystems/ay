// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Interpolation strategies: tree, sequence, pointwise, Farkas cascade, and shared equalities.

use super::*;

impl CegarEngine {
    /// Tree interpolation for multi-body counterexamples.
    ///
    /// For each predicate-headed node n in the counterexample tree:
    /// - A = constraints in the subtree rooted at n (plus boundary equalities)
    /// - B = all remaining constraints (plus matching boundary equalities)
    ///   and we compute an interpolant over interface variables.
    ///
    /// This mirrors Eldarica's tree partitioning and prevents false "genuine"
    /// counterexamples when linear extraction misses sibling branches.
    fn try_tree_interpolation(
        &mut self,
        tree: &[TraceTreeNode],
    ) -> Option<Vec<(PredicateId, ChcExpr)>> {
        if tree.len() < 2 {
            return None;
        }
        let verbose = self.config.base.verbose;

        let (node_substs, node_constraints, links) =
            self.build_tree_symbolic_constraints(tree, "_tree")?;

        // The whole tree must be UNSAT before interpolation is meaningful.
        let mut all_parts = node_constraints.clone();
        for link in &links {
            all_parts.extend(link.equalities.iter().cloned());
        }
        let full_check = self
            .smt
            .check_sat_with_timeout(&ChcExpr::and_all(all_parts), self.config.query_timeout);
        if !full_check.is_unsat() {
            if verbose {
                safe_eprintln!("CEGAR tree-interp: full tree is SAT or Unknown, skipping");
            }
            return None;
        }

        let mut new_predicates = Vec::new();
        for (node_idx, node) in tree.iter().enumerate() {
            let clause = &self.problem.clauses()[self.edges[node.edge_idx].clause_index];
            let (target_relation, head_args) = match &clause.head {
                ClauseHead::Predicate(pid, args) => (*pid, args),
                ClauseHead::False => continue,
            };
            let (Some(parent_idx), Some(parent_body_pos)) = (node.parent, node.parent_body_pos)
            else {
                continue;
            };

            let canonical_vars = self.canonical_vars(target_relation);
            let iface_vars: Vec<ChcVar> = canonical_vars
                .iter()
                .enumerate()
                .map(|(i, cv)| ChcVar::new(format!("_tiface_{node_idx}_{i}"), cv.sort.clone()))
                .collect();
            let iface_names: FxHashSet<String> =
                iface_vars.iter().map(|v| v.name.clone()).collect();

            let mut subtree_nodes = FxHashSet::default();
            Self::collect_subtree_nodes(tree, node_idx, &mut subtree_nodes);

            let mut a_parts = Vec::new();
            for (idx, c) in node_constraints.iter().enumerate() {
                if subtree_nodes.contains(&idx) {
                    a_parts.push(c.clone());
                }
            }
            for link in &links {
                if subtree_nodes.contains(&link.child) && subtree_nodes.contains(&link.parent) {
                    a_parts.extend(link.equalities.iter().cloned());
                }
            }
            for (h_arg, iface_v) in head_args.iter().zip(iface_vars.iter()) {
                let renamed_head = h_arg.substitute(&node_substs[node_idx]);
                a_parts.push(ChcExpr::eq(renamed_head, ChcExpr::var(iface_v.clone())));
            }

            let mut b_parts = Vec::new();
            for (idx, c) in node_constraints.iter().enumerate() {
                if !subtree_nodes.contains(&idx) {
                    b_parts.push(c.clone());
                }
            }
            for link in &links {
                if !subtree_nodes.contains(&link.child) && !subtree_nodes.contains(&link.parent) {
                    b_parts.extend(link.equalities.iter().cloned());
                }
            }
            let parent_clause =
                &self.problem.clauses()[self.edges[tree[parent_idx].edge_idx].clause_index];
            let Some((_, parent_body_args)) = parent_clause.body.predicates.get(parent_body_pos)
            else {
                continue;
            };
            if parent_body_args.len() != iface_vars.len() {
                continue;
            }
            for (iface_v, parent_arg) in iface_vars.iter().zip(parent_body_args.iter()) {
                let parent_renamed = parent_arg.substitute(&node_substs[parent_idx]);
                b_parts.push(ChcExpr::eq(ChcExpr::var(iface_v.clone()), parent_renamed));
            }

            if b_parts.is_empty() {
                continue;
            }

            let a_resolved = Self::resolve_equalities(&a_parts, &iface_names);
            let b_resolved = Self::resolve_equalities(&b_parts, &iface_names);
            if verbose {
                safe_eprintln!(
                    "CEGAR tree-interp: node {} (pred P{}) A-parts={} B-parts={}",
                    node_idx,
                    target_relation.index(),
                    a_resolved.len(),
                    b_resolved.len()
                );
            }

            let interpolant =
                self.try_interpolation_cascade(node_idx, &a_resolved, &b_resolved, &iface_names);
            if let Some(itp) = interpolant {
                let mut back_subst = Vec::new();
                for (iface_v, canonical_v) in iface_vars.iter().zip(canonical_vars.iter()) {
                    back_subst.push((iface_v.clone(), ChcExpr::var(canonical_v.clone())));
                }
                let pred = itp.substitute(&back_subst);
                if !matches!(pred, ChcExpr::Bool(true | false)) {
                    new_predicates.push((target_relation, pred));
                }
            }
        }

        if new_predicates.is_empty() {
            None
        } else {
            Some(new_predicates)
        }
    }

    pub(super) fn refine_from_trace(
        &mut self,
        trace: &[usize],
        trace_tree: &[TraceTreeNode],
    ) -> CexAnalysis {
        // Tree interpolation first: handles multi-branch counterexamples where
        // a linear trace can miss sibling constraints.
        if let Some(predicates) = self.try_tree_interpolation(trace_tree) {
            if !predicates.is_empty() {
                return CexAnalysis::Spurious(predicates);
            }
        }

        // Try sequence interpolation first (mutually consistent interpolants),
        // then fall back to independent point-by-point interpolation.
        if let Some(predicates) = self.try_sequence_interpolation(trace) {
            if !predicates.is_empty() {
                return CexAnalysis::Spurious(predicates);
            }
        }

        // Fall back to independent binary interpolation at each split point.
        self.refine_from_trace_pointwise(trace)
    }

    /// Sequence interpolation: extract mutually consistent interpolants for all
    /// split points in a single pass.
    ///
    /// For a trace [step_0, step_1, ..., step_n], identifies boundary points
    /// where clauses have predicate heads. Then computes cumulative A/B
    /// interpolants: at boundary k, A = steps 0..=k and B = steps k+1..end.
    ///
    /// The interpolant from boundary k is added to the A-side for boundary k+1,
    /// ensuring mutual consistency: I_k AND constraints_{k+1} => I_{k+1}.
    ///
    /// Reference: Eldarica LinTreeInterpolator
    /// `reference/eldarica/src/main/scala/lazabs/horn/predgen/LinTreeInterpolator.scala:49-131`
    fn try_sequence_interpolation(
        &mut self,
        trace: &[usize],
    ) -> Option<Vec<(PredicateId, ChcExpr)>> {
        if trace.len() < 2 {
            return None;
        }

        let verbose = self.config.base.verbose;

        // Phase 1: Rename variables per step (same as pointwise)
        let mut step_substs: Vec<Vec<(ChcVar, ChcExpr)>> = Vec::new();
        let mut step_constraints: Vec<ChcExpr> = Vec::new();

        for (step, &edge_idx) in trace.iter().enumerate() {
            let edge = &self.edges[edge_idx];
            let clause = &self.problem.clauses()[edge.clause_index];
            let subst = rename_clause_vars(clause, "_seq", step);
            step_constraints.push(
                clause
                    .body
                    .constraint
                    .as_ref()
                    .map_or(ChcExpr::Bool(true), |c| c.substitute(&subst)),
            );
            step_substs.push(subst);
        }

        // Phase 2: Build linking equalities between steps
        let links = self.build_trace_links(trace, &step_substs);

        // Phase 3: Identify split points (steps with predicate heads, not the last step)
        struct SplitPoint {
            step: usize,
            relation: PredicateId,
            head_args: Vec<ChcExpr>,
        }
        let mut split_points: Vec<SplitPoint> = Vec::new();

        for (step_idx, &edge_idx) in trace.iter().enumerate() {
            if step_idx + 1 >= trace.len() {
                continue; // Last step (query) is not a split point
            }
            let edge = &self.edges[edge_idx];
            let clause = &self.problem.clauses()[edge.clause_index];
            if let ClauseHead::Predicate(pid, ref args) = clause.head {
                split_points.push(SplitPoint {
                    step: step_idx,
                    relation: pid,
                    head_args: args.clone(),
                });
            }
        }

        if split_points.is_empty() {
            return None;
        }

        // Phase 4: Verify the full trace is UNSAT
        let mut all_parts: Vec<ChcExpr> = step_constraints.clone();
        for link in &links {
            all_parts.extend(link.equalities.iter().cloned());
        }
        let full_formula = ChcExpr::and_all(all_parts);
        let full_check = self
            .smt
            .check_sat_with_timeout(&full_formula, self.config.query_timeout);
        if !full_check.is_unsat() {
            if verbose {
                safe_eprintln!("CEGAR seq-interp: full trace is SAT or Unknown, skipping");
            }
            return None;
        }

        // Phase 5: Cumulative sequence interpolation
        // For each split point k, build:
        //   A = constraints for steps 0..=k + links within 0..=k + interface equalities
        //       + previous interpolant (if any)
        //   B = interface equalities + constraints for steps k+1..end + links within k+1..end
        //
        // The interpolant at k is propagated as an A-side constraint for k+1.
        let mut new_predicates: Vec<(PredicateId, ChcExpr)> = Vec::new();
        let mut prev_interpolant: Option<ChcExpr> = None;

        for sp in &split_points {
            let canonical_vars = self.canonical_vars(sp.relation);
            let iface_vars: Vec<ChcVar> = canonical_vars
                .iter()
                .enumerate()
                .map(|(i, cv)| ChcVar::new(format!("_siface_{i}"), cv.sort.clone()))
                .collect();
            let iface_names: FxHashSet<String> =
                iface_vars.iter().map(|v| v.name.clone()).collect();

            // A-part: steps 0..=sp.step
            let mut a_parts: Vec<ChcExpr> = Vec::new();
            a_parts.extend(step_constraints[..=sp.step].iter().cloned());
            // A-side links (both endpoints within A)
            for link in &links {
                if link.from_step <= sp.step && link.to_step <= sp.step {
                    a_parts.extend(link.equalities.iter().cloned());
                }
            }
            // Interface: head args at split step == iface vars
            for (h_arg, iface_v) in sp.head_args.iter().zip(iface_vars.iter()) {
                let renamed_head = h_arg.substitute(&step_substs[sp.step]);
                a_parts.push(ChcExpr::eq(renamed_head, ChcExpr::var(iface_v.clone())));
            }
            // Propagate previous interpolant (key for mutual consistency)
            if let Some(ref prev_itp) = prev_interpolant {
                a_parts.push(prev_itp.clone());
            }

            // B-part: steps sp.step+1..end
            let mut b_parts: Vec<ChcExpr> = Vec::new();
            b_parts.extend(step_constraints[(sp.step + 1)..].iter().cloned());
            // B-side links (both endpoints within B)
            for link in &links {
                if link.from_step > sp.step && link.to_step > sp.step {
                    b_parts.extend(link.equalities.iter().cloned());
                }
            }
            // Interface: iface vars == body args at the next step consuming this head
            for link in &links {
                if link.from_step == sp.step && link.to_step > sp.step {
                    let next_clause =
                        &self.problem.clauses()[self.edges[trace[link.to_step]].clause_index];
                    for (body_pred_id, body_args) in &next_clause.body.predicates {
                        if *body_pred_id == sp.relation && body_args.len() == sp.head_args.len() {
                            for (iface_v, b_arg) in iface_vars.iter().zip(body_args.iter()) {
                                let renamed_body = b_arg.substitute(&step_substs[link.to_step]);
                                b_parts
                                    .push(ChcExpr::eq(ChcExpr::var(iface_v.clone()), renamed_body));
                            }
                            break;
                        }
                    }
                }
            }

            if b_parts.is_empty() {
                continue;
            }

            // Resolve equalities and try interpolation
            let a_resolved = Self::resolve_equalities(&a_parts, &iface_names);
            let b_resolved = Self::resolve_equalities(&b_parts, &iface_names);

            if verbose {
                safe_eprintln!(
                    "CEGAR seq-interp: split {} (pred P{}) A-parts={} B-parts={}",
                    sp.step,
                    sp.relation.index(),
                    a_resolved.len(),
                    b_resolved.len()
                );
            }

            let interpolant =
                self.try_interpolation_cascade(sp.step, &a_resolved, &b_resolved, &iface_names);

            if let Some(itp) = interpolant {
                // Map interpolant from _siface_* to canonical vars
                let mut back_subst = Vec::new();
                for (iface_v, canonical) in iface_vars.iter().zip(canonical_vars.iter()) {
                    back_subst.push((iface_v.clone(), ChcExpr::var(canonical.clone())));
                }
                let pred = itp.substitute(&back_subst);

                if verbose {
                    safe_eprintln!("CEGAR seq-interp: split {} -> predicate: {}", sp.step, pred);
                }

                if !matches!(pred, ChcExpr::Bool(true | false)) {
                    new_predicates.push((sp.relation, pred));
                }

                // Propagate: the interpolant (in iface vars) is added to A for the
                // next split point. This makes the next interpolant consistent with
                // this one: I_k AND constraints_{k+1} => I_{k+1}.
                prev_interpolant = Some(itp);
            } else {
                // If interpolation fails at this point, break the chain.
                // Previous interpolants are still valid.
                if verbose {
                    safe_eprintln!(
                        "CEGAR seq-interp: split {} interpolation failed, chain broken",
                        sp.step
                    );
                }
                prev_interpolant = None;
            }
        }

        if new_predicates.is_empty() {
            None
        } else {
            if verbose {
                safe_eprintln!(
                    "CEGAR seq-interp: extracted {} predicates from {} split points",
                    new_predicates.len(),
                    split_points.len()
                );
            }
            Some(new_predicates)
        }
    }
}
