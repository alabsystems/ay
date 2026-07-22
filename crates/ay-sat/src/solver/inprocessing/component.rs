// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Formula component decomposition integration.
//!
//! Runs `component::find_components` analysis after BVE + subsumption during
//! preprocessing to detect whether the formula decomposes into independent
//! subproblems.
//!
//! When beneficial (multiple large components), constructs independent sub-solvers
//! for each component and solves them separately. SAT iff all components are SAT,
//! UNSAT iff any component is UNSAT.
//!
//! Reference: CryptoMiniSat comphandler.cpp / compfinder.cpp (removed from
//! modern CMS, but the algorithm is standard).

use super::super::*;

impl Solver {
    /// Analyze the formula for connected component structure.
    ///
    /// Returns `true` if the formula decomposes into multiple beneficial
    /// components (>1 component with >= 10 variables each).
    pub(in crate::solver) fn analyze_components(&mut self) -> bool {
        if !self.require_level_zero() {
            return false;
        }

        let num_vars = self.num_vars;
        let arena = &self.arena;

        // live_indices (husk adjudication #1): garbage-kept husks are
        // logically deleted and must not contribute edges to the variable
        // interaction graph.
        let clause_data: Vec<Vec<Literal>> = arena
            .live_indices()
            .filter(|&idx| !arena.is_learned(idx) && arena.len_of(idx) >= 2)
            .map(|idx| arena.literals(idx).to_vec())
            .collect();

        let result = crate::component::find_components(
            num_vars,
            clause_data.iter().map(Vec::as_slice),
            |vi| self.is_active_component_var(vi),
        );

        self.cold.component_stats.runs += 1;
        if result.num_components > 1 {
            self.cold.component_stats.decomposable_found += 1;
        }
        let max = result.num_components as u64;
        if max > self.cold.component_stats.max_components {
            self.cold.component_stats.max_components = max;
        }

        if result.num_components > 1 {
            tracing::info!(
                components = result.num_components,
                sizes = ?result.component_sizes,
                beneficial = result.beneficial,
                "component analysis: formula decomposes into {} components",
                result.num_components,
            );
        } else {
            tracing::debug!(
                components = result.num_components,
                "component analysis: single connected component (no decomposition)"
            );
        }

        result.beneficial
    }

    /// Try to solve by decomposing into independent components.
    ///
    /// After preprocessing, if multiple disconnected components exist, constructs
    /// a fresh sub-solver for each and solves independently.
    ///
    /// Returns `Some(SatResult)` if decomposition succeeded, `None` if skipped.
    ///
    /// Skipped when: proof logging active, scope selectors active, single
    /// component, or components too small.
    pub(in crate::solver) fn try_decompose_solve(&mut self) -> Option<SatResult> {
        if self.proof_manager.is_some() {
            tracing::debug!("decompose_solve: skipping (proof logging active)");
            return None;
        }
        if !self.cold.scope_selectors.is_empty() {
            tracing::debug!("decompose_solve: skipping (scope selectors active)");
            return None;
        }
        if !self.require_level_zero() {
            return None;
        }

        let num_vars = self.num_vars;

        // live_indices (husk adjudication #1, FALSE-UNSAT fix): a garbage-kept
        // husk (e.g. congruence forward subsumption via mark_garbage_keep_data)
        // whose variable is later BVE-eliminated would otherwise enter
        // clause_data; the eliminated variable maps to remap[v]==u32::MAX and
        // the literal-drop below would inject a strengthened phantom clause
        // into the sub-solver, producing a reachable false UNSAT (this path
        // runs exactly when proof logging is off, so there is no proof gate).
        let clause_data: Vec<Vec<Literal>> = self
            .arena
            .live_indices()
            .filter(|&idx| !self.arena.is_learned(idx) && self.arena.len_of(idx) >= 2)
            .map(|idx| self.arena.literals(idx).to_vec())
            .collect();

        let (result, decomp) = crate::component::find_components_detailed(
            num_vars,
            clause_data.iter().map(Vec::as_slice),
            |vi| self.is_active_component_var(vi),
        );

        if !result.beneficial || decomp.num_components < 2 {
            return None;
        }

        // Skip decomposition when the largest component dominates the formula
        // (>80% of active variables). In this case, the small components are
        // trivial (often solvable by BCP) and the sub-solver overhead for the
        // large component (new solver allocation, re-preprocessing, recursive
        // decomposition) outweighs any benefit.
        //
        // #8448: Lowered from 90% to 80%. FmlaEquivChain decomposes into 218
        // components where the largest is 88% of the formula (54372 out of
        // 61122 active vars). At the 90% threshold this slipped through,
        // causing the sub-solver to re-preprocess a 54K-var formula from
        // scratch. The sub-solver's preprocessing is nearly as expensive as
        // the original, and the timeout propagates through the interrupt
        // handle — so the entire 15s budget is consumed by redundant
        // preprocessing of the dominant component. At 80%, decomposition
        // only fires when the non-trivial components represent a meaningful
        // fraction of the work, making the sub-solver overhead worthwhile.
        let total_active: usize = result.component_sizes.iter().sum();
        if let Some(&largest) = result.component_sizes.first() {
            if total_active > 0 && largest * 100 / total_active > 80 {
                tracing::debug!(
                    largest,
                    total_active,
                    pct = largest * 100 / total_active,
                    "decompose_solve: skipping (largest component >80% of formula)"
                );
                return None;
            }
        }

        tracing::info!(
            num_components = decomp.num_components,
            sizes = ?result.component_sizes,
            "decompose_solve: splitting into {} independent components",
            decomp.num_components,
        );

        let t0 = ay_core::time::Instant::now();

        // Build per-component variable remapping: original var -> local var.
        let mut remap: Vec<u32> = vec![u32::MAX; num_vars];
        for component_vars in &decomp.components {
            for (local_idx, &orig_vi) in component_vars.iter().enumerate() {
                remap[orig_vi] = local_idx as u32;
            }
        }

        // Combined model: start with current level-0 assignments.
        let mut combined_model = vec![false; num_vars];
        for (vi, val) in combined_model.iter_mut().enumerate().take(num_vars) {
            if self.var_is_assigned(vi) {
                let lit = Literal::positive(Variable(vi as u32));
                *val = self.vals[lit.index()] > 0;
            }
        }

        for (comp_id, component_vars) in decomp.components.iter().enumerate() {
            if component_vars.is_empty() {
                continue;
            }

            let comp_num_vars = component_vars.len();
            let mut sub_solver = Self::new(comp_num_vars);
            // Enable preprocessing on sub-solvers: component clauses are
            // residuals after the parent's BVE, but the component formula
            // itself has never been preprocessed. BVE/probing/vivification
            // on the component can dramatically reduce it (Kissat's cascade
            // pattern). Previously preprocess_enabled was false, which left
            // the sub-solver doing raw CDCL on ~350K clauses (#8134).
            // sub_solver.cold.preprocess_enabled is true by default.

            // Disable recursive decomposition in sub-solvers (#8448):
            // the parent already decomposed the formula. Recursive
            // decomposition of components wastes time on redundant
            // component analysis that rarely finds further decomposition.
            // On FmlaEquivChain, the sub-solver's second decomposition
            // (31 components, main=51K vars) adds overhead without
            // meaningful size reduction.
            sub_solver.set_decompose_enabled(false);

            // Disable lookahead in sub-solvers (#8448): lookahead is
            // expensive (O(vars) per round) and the parent already ran
            // lookahead at the top level. On FmlaEquivChain, the
            // sub-solver's lookahead round takes 5s (finding 772 failed
            // literals) — valuable but too expensive at 15s timeout.
            // Probing during preprocessing still runs (failed literal
            // detection without the full scoring overhead).
            sub_solver.cold.next_lookahead_conflict = u64::MAX;

            // Share interrupt handle so the parent's timeout propagates to
            // sub-solvers. Without this, the sub-solver runs indefinitely
            // and AY never returns a result (#8134).
            if let Some(ref handle) = self.cold.interrupt {
                sub_solver.set_interrupt(handle.clone());
            }

            for clause in &clause_data {
                // Find which component this clause belongs to.
                let clause_comp = clause.iter().find_map(|&lit| {
                    let vi = lit.variable().index();
                    let cid = decomp.var_component[vi];
                    if cid != u32::MAX {
                        Some(cid)
                    } else {
                        None
                    }
                });
                if clause_comp != Some(comp_id as u32) {
                    continue;
                }

                // Check if clause is satisfied by a level-0 assignment.
                let clause_satisfied = clause.iter().any(|&lit| {
                    let vi = lit.variable().index();
                    self.var_is_assigned(vi)
                        && self.var_data[vi].level == 0
                        && self.vals[lit.index()] > 0
                });
                if clause_satisfied {
                    continue;
                }

                // Remap literals to component-local variable indices.
                let mut remapped: Vec<Literal> = Vec::with_capacity(clause.len());
                for &lit in clause {
                    let vi = lit.variable().index();
                    let local = remap[vi];
                    if local == u32::MAX {
                        // Variable maps to no component. Dropping the literal
                        // is only sound when it is falsified at level 0 (the
                        // clause was already checked as not satisfied at level
                        // 0 above). Any other reason — e.g. a removed/BVE-
                        // eliminated variable leaking into a live clause —
                        // means the clause set is inconsistent with the
                        // decomposition; dropping would strengthen the clause
                        // into a phantom and can flip the verdict to a false
                        // UNSAT. Abort the decomposition instead (husk
                        // adjudication #1, defense in depth).
                        let falsified_at_level0 = self.var_is_assigned(vi)
                            && self.var_data[vi].level == 0
                            && self.vals[lit.index()] < 0;
                        if falsified_at_level0 {
                            continue; // Root-falsified literal: sound to drop.
                        }
                        tracing::warn!(
                            var = vi,
                            clause = ?clause,
                            "decompose_solve: aborting — literal on unassigned \
                             component-less variable (removed var in live clause?)"
                        );
                        return None;
                    }
                    let local_var = Variable(local);
                    let remapped_lit = if lit.is_positive() {
                        Literal::positive(local_var)
                    } else {
                        Literal::negative(local_var)
                    };
                    remapped.push(remapped_lit);
                }

                if remapped.is_empty() {
                    self.cold.component_stats.decompose_solves += 1;
                    self.cold.component_stats.decompose_unsat += 1;
                    return Some(self.declare_unsat());
                }

                sub_solver.add_clause(remapped);
            }

            let sub_result = sub_solver.solve();
            let sub_result = sub_result.into_inner();

            match sub_result {
                SatResult::Sat(model) => {
                    for (local_idx, &orig_vi) in component_vars.iter().enumerate() {
                        if local_idx < model.len() {
                            combined_model[orig_vi] = model[local_idx];
                        }
                    }
                    tracing::debug!(
                        component = comp_id,
                        vars = comp_num_vars,
                        "decompose_solve: component {} SAT",
                        comp_id,
                    );
                }
                SatResult::Unsat(_) => {
                    tracing::info!(
                        component = comp_id,
                        vars = comp_num_vars,
                        elapsed_ms = t0.elapsed().as_millis(),
                        "decompose_solve: component {} UNSAT => formula UNSAT",
                        comp_id,
                    );
                    self.cold.component_stats.decompose_solves += 1;
                    self.cold.component_stats.decompose_unsat += 1;
                    return Some(self.declare_unsat());
                }
                SatResult::Unknown => {
                    tracing::debug!(
                        component = comp_id,
                        "decompose_solve: component {} Unknown, aborting",
                        comp_id,
                    );
                    return None;
                }
            }
        }

        tracing::info!(
            num_components = decomp.num_components,
            elapsed_ms = t0.elapsed().as_millis(),
            "decompose_solve: all {} components SAT",
            decomp.num_components,
        );

        self.cold.component_stats.decompose_solves += 1;
        self.cold.component_stats.decompose_sat += 1;

        // #7912: Route through declare_sat_from_model for universal model
        // verification. The combined_model is in internal variable space.
        // finalize_sat_model applies the parent's BVE reconstruction entries,
        // verifies against the original formula (always-on), and truncates
        // to user_num_vars. Previously this returned SatResult::Sat directly,
        // bypassing all model verification and reconstruction.
        Some(self.declare_sat_from_model(combined_model))
    }

    /// Check if a variable is active for component analysis.
    fn is_active_component_var(&self, vi: usize) -> bool {
        if vi >= self.num_vars {
            return false;
        }
        if self.var_is_assigned(vi) && self.var_data[vi].level == 0 {
            return false;
        }
        !self.var_lifecycle.is_removed(vi)
    }
}
