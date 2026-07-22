// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Global generalization via cluster-driven convex closure.
//!
//! This module implements Spacer's global generalizer subsumption rule:
//! "Global Guidance for Local Generalization in Model Checking" (CAV 2020).
//!
//! # Algorithm
//!
//! Given a cluster of similar blocking cubes that differ only in numeric constants:
//! 1. Run convex closure over the substitution points (pattern variable values)
//! 2. Build `full_cc := pattern ∧ cc_constraints`
//! 3. Project away pattern variables using MBP
//! 4. Weaken the result until it's implied by `full_cc`
//!
//! The result is a generalized blocking cube that subsumes all members of the cluster.
//!
//! # References
//!
//! - Z3: `reference/z3/src/muz/spacer/spacer_global_generalizer.cpp`
//! - Design: the development design notes
//! - Issue: #1298

use crate::convex_closure::ConvexClosure;
use crate::mbp::Mbp;
use crate::smt::SmtResult;
use crate::{ChcExpr, SmtValue};
use ay_core::kani_compat::DetHashMap as FxHashMap;

use super::lemma_cluster::LemmaCluster;
use super::solver::PdrSolver;

/// Maximum pattern variables to allow for subsume attempt
const MAX_PATTERN_VARS: usize = 6;

/// Maximum cluster members to consider for CC
const MAX_CLUSTER_MEMBERS: usize = 8;

/// Maximum SMT queries per subsume attempt
const MAX_SMT_QUERIES: usize = 20;

impl PdrSolver {
    /// Attempt Spacer-style cluster subsumption over a cluster.
    ///
    /// Returns Some(blocking_cube) if subsumption succeeds, None otherwise.
    /// The returned cube is more general than any individual cluster member.
    ///
    /// # Algorithm
    ///
    /// 1. Preconditions: cluster has ≥2 members, all Int pattern vars, bounded size
    /// 2. Run convex closure over substitution points
    /// 3. Build `full_cc := pattern ∧ cc_constraints`
    /// 4. Get a model for `full_cc`
    /// 5. Project away pattern variables using MBP
    /// 6. Weaken until implied by `full_cc`
    /// 7. Verify the result is inductive
    pub(super) fn try_cluster_subsume(
        &mut self,
        cluster: &LemmaCluster,
        current_level: usize,
    ) -> Option<ChcExpr> {
        // --- Preconditions ---

        // Need at least 2 members (pointless otherwise)
        if cluster.members.len() < 2 {
            return None;
        }

        // Limit pattern variable count to bound SMT work
        if cluster.pattern_vars.len() > MAX_PATTERN_VARS {
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: Cluster subsume skipped - too many pattern vars ({} > {})",
                    cluster.pattern_vars.len(),
                    MAX_PATTERN_VARS
                );
            }
            return None;
        }

        // Limit members considered (take most recent)
        let members_to_use: Vec<_> = cluster
            .members
            .iter()
            .rev()
            .take(MAX_CLUSTER_MEMBERS)
            .collect();

        // --- Convex Closure over substitution points ---

        let mut cc = ConvexClosure::new();
        cc.reset(cluster.pattern_vars.clone());

        for member in &members_to_use {
            // i128-lockstep: ConvexClosure is i64-based; skip members whose
            // substitution values don't fit i64. The resulting candidate is
            // verified by is_inductive_blocking before adoption, so dropping
            // points only affects candidate quality, never soundness.
            let values: Option<Vec<i64>> = member
                .subst_values
                .iter()
                .map(|&v| i64::try_from(v).ok())
                .collect();
            if let Some(values) = values {
                cc.add_data_point(&values);
            }
        }

        let cc_result = cc.compute();
        if cc_result.is_empty() {
            // No constraints discovered - CC doesn't help
            return None;
        }

        // --- Build full_cc := pattern ∧ cc_constraints ---

        let cc_constraints: Vec<ChcExpr> = cc_result
            .equalities
            .into_iter()
            .chain(cc_result.bounds)
            .chain(cc_result.divisibility)
            .collect();

        let full_cc = if cc_constraints.is_empty() {
            cluster.pattern.clone()
        } else {
            let mut all = vec![cluster.pattern.clone()];
            all.extend(cc_constraints);
            ChcExpr::and_all(all)
        };

        // --- Get a model for full_cc ---

        self.smt.reset();
        match self.smt.check_sat(&full_cc) {
            SmtResult::Sat(model) => {
                // Continue with model
                self.try_cluster_subsume_with_model(cluster, &full_cc, &model, current_level)
            }
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                // full_cc is UNSAT - something is wrong or CC is too restrictive
                if self.config.verbose {
                    safe_eprintln!("PDR: Cluster subsume - full_cc is UNSAT, skipping");
                }
                None
            }
            SmtResult::Unknown => {
                // Solver gave up
                None
            }
        }
    }

    fn try_cluster_subsume_with_model(
        &mut self,
        cluster: &LemmaCluster,
        full_cc: &ChcExpr,
        model: &FxHashMap<String, SmtValue>,
        current_level: usize,
    ) -> Option<ChcExpr> {
        // --- Project away pattern variables ---

        let mbp = Mbp::new();
        let projected = mbp.project(full_cc, &cluster.pattern_vars, model);

        // --- Weaken until implied by full_cc ---

        let candidate = self.weaken_until_implied(full_cc, &projected);

        // Check if candidate is trivial
        if candidate == ChcExpr::Bool(true) {
            // Would create lemma `false` - useless
            return None;
        }

        // --- Acceptance check ---

        // Choose target level: min(cluster_min_level, current_level)
        let cluster_min_level = cluster.min_level().unwrap_or(current_level);
        let target_level = cluster_min_level.min(current_level);

        // Verify inductiveness
        if self.is_inductive_blocking(&candidate, cluster.predicate, target_level) {
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: Cluster subsume SUCCESS - generalized {} members to: {}",
                    cluster.members.len(),
                    candidate
                );
            }
            Some(candidate)
        } else {
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: Cluster subsume - candidate not inductive at level {}",
                    target_level
                );
            }
            None
        }
    }

    /// Weaken formula by dropping conjuncts while maintaining implication from full_cc.
    ///
    /// This is the `over_approximate` procedure from Z3 Spacer.
    fn weaken_until_implied(&mut self, full_cc: &ChcExpr, projected: &ChcExpr) -> ChcExpr {
        // Flatten projected into conjuncts
        let mut conjuncts = projected.collect_conjuncts_nontrivial();

        if conjuncts.is_empty() {
            return projected.clone();
        }

        let mut queries = 0;
        let mut i = 0;

        while i < conjuncts.len() && queries < MAX_SMT_QUERIES {
            // Try dropping conjunct i
            let without_i: Vec<_> = conjuncts
                .iter()
                .enumerate()
                .filter_map(|(j, c)| if j != i { Some(c.clone()) } else { None })
                .collect();

            let candidate = if without_i.is_empty() {
                ChcExpr::Bool(true)
            } else {
                ChcExpr::and_all(without_i)
            };

            // Check if full_cc => candidate (i.e., full_cc ∧ ¬candidate is UNSAT)
            let check_formula = ChcExpr::and(full_cc.clone(), ChcExpr::not(candidate.clone()));
            self.smt.reset();
            queries += 1;

            match self.smt.check_sat(&check_formula) {
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                    // Implication holds - can drop conjunct i
                    conjuncts.remove(i);
                    // Don't increment i - next element shifts into position i
                }
                _ => {
                    // Can't drop - keep and move to next
                    i += 1;
                }
            }
        }

        // Rebuild formula from remaining conjuncts
        if conjuncts.is_empty() {
            ChcExpr::Bool(true)
        } else {
            ChcExpr::and_all(conjuncts)
        }
    }
}

#[allow(clippy::unwrap_used, clippy::panic)]
#[cfg(test)]
mod tests;
