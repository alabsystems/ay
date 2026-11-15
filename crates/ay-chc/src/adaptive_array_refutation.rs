// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Bounded original-clause refutation for small linear BV/array loops.
//!
//! This is derivation-tree BMC, not a safety argument: exhaustion, cancellation,
//! or an incomplete model only releases the slice to the invariant engines.

use crate::adaptive::AdaptivePortfolio;
use crate::adaptive_decision_log::DecisionEntry;
use crate::adaptive_route_admission::{scan_problem_surface, RouteSurfaceCaps};
use crate::bmc::{BmcConfig, BmcSolver};
use crate::classifier::ProblemFeatures;
use crate::engine_config::ChcEngineConfig;
use crate::engine_result::ValidationEvidence;
use crate::portfolio::PortfolioResult;
use crate::{ChcExpr, ChcProblem, ChcSort, ClauseHead};
use ay_core::time::Instant;
use std::time::Duration;

const MAX_DEPTH: usize = 20;
const MAX_NODES: usize = 512;
const MAX_MEMORY: usize = 512 * 1024 * 1024;

fn finite_sort(sort: &ChcSort) -> bool {
    match sort {
        ChcSort::Bool => true,
        ChcSort::BitVec(width) => (1..=128).contains(width),
        ChcSort::Array(key, value) => finite_sort(key) && finite_sort(value),
        _ => false,
    }
}

// Called only after the source node/depth scan. The existing executor sort
// guard precedes exact sort computation, so malformed width-changing terms
// refuse before typed builders or native BV value allocation. Check every
// intermediate, including repeats/concatenations hidden below Boolean guards.
fn finite_term(expr: &ChcExpr, progress: &mut dyn FnMut() -> bool) -> bool {
    if !progress() {
        return false;
    }
    if crate::expr::dag::children(expr)
        .iter()
        .any(|child| !finite_term(child, progress))
    {
        return false;
    }
    if crate::smt::executor_sort_guard::unsupported_executor_expr_reason(expr).is_some() {
        return false;
    }
    finite_sort(&expr.sort()) && progress()
}

fn finite_source(problem: &ChcProblem, progress: &mut dyn FnMut() -> bool) -> bool {
    for predicate in problem.predicates() {
        if !progress() || !predicate.arg_sorts.iter().all(finite_sort) {
            return false;
        }
    }
    for clause in problem.clauses() {
        if let Some(constraint) = &clause.body.constraint {
            if !finite_term(constraint, progress) {
                return false;
            }
        }
        for (_, args) in &clause.body.predicates {
            if args.iter().any(|arg| !finite_term(arg, progress)) {
                return false;
            }
        }
        if let ClauseHead::Predicate(_, args) = &clause.head {
            if args.iter().any(|arg| !finite_term(arg, progress)) {
                return false;
            }
        }
    }
    progress()
}

fn source_caps() -> RouteSurfaceCaps {
    RouteSurfaceCaps {
        max_clauses: 128,
        max_predicates: 128,
        max_predicate_arity: 64,
        max_actions: 0,
        max_datatype_defs: 0,
        max_datatype_members: 0,
        max_body_atoms_per_clause: 1,
        max_total_body_atoms: 128,
        max_expr_nodes_per_clause: 4096,
        max_total_expr_nodes: 32768,
        max_expr_depth: 64,
        max_total_sort_nodes: 32768,
        max_sort_depth: 16,
        max_variable_occurrences_per_clause: 4096,
        max_array_selects: 512,
        max_const_key_rewrite_visits: 65536,
        max_total_name_bytes: 256 * 1024,
    }
}

impl AdaptivePortfolio {
    pub(crate) fn try_linear_bv_array_refutation(
        &self,
        features: &ProblemFeatures,
        deadline: Option<Instant>,
    ) -> Option<(PortfolioResult, ValidationEvidence)> {
        // This probe uses wall-bounded executor batches. It cannot enter a
        // counted proof run until those batches charge the run's effort node.
        if BmcSolver::closed_under_effort() {
            return None;
        }
        // Structural admission is independent of symbol names and constants.
        if !features.uses_arrays
            || !features.is_linear
            || !features.has_cycles
            || features.num_facts == 0
            || features.num_queries == 0
            || features.num_clauses > 128
            || features.num_predicates > 128
        {
            return None;
        }
        let started = Instant::now();
        let remaining = self
            .remaining_budget(deadline)
            .unwrap_or(Duration::from_secs(8));
        let budget = (remaining / 4).min(Duration::from_secs(8));
        let log = |admitted, reason: String, result| {
            self.decision_log.log_decision(DecisionEntry {
                stage: "linear_bv_array_refutation",
                gate_result: admitted,
                gate_reason: reason,
                budget_secs: budget.as_secs_f64(),
                elapsed_secs: started.elapsed().as_secs_f64(),
                result,
                lemmas_learned: 0,
                max_frame: 0,
            });
        };
        if budget < Duration::from_millis(50) || self.budget_exhausted(deadline) {
            log(
                false,
                "no bounded refutation slice remained".to_string(),
                "skipped",
            );
            return None;
        }
        let route_deadline = started + budget;
        let _deadline = crate::smt::ScopedSmtDeadline::install_until(route_deadline);
        let memory = Some(
            self.config
                .memory_budget
                .unwrap_or(MAX_MEMORY)
                .min(MAX_MEMORY),
        );
        let _memory = crate::smt::SmtContext::scoped_thread_term_memory_budget(memory);
        let stats = match scan_problem_surface(
            &self.problem,
            source_caps(),
            &self.cancellation_token,
            route_deadline,
        ) {
            Ok(stats) => stats,
            Err(reason) => {
                log(
                    false,
                    format!("bounded original-source admission refused: {reason:?}"),
                    "unknown",
                );
                return None;
            }
        };
        // Bound the product of source size and tree expansion before cloning.
        // This is an AST/name work envelope, not an RSS or hard-deadline claim.
        let expansion_fits = stats
            .total_expr_nodes
            .checked_add(stats.total_sort_nodes)
            .and_then(|nodes| nodes.checked_mul(MAX_NODES))
            .is_some_and(|work| work <= 4_000_000)
            && stats
                .total_name_bytes
                .checked_mul(MAX_NODES)
                .is_some_and(|bytes| bytes <= 64 * 1024 * 1024);
        if !expansion_fits {
            log(
                false,
                "source/tree expansion work envelope exceeded".to_string(),
                "cap_exceeded",
            );
            return None;
        }
        if !finite_source(&self.problem, &mut || {
            !self.budget_exhausted(Some(route_deadline))
        }) {
            log(
                false,
                "unsupported/non-finite native term, width, or interrupted source".to_string(),
                "unknown",
            );
            return None;
        }
        // Recursive sort/clone operations follow the bounded source scan.
        if !self.problem.has_bv_sorts()
            || !self.problem.has_array_sorts()
            || self.problem.has_real_sorts()
            || self.problem.has_datatype_sorts()
        {
            return None;
        }
        if self.budget_exhausted(Some(route_deadline)) {
            return None;
        }
        let solver = BmcSolver::new(
            self.problem.clone(),
            BmcConfig {
                base: ChcEngineConfig {
                    verbose: self.config.verbose,
                    cancellation_token: Some(self.lane_token()),
                },
                smt_lane: crate::smt::SmtLane::Verification,
                max_depth: MAX_DEPTH,
                acyclic_safe: false,
                per_depth_timeout: Some(budget),
                time_budget: Some(budget),
                memory_budget: memory,
                ..BmcConfig::default()
            },
        );
        let available = route_deadline.saturating_duration_since(Instant::now());
        let candidate =
            solver.solve_array_committed_tree_refutation(MAX_DEPTH, available, MAX_NODES);
        if let PortfolioResult::Unsafe(counterexample) = candidate {
            // The search model and the legacy SMT-witness fallback grant no
            // authority here. Retain and recheck a ground derivation in the
            // caller's exact original namespace, including every query premise.
            if let Some(ground) = counterexample.ground_derivation.as_ref() {
                let valid = crate::ground_derivation::validate_ground_derivation_with_progress(
                    &self.problem,
                    ground,
                    &mut || !self.budget_exhausted(Some(route_deadline)),
                )
                .is_ok();
                if valid && !self.budget_exhausted(Some(route_deadline)) {
                    log(
                        true,
                        "bounded original-clause ground refutation".to_string(),
                        "unsafe",
                    );
                    return Some((
                        PortfolioResult::Unsafe(counterexample),
                        ValidationEvidence::BmcCounterexample,
                    ));
                }
            }
        }
        log(
            true,
            "no replayable original-space ground counterexample within bounds".to_string(),
            "unknown",
        );
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ChcOp;
    use std::sync::Arc;

    #[test]
    fn intermediate_width_and_malformed_terms_refuse_before_native_allocation() {
        let byte = || Arc::new(ChcExpr::BitVec(0, 8));
        let huge = ChcExpr::Op(ChcOp::BvRepeat(u32::MAX), vec![byte()]);
        assert!(!finite_term(&huge, &mut || true));
        let malformed = ChcExpr::Op(ChcOp::BvZeroExtend(8), vec![Arc::new(ChcExpr::Bool(true))]);
        assert!(!finite_term(&malformed, &mut || true));
        let wide = ChcExpr::Op(ChcOp::BvRepeat(17), vec![byte()]);
        let hidden = ChcExpr::eq(wide.clone(), wide);
        assert!(!finite_term(&hidden, &mut || true));
        let pointer_pair = ChcExpr::Op(
            ChcOp::BvConcat,
            vec![
                Arc::new(ChcExpr::BitVec(0, 64)),
                Arc::new(ChcExpr::BitVec(0, 64)),
            ],
        );
        assert!(finite_term(&pointer_pair, &mut || true));
        assert!(!finite_term(&pointer_pair, &mut || false));
    }
}
