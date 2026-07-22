// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! DAR (Dual Approximated Reachability) engine for CHC problems.
//!
//! Port of Golem's DAR engine (`reference/golem/src/engine/DAR.cc`) for AY's
//! `TransitionSystem` abstraction. Part of #431.
//!
//! DAR maintains two sequences of over-approximations:
//! - Forward sequence: `F[0]=Init, F[1], ..., F[n]` (forward reachable sets)
//! - Backward sequence: `B[0]=Query, B[1], ..., B[n]` (backward reachable sets)
//!
//! At each step, it tries to interpolate between `F[i] ∧ T` and `B[n-i]'`
//! (where `'` denotes the next-state version). When interpolation succeeds,
//! it strengthens both sequences. Fixpoint is detected when some `F[i]` is
//! implied by `F[0] ∨ ... ∨ F[i-1]`.
//!
//! The key advantage: the invariant is naturally disjunctive:
//! `Inv = F[0] ∨ F[1] ∨ ... ∨ F[k]`
//!
//! MVP scope: single-predicate, linear CHC transition systems only.

use crate::engine_config::ChcEngineConfig;
use crate::engine_result::build_single_pred_model;
use crate::engine_utils::{check_sat_with_timeout, search_budget_exhausted};
use crate::interpolant_validation::{
    collect_conjuncts_for_interpolation, is_valid_interpolant_with_check_sat,
    validate_inductive_invariant,
};
use crate::interpolation::{interpolating_sat_constraints, InterpolatingSatResult};
use crate::smt::SmtResult;
use crate::transition_system::TransitionSystem;
use crate::{ChcExpr, ChcProblem, ChcSort};
use ay_core::kani_compat::DetHashSet as FxHashSet;
use ay_core::time::Instant;
use std::fmt;
use std::time::Duration;

/// DAR solver result (type alias for unified ChcEngineResult).
pub(crate) type DarResult = crate::engine_result::ChcEngineResult;

/// DAR solver configuration.
#[derive(Debug, Clone)]
pub struct DarConfig {
    /// Common engine settings (verbose, cancellation).
    pub base: ChcEngineConfig,
    /// Maximum unrolling depth n (default: 50).
    pub max_n: usize,
    /// Timeout per SMT query.
    pub query_timeout: Duration,
    /// Total solver timeout.
    pub total_timeout: Duration,
}

impl Default for DarConfig {
    fn default() -> Self {
        Self {
            base: ChcEngineConfig::default(),
            max_n: 50,
            query_timeout: Duration::from_secs(5),
            total_timeout: Duration::from_secs(30),
        }
    }
}

/// Applicability summary for the DAR engine.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DarReadinessReport {
    pub(crate) predicate_count: usize,
    pub(crate) clause_count: usize,
    pub(crate) state_var_count: usize,
    pub(crate) status: DarReadinessStatus,
}

impl DarReadinessReport {
    pub(crate) fn analyze(problem: &ChcProblem) -> Self {
        let predicate_count = problem.predicates().len();
        let clause_count = problem.clauses().len();
        let state_var_count = problem
            .predicates()
            .first()
            .map_or(0, |predicate| predicate.arg_sorts.len());

        let status = analyze_dar_readiness(problem);

        Self {
            predicate_count,
            clause_count,
            state_var_count,
            status,
        }
    }

    pub(crate) fn is_ready(&self) -> bool {
        matches!(self.status, DarReadinessStatus::Ready)
    }

    pub(crate) fn blocker(&self) -> Option<&DarReadinessBlocker> {
        match &self.status {
            DarReadinessStatus::Ready => None,
            DarReadinessStatus::NotApplicable(blocker) => Some(blocker),
        }
    }
}

/// DAR readiness state.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum DarReadinessStatus {
    Ready,
    NotApplicable(DarReadinessBlocker),
}

/// First reason DAR cannot soundly enter its transition-system loop.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum DarReadinessBlocker {
    PredicateCount {
        actual: usize,
    },
    NonLinearClause {
        clause_index: usize,
        body_predicate_count: usize,
    },
    MissingFact,
    MissingTransition,
    MissingQuery,
    UnsupportedStateSort {
        sort: ChcSort,
    },
}

impl fmt::Display for DarReadinessBlocker {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::PredicateCount { actual } => {
                write!(f, "expected one predicate, found {actual}")
            }
            Self::NonLinearClause {
                clause_index,
                body_predicate_count,
            } => write!(
                f,
                "clause {clause_index} has {body_predicate_count} body predicates"
            ),
            Self::MissingFact => f.write_str("no fact clause for the analyzed predicate"),
            Self::MissingTransition => {
                f.write_str("no self-transition clause for the analyzed predicate")
            }
            Self::MissingQuery => f.write_str("no query clause for the analyzed predicate"),
            Self::UnsupportedStateSort { sort } => {
                write!(f, "state sort {sort} is unsupported by DAR interpolation")
            }
        }
    }
}

fn analyze_dar_readiness(problem: &ChcProblem) -> DarReadinessStatus {
    if problem.predicates().len() != 1 {
        return DarReadinessStatus::NotApplicable(DarReadinessBlocker::PredicateCount {
            actual: problem.predicates().len(),
        });
    }

    for (clause_index, clause) in problem.clauses().iter().enumerate() {
        let body_predicate_count = clause.body.predicates.len();
        if body_predicate_count > 1 {
            return DarReadinessStatus::NotApplicable(DarReadinessBlocker::NonLinearClause {
                clause_index,
                body_predicate_count,
            });
        }
    }

    let predicate = &problem.predicates()[0];
    for sort in &predicate.arg_sorts {
        if !dar_supports_state_sort(sort) {
            return DarReadinessStatus::NotApplicable(DarReadinessBlocker::UnsupportedStateSort {
                sort: sort.clone(),
            });
        }
    }

    let pred_id = predicate.id;
    if !problem
        .facts()
        .any(|fact| fact.head.predicate_id() == Some(pred_id))
    {
        return DarReadinessStatus::NotApplicable(DarReadinessBlocker::MissingFact);
    }

    if !problem.transitions().any(|transition| {
        transition.head.predicate_id() == Some(pred_id)
            && transition
                .body
                .predicates
                .first()
                .is_some_and(|(body_pred, _)| *body_pred == pred_id)
    }) {
        return DarReadinessStatus::NotApplicable(DarReadinessBlocker::MissingTransition);
    }

    if !problem.queries().any(|query| {
        query
            .body
            .predicates
            .first()
            .is_some_and(|(body_pred, _)| *body_pred == pred_id)
    }) {
        return DarReadinessStatus::NotApplicable(DarReadinessBlocker::MissingQuery);
    }

    DarReadinessStatus::Ready
}

fn dar_supports_state_sort(sort: &ChcSort) -> bool {
    match sort {
        // F1 (LRA-Lin unlock): Bool admitted alongside arithmetic/Array. Mixed
        // Bool+Real predicates dominate the track; the interpolating backend's
        // dual-MBP strategy handles Bool+LIA. DAR never returns Unsafe and its
        // Safe results are replayed against the ORIGINAL clauses by the portfolio
        // acceptance pipeline (#5660/#5877 fail-closed).
        ChcSort::Bool | ChcSort::Int | ChcSort::Real | ChcSort::Array(_, _) => true,
        ChcSort::BitVec(_) | ChcSort::Uninterpreted(_) | ChcSort::Datatype { .. } => false,
    }
}

/// DAR solver.
pub(crate) struct DarSolver {
    problem: ChcProblem,
    config: DarConfig,
}

impl Drop for DarSolver {
    fn drop(&mut self) {
        std::mem::take(&mut self.problem).iterative_drop();
    }
}

impl DarSolver {
    pub(crate) fn new(problem: ChcProblem, config: DarConfig) -> Self {
        Self { problem, config }
    }

    pub(crate) fn solve(&self) -> DarResult {
        let start = Instant::now();

        let readiness = DarReadinessReport::analyze(&self.problem);
        if !readiness.is_ready() {
            if self.config.base.verbose {
                if let Some(blocker) = readiness.blocker() {
                    safe_eprintln!("DAR: Not applicable: {}", blocker);
                }
            }
            return DarResult::NotApplicable;
        }

        let ts = match TransitionSystem::from_chc_problem(&self.problem) {
            Ok(ts) => ts,
            Err(err) => {
                if self.config.base.verbose {
                    safe_eprintln!("DAR: Not applicable: {}", err);
                }
                return DarResult::NotApplicable;
            }
        };

        // Sort precheck: interpolation supports arithmetic sorts, Array, AND Bool
        // state vars (F1, the LRA-Lin unlock). Bool state vars are versioned and
        // the interpolating backend's dual-MBP strategy handles mixed Bool+LIA.
        // DAR only ever returns Safe/Unknown (never Unsafe), and Safe results are
        // replayed against the ORIGINAL clauses by the portfolio acceptance
        // pipeline (#5660/#5877 fail-closed).
        if let Some(bad_sort) = ts.find_unsupported_interpolation_state_sort_allowing_bool() {
            if self.config.base.verbose {
                safe_eprintln!(
                    "DAR: Not applicable: state variable has unsupported sort {}",
                    bad_sort
                );
            }
            return DarResult::NotApplicable;
        }
        for var in ts.state_vars() {
            if matches!(&var.sort, ChcSort::BitVec(_)) {
                if self.config.base.verbose {
                    safe_eprintln!(
                        "DAR: Not applicable: state variable has non-arithmetic sort {}",
                        var.sort
                    );
                }
                return DarResult::NotApplicable;
            }
        }

        // Base case: SAT(Init ∧ Query) => init state already bad.
        // We do NOT return Unsafe from DAR (skeleton counterexamples are unreliable
        // due to variable encoding differences in TransitionSystem). Instead we
        // just check unsatisfiability to decide whether interpolation can proceed.
        let init_and_query = ChcExpr::and(ts.init.clone(), ts.query.clone());
        if !self.check_sat(&init_and_query).is_unsat() {
            // Init intersects Query or unknown — BMC will find the real counterexample.
            return DarResult::Unknown;
        }

        // Initialize sequences: forward[0] = Init, backward[0] = Query
        let mut forward = vec![ts.init.clone()];
        let mut backward = vec![ts.query.clone()];
        let boundary_vars_t1 = ts.state_var_names_at(1);

        // First step: check Init ∧ T ∧ Query' (1-step reachability)
        let a_first = ChcExpr::and(ts.init.clone(), ts.transition_at(0));
        let b_first = ts.query_at(1);
        let check_first = ChcExpr::and(a_first.clone(), b_first.clone());

        if !self.check_sat(&check_first).is_unsat() {
            // 1-step reachability SAT or unknown — let BMC handle counterexample generation.
            return DarResult::Unknown;
        }

        // Compute initial interpolants for n=1
        // Forward interpolant: partition {Init, T} from {Query'}
        let mut a_constraints = Vec::new();
        collect_conjuncts_for_interpolation(&a_first, &mut a_constraints);
        let mut b_constraints = Vec::new();
        collect_conjuncts_for_interpolation(&b_first, &mut b_constraints);

        let fwd_itp = match interpolating_sat_constraints(
            &a_constraints,
            &b_constraints,
            &boundary_vars_t1,
        ) {
            InterpolatingSatResult::Unsat(i) => i,
            InterpolatingSatResult::Unknown => return DarResult::Unknown,
        };
        // Shift interpolant from time-1 vars back to time-0
        let fwd_itp_t0 = ts.shift_versioned_state_vars(&fwd_itp, -1);
        forward.push(fwd_itp_t0);

        // Backward interpolant: partition {Init} from {T, Query'}
        // Here A = {Init}, B = {T, Query'} at the time-0 boundary
        let boundary_vars_t0 = ts.state_var_names();
        let init_constraints = vec![ts.init.clone()];
        let mut tb_constraints = Vec::new();
        collect_conjuncts_for_interpolation(&ts.transition_at(0), &mut tb_constraints);
        collect_conjuncts_for_interpolation(&b_first, &mut tb_constraints);

        let bwd_itp = match interpolating_sat_constraints(
            &tb_constraints,
            &init_constraints,
            &boundary_vars_t0,
        ) {
            InterpolatingSatResult::Unsat(i) => i,
            InterpolatingSatResult::Unknown => {
                // Backward interpolation failed; continue with forward-only
                backward.push(ts.query.clone());
                return self.main_loop(&ts, &mut forward, &mut backward, start);
            }
        };
        backward.push(bwd_itp);

        self.main_loop(&ts, &mut forward, &mut backward, start)
    }

    fn main_loop(
        &self,
        ts: &TransitionSystem,
        forward: &mut Vec<ChcExpr>,
        backward: &mut Vec<ChcExpr>,
        start: Instant,
    ) -> DarResult {
        let boundary_vars_t1 = ts.state_var_names_at(1);

        for _iteration in 0..self.config.max_n {
            if search_budget_exhausted(&self.config.base, start, self.config.total_timeout) {
                return DarResult::Unknown;
            }

            // Local strengthening: find pair (F[i], B[n-i]) separable by one step
            if !self.local_strengthen(ts, forward, backward, &boundary_vars_t1, start) {
                // Local strengthening failed; try global strengthening
                if !self.global_strengthen(ts, forward, backward, &boundary_vars_t1, start) {
                    // Both failed: could be timeout, interpolation failure, or real
                    // unreachability failure. Return Unknown; only base-case SAT checks
                    // with explicit concrete witness return Unsafe.
                    if self.config.base.verbose {
                        safe_eprintln!(
                            "DAR: Both strengthening stages failed at depth {}",
                            forward.len()
                        );
                    }
                    return DarResult::Unknown;
                }
            }

            // Check for fixpoint
            if let Some(inv) = self.check_fixpoint(forward) {
                return self.build_safe_result(ts, &inv);
            }
            if let Some(inv) = self.check_fixpoint_backward(backward) {
                return self.build_safe_result(ts, &inv);
            }
        }

        DarResult::Unknown
    }

    /// Local strengthening: iterate backward from j=0, checking if F[i] ∧ T ∧ B[j]' is UNSAT.
    /// On first UNSAT pair, propagate interpolants through both sequences.
    /// Returns true if strengthening succeeded.
    fn local_strengthen(
        &self,
        ts: &TransitionSystem,
        forward: &mut Vec<ChcExpr>,
        backward: &mut Vec<ChcExpr>,
        boundary_vars_t1: &FxHashSet<String>,
        start: Instant,
    ) -> bool {
        let n = forward.len() - 1;

        for j in 0..=n {
            let i = n - j;
            if search_budget_exhausted(&self.config.base, start, self.config.total_timeout) {
                return false;
            }

            let a = ChcExpr::and(forward[i].clone(), ts.transition_at(0));
            let b = ts.send_through_time(&backward[j], 1);
            let check = ChcExpr::and(a.clone(), b.clone());

            let result = self.check_sat(&check);
            if result.is_unsat() {
                // Found separable pair at (i, j). Propagate.
                return self.iterative_local_strengthen(
                    ts,
                    forward,
                    backward,
                    i,
                    boundary_vars_t1,
                    start,
                );
            } else if result.is_unknown() {
                return false;
            }
        }
        false
    }

    /// Propagate interpolants through both sequences starting from the gap at forward_index.
    fn iterative_local_strengthen(
        &self,
        ts: &TransitionSystem,
        forward: &mut Vec<ChcExpr>,
        backward: &mut Vec<ChcExpr>,
        forward_index: usize,
        boundary_vars_t1: &FxHashSet<String>,
        start: Instant,
    ) -> bool {
        let n = forward.len() - 1;

        // Forward propagation: strengthen F[idx+1] for idx in forward_index..n
        for idx in forward_index..=n {
            if search_budget_exhausted(&self.config.base, start, self.config.total_timeout) {
                return false;
            }

            let j = n - idx; // backward index
            if j >= backward.len() {
                continue;
            }

            if let Some(itp) =
                self.interpolate_forward(ts, forward, backward, idx, boundary_vars_t1)
            {
                let itp_t0 = ts.shift_versioned_state_vars(&itp, -1);
                if idx + 1 < forward.len() {
                    // Strengthen existing: F[idx+1] = F[idx+1] ∧ itp
                    forward[idx + 1] = ChcExpr::and(forward[idx + 1].clone(), itp_t0);
                } else {
                    // Extend sequence
                    forward.push(itp_t0);
                }
            } else {
                return false;
            }
        }

        // Backward propagation: strengthen B[idx+1] for backward_index..n
        let backward_index = n - forward_index;
        for idx in backward_index..=n {
            if search_budget_exhausted(&self.config.base, start, self.config.total_timeout) {
                return false;
            }

            let fi = n - idx; // forward index
            if fi >= forward.len() {
                continue;
            }

            if let Some(itp) = self.interpolate_backward(ts, forward, backward, fi, idx) {
                if idx + 1 < backward.len() {
                    backward[idx + 1] = ChcExpr::and(backward[idx + 1].clone(), itp);
                } else {
                    backward.push(itp);
                }
            } else {
                // Backward interpolation failure is non-fatal; skip
                if idx + 1 >= backward.len() {
                    backward.push(backward[idx].clone());
                }
            }
        }

        true
    }

    /// Interpolate forward: given F[i] ∧ T ∧ B[n-i]' is UNSAT,
    /// partition {F[i], T} from {B[n-i]'} and return interpolant in next-state vars.
    fn interpolate_forward(
        &self,
        ts: &TransitionSystem,
        forward: &[ChcExpr],
        backward: &[ChcExpr],
        forward_idx: usize,
        boundary_vars_t1: &FxHashSet<String>,
    ) -> Option<ChcExpr> {
        let n = forward.len() - 1;
        let backward_idx = n - forward_idx;
        if backward_idx >= backward.len() {
            return None;
        }

        let a = ChcExpr::and(forward[forward_idx].clone(), ts.transition_at(0));
        let b = ts.send_through_time(&backward[backward_idx], 1);

        let mut a_constraints = Vec::new();
        collect_conjuncts_for_interpolation(&a, &mut a_constraints);
        let mut b_constraints = Vec::new();
        collect_conjuncts_for_interpolation(&b, &mut b_constraints);

        match interpolating_sat_constraints(&a_constraints, &b_constraints, boundary_vars_t1) {
            InterpolatingSatResult::Unsat(itp) => {
                // Validate Craig conditions
                let a_flat = ChcExpr::and_all(a_constraints.iter().cloned());
                let b_flat = ChcExpr::and_all(b_constraints.iter().cloned());
                if is_valid_interpolant_with_check_sat(
                    &a_flat,
                    &b_flat,
                    &itp,
                    boundary_vars_t1,
                    |q| self.check_sat(q),
                ) {
                    Some(itp)
                } else {
                    None
                }
            }
            InterpolatingSatResult::Unknown => None,
        }
    }

    /// Interpolate backward: given F[i] ∧ T ∧ B[j]' is UNSAT,
    /// partition {F[i]} from {T, B[j]'} and return interpolant in current-state vars.
    fn interpolate_backward(
        &self,
        ts: &TransitionSystem,
        forward: &[ChcExpr],
        backward: &[ChcExpr],
        forward_idx: usize,
        backward_idx: usize,
    ) -> Option<ChcExpr> {
        if forward_idx >= forward.len() || backward_idx >= backward.len() {
            return None;
        }

        let a_part = ChcExpr::and(
            ts.transition_at(0),
            ts.send_through_time(&backward[backward_idx], 1),
        );
        let b_part = forward[forward_idx].clone();

        // Partition: A = {T, B[j]'}, B = {F[i]} at the current-state boundary
        let boundary_vars_t0 = ts.state_var_names();
        let mut a_constraints = Vec::new();
        collect_conjuncts_for_interpolation(&a_part, &mut a_constraints);
        let b_constraints = vec![b_part];

        match interpolating_sat_constraints(&a_constraints, &b_constraints, &boundary_vars_t0) {
            InterpolatingSatResult::Unsat(itp) => Some(itp),
            InterpolatingSatResult::Unknown => None,
        }
    }

    /// Global strengthening: try multi-step unrolling when local fails.
    /// Reference: Golem DAR.cc:141-181
    fn global_strengthen(
        &self,
        ts: &TransitionSystem,
        forward: &mut Vec<ChcExpr>,
        backward: &mut Vec<ChcExpr>,
        boundary_vars_t1: &FxHashSet<String>,
        start: Instant,
    ) -> bool {
        let n = forward.len() - 1;

        // Build unrolled transitions: Init ∧ T@0 ∧ T@1 ∧ ... ∧ T@(k-1) ∧ B[n-k]@k
        // For increasing k, check if the unrolled formula is UNSAT
        for k in 2..=n + 1 {
            if search_budget_exhausted(&self.config.base, start, self.config.total_timeout) {
                return false;
            }

            // Build: Init ∧ T@0 ∧ T@1 ∧ ... ∧ T@(k-1)
            let mut prefix_parts = vec![ts.init.clone()];
            for step in 0..k {
                prefix_parts.push(ts.transition_at(step));
            }
            let prefix = ChcExpr::and_all(prefix_parts);

            let backward_idx = n.saturating_sub(k);
            if backward_idx >= backward.len() {
                continue;
            }

            let suffix = ts.send_through_time(&backward[backward_idx], k);
            let check = ChcExpr::and(prefix.clone(), suffix.clone());

            let result = self.check_sat(&check);
            if result.is_unsat() {
                // Multi-step UNSAT found at depth k. Extract path interpolants.
                let boundary_vars_tk = ts.state_var_names_at(k);

                let mut a_constraints = Vec::new();
                collect_conjuncts_for_interpolation(&prefix, &mut a_constraints);
                let mut b_constraints = Vec::new();
                collect_conjuncts_for_interpolation(&suffix, &mut b_constraints);

                if let InterpolatingSatResult::Unsat(itp) =
                    interpolating_sat_constraints(&a_constraints, &b_constraints, &boundary_vars_tk)
                {
                    // Shift interpolant back to time-0
                    let itp_t0 = ts.shift_versioned_state_vars(&itp, -(k as i32));
                    // Strengthen forward[k] (or extend)
                    while forward.len() <= k {
                        forward.push(ChcExpr::Bool(true));
                    }
                    forward[k] = ChcExpr::and(forward[k].clone(), itp_t0);

                    // Now do iterative local strengthening from k-1
                    return self.iterative_local_strengthen(
                        ts,
                        forward,
                        backward,
                        k.saturating_sub(1),
                        boundary_vars_t1,
                        start,
                    );
                }
                return false;
            } else if result.is_unknown() {
                return false;
            }
        }

        false
    }

    /// Check fixpoint on forward sequence: F[i] ⊆ F[0] ∨ ... ∨ F[i-1]
    fn check_fixpoint(&self, sequence: &[ChcExpr]) -> Option<ChcExpr> {
        for i in 1..sequence.len() {
            let disjunction = ChcExpr::or_all(sequence[..i].to_vec());
            // Check: F[i] ∧ ¬(F[0] ∨ ... ∨ F[i-1]) is UNSAT
            // i.e., F[i] ⊆ F[0] ∨ ... ∨ F[i-1]
            let check = ChcExpr::and(sequence[i].clone(), ChcExpr::not(disjunction.clone()));
            if self.check_sat(&check).is_unsat() {
                if self.config.base.verbose {
                    safe_eprintln!("DAR: Forward fixpoint at index {}", i);
                }
                return Some(disjunction);
            }
        }
        None
    }

    /// Check fixpoint on backward sequence: B[i] ⊆ B[0] ∨ ... ∨ B[i-1]
    /// Returns ¬(B[0] ∨ ... ∨ B[i-1]) as the invariant.
    fn check_fixpoint_backward(&self, sequence: &[ChcExpr]) -> Option<ChcExpr> {
        for i in 1..sequence.len() {
            let disjunction = ChcExpr::or_all(sequence[..i].to_vec());
            let check = ChcExpr::and(sequence[i].clone(), ChcExpr::not(disjunction.clone()));
            if self.check_sat(&check).is_unsat() {
                if self.config.base.verbose {
                    safe_eprintln!("DAR: Backward fixpoint at index {}", i);
                }
                return Some(ChcExpr::not(disjunction));
            }
        }
        None
    }

    fn build_safe_result(&self, ts: &TransitionSystem, inv: &ChcExpr) -> DarResult {
        // Validate the invariant is inductive
        if validate_inductive_invariant(ts, inv, |q| self.check_sat(q)).is_some() {
            if self.config.base.verbose {
                safe_eprintln!("DAR: Invariant validation failed, returning Unknown");
            }
            return DarResult::Unknown;
        }

        build_single_pred_model(&self.problem, inv.clone())
            .map_or(DarResult::Unknown, DarResult::Safe)
    }

    fn check_sat(&self, constraint: &ChcExpr) -> SmtResult {
        check_sat_with_timeout(constraint, self.config.query_timeout)
    }
}

#[allow(clippy::unwrap_used, clippy::panic)]
#[cfg(test)]
mod tests;
