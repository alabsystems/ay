// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Main CEGAR engine implementation
//!
//! Reference: `reference/eldarica/src/main/scala/lazabs/horn/bottomup/CEGAR.scala`
//!
//! Implements predicate abstraction with CEGAR refinement for CHC solving.
//! The algorithm:
//! 1. Seeds the abstract reachability graph (ARG) with fact clauses
//! 2. Expands states by applying clauses and computing abstract successors
//! 3. When a path to False is found, checks if the counterexample is genuine
//! 4. If spurious, extracts interpolants to discover new predicates and refines
//! 5. If queue empties without reaching False, extracts inductive invariants

mod cegar_cache;
mod types;
use cegar_cache::{CachedFeasibility, CegarCache};
use types::*;
pub(crate) use types::{CegarConfig, CegarCounterexample, CegarResult};

use super::abstract_state::{AbstractEdge, AbstractState};
use super::predicate_store::PredicateStore;
use super::state_queue::StateQueue;
use crate::farkas::compute_interpolant as farkas_compute_interpolant;
use crate::interpolation::{interpolating_sat_constraints, InterpolatingSatResult};
use crate::{
    compute_interpolant_from_lia_farkas, compute_interpolant_from_smt_farkas_history,
    CexVerificationResult, ChcExpr, ChcOp, ChcProblem, ChcSort, ChcVar, ClauseHead, Counterexample,
    CounterexampleStep, InterpolatingResult, InterpolatingSmtContext, InvariantModel, PdrConfig,
    PdrSolver, PredicateId, PredicateInterpretation, QualifierSet, SmtContext, SmtResult,
};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};

/// Main CEGAR engine
///
/// Implements predicate abstraction with CEGAR refinement.
/// Maintains an abstract reachability graph (ARG) with:
/// - Abstract states: (relation, predicates) pairs
/// - Abstract edges: clause applications between states
/// - Subsumption tracking for pruning
/// - Priority queue for expansion scheduling
pub(crate) struct CegarEngine {
    problem: ChcProblem,
    config: CegarConfig,
    qualifiers: QualifierSet,
    predicates: PredicateStore,
    active_states: FxHashMap<PredicateId, FxHashSet<AbstractState>>,
    max_states: FxHashMap<PredicateId, FxHashSet<AbstractState>>,
    forward_subsumed: FxHashMap<AbstractState, AbstractState>,
    backward_subsumed: FxHashMap<AbstractState, AbstractState>,
    edges: Vec<AbstractEdge>,
    queue: StateQueue,
    smt: SmtContext,
    iteration: usize,
    /// Last counterexample trace (edge indices), saved for template fallback.
    last_cex_trace: Option<Vec<usize>>,
    /// Source states and clause index of the last counterexample expansion,
    /// saved for Eldarica-style postponed re-enqueuing on refinement failure.
    last_cex_expansion: Option<(Vec<AbstractState>, usize)>,
    /// Number of consecutive refinement failures where the counterexample was
    /// postponed rather than producing new predicates. When this exceeds the
    /// queue size, refinement has exhausted all productive paths.
    /// Reference: Eldarica CEGAR.scala:136 `postponedExpansionCount`
    postponed_count: usize,
    /// Number of times template-only refinement has reset `postponed_count`.
    /// After `MIN_TEMPLATE_RESETS`, further resets require predicate store growth (#3085, #3121).
    template_resets: usize,
    /// Predicate count at last template reset. Used to detect genuine progress
    /// beyond the minimum reset allowance.
    predicates_at_last_reset: usize,
    /// State preservation cache for feasibility and implication results (#3762).
    /// Survives `restart_arg()` to avoid redundant SMT queries across CEGAR
    /// refinement iterations.
    cache: CegarCache,
    /// Number of multipred bounded-BMC replay validations attempted (inc-9).
    /// Capped so the refinement loop cannot burn its budget re-replaying.
    multipred_replay_attempts: usize,
    /// Deepest trace depth whose multipred replay failed (inc-9). The replay
    /// only uses the depth bound, so shallower traces are rejected without
    /// re-running it.
    multipred_replay_failed_depth: Option<usize>,
}

impl Drop for CegarEngine {
    fn drop(&mut self) {
        std::mem::take(&mut self.problem).iterative_drop();
    }
}

impl CegarEngine {
    pub(crate) fn new(problem: ChcProblem, config: CegarConfig) -> Self {
        let qualifiers = QualifierSet::from_problem(&problem);
        let mut active_states = FxHashMap::default();
        let mut max_states = FxHashMap::default();

        for pred in problem.predicates() {
            active_states.insert(pred.id, FxHashSet::default());
            max_states.insert(pred.id, FxHashSet::default());
        }

        let smt = problem.make_smt_context();
        Self {
            problem,
            config,
            qualifiers,
            predicates: PredicateStore::new(),
            active_states,
            max_states,
            forward_subsumed: FxHashMap::default(),
            backward_subsumed: FxHashMap::default(),
            edges: Vec::new(),
            queue: StateQueue::new(),
            smt,
            iteration: 0,
            last_cex_trace: None,
            last_cex_expansion: None,
            postponed_count: 0,
            template_resets: 0,
            predicates_at_last_reset: 0,
            cache: CegarCache::new(),
            multipred_replay_attempts: 0,
            multipred_replay_failed_depth: None,
        }
    }

    /// Run the CEGAR algorithm
    ///
    /// Uses Eldarica-style postponed expansion for stall recovery:
    /// when refinement fails to produce new predicates, the counterexample
    /// expansion is re-enqueued with a priority penalty instead of being
    /// discarded. The solver gives up when postponed failures dominate the
    /// remaining queue.
    ///
    /// Reference: `reference/eldarica/src/main/scala/lazabs/horn/bottomup/CEGAR.scala:136-211`
    pub(crate) fn solve(&mut self) -> CegarResult {
        self.seed_facts();

        loop {
            // Stall detection: give up when postponed failures dominate and enough
            // exploration has happened. ARG restarts happen at multiples of 5, so
            // threshold of 20 allows 4 restarts before giving up.
            if self.postponed_count > self.queue.len() && self.postponed_count >= 20 {
                if self.config.base.verbose {
                    let stats = self.cache.stats();
                    safe_eprintln!(
                        "CEGAR: refinement exhausted — {} postponed failures > {} remaining queue entries \
                         (cache: feas {}/{} hits/misses, impl {}/{} hits/misses)",
                        self.postponed_count,
                        self.queue.len(),
                        stats.feasibility_hits,
                        stats.feasibility_misses,
                        stats.implication_hits,
                        stats.implication_misses,
                    );
                }
                return CegarResult::Unknown;
            }

            match self.expand_until_counterexample() {
                ExpandResult::QueueEmpty => {
                    self.log_cache_stats("queue empty");
                    return self.extract_invariants();
                }
                ExpandResult::Cancelled | ExpandResult::IterationLimit => {
                    self.log_cache_stats("cancelled/limit");
                    return CegarResult::Unknown;
                }
                ExpandResult::Counterexample(cex_edge_idx) => {
                    self.iteration += 1;
                    if self.config.base.verbose {
                        safe_eprintln!(
                            "CEGAR: refinement #{} (edges={}, preds={}, postponed={})",
                            self.iteration,
                            self.edges.len(),
                            self.predicates.len(),
                            self.postponed_count
                        );
                    }

                    match self.analyze_counterexample(cex_edge_idx) {
                        CexAnalysis::Genuine(trace) => {
                            if self.config.base.verbose {
                                safe_eprintln!(
                                    "CEGAR: counterexample is GENUINE ({} steps)",
                                    trace.len()
                                );
                            }
                            // Internal validation: verify against original problem
                            // constraints before returning Unsafe. The abstract
                            // feasibility check can produce false genuines when
                            // the abstraction loses precision (#3156).
                            if self.validate_counterexample(&trace) {
                                return CegarResult::Unsafe(CegarCounterexample { trace });
                            }
                            if self.config.base.verbose {
                                safe_eprintln!(
                                    "CEGAR: counterexample failed internal validation, treating as spurious"
                                );
                            }
                            // Treat as analysis failure: try templates, then postpone
                            let saved_trace = self.last_cex_trace.clone();
                            if let Some(ref t) = saved_trace {
                                let templates = self.generate_template_predicates(t);
                                if !templates.is_empty()
                                    && self.refine(templates)
                                    && self.record_template_refinement_success()
                                {
                                    continue;
                                }
                            }
                            self.postpone_counterexample();
                            if self.postponed_count.is_multiple_of(5) {
                                self.restart_arg();
                            }
                            continue;
                        }
                        CexAnalysis::Spurious(new_predicates) => {
                            if !new_predicates.is_empty() && self.refine(new_predicates) {
                                // Genuine interpolation progress — reset counters
                                self.postponed_count = 0;
                                self.template_resets = 0;
                                continue;
                            }
                            // Interpolation failed or stalled — try template predicates
                            let trace = self.last_cex_trace.clone();
                            if let Some(ref trace) = trace {
                                let templates = self.generate_template_predicates(trace);
                                if !templates.is_empty() && self.refine(templates) {
                                    if self.record_template_refinement_success() {
                                        continue;
                                    }
                                    if self.config.base.verbose {
                                        safe_eprintln!(
                                            "CEGAR: template retry cap reached ({}/{})",
                                            self.template_resets,
                                            MIN_TEMPLATE_RESETS
                                        );
                                    }
                                }
                            }
                            // Stall recovery: postpone first, then restart ARG
                            self.postpone_counterexample();
                            // After every 5 consecutive postponements without progress,
                            // restart the ARG to explore completely different traces.
                            // This combines Eldarica's postpone approach with AY's
                            // ARG restart for hard cases.
                            if self.postponed_count.is_multiple_of(5) {
                                if self.config.base.verbose {
                                    safe_eprintln!(
                                        "CEGAR: ARG restart after {} postponements",
                                        self.postponed_count
                                    );
                                }
                                self.restart_arg();
                            }
                            continue;
                        }
                        CexAnalysis::AnalysisFailed => {
                            // Analysis failed — try templates, then postpone
                            let trace = self.last_cex_trace.clone();
                            if let Some(ref trace) = trace {
                                let templates = self.generate_template_predicates(trace);
                                if !templates.is_empty() && self.refine(templates) {
                                    if self.record_template_refinement_success() {
                                        continue;
                                    }
                                    if self.config.base.verbose {
                                        safe_eprintln!(
                                            "CEGAR: template retry cap reached after analysis failure ({}/{})",
                                            self.template_resets,
                                            MIN_TEMPLATE_RESETS
                                        );
                                    }
                                }
                            }
                            self.postpone_counterexample();
                            if self.postponed_count.is_multiple_of(5) {
                                if self.config.base.verbose {
                                    safe_eprintln!(
                                        "CEGAR: ARG restart after {} postponements (analysis failure)",
                                        self.postponed_count
                                    );
                                }
                                self.restart_arg();
                            }
                            continue;
                        }
                    }
                }
            }
        }
    }

    fn expand_until_counterexample(&mut self) -> ExpandResult {
        while !self.queue.is_empty() {
            // Check cancellation, memory budget (#2769), or conversion budget (#2472)
            if self.config.base.is_cancelled() || self.smt.is_budget_exhausted() {
                return ExpandResult::Cancelled;
            }

            if self.iteration >= self.config.max_iterations {
                return ExpandResult::IterationLimit;
            }

            let expansion = match self.queue.dequeue() {
                Some(e) => e,
                None => break,
            };

            if expansion
                .states
                .iter()
                .any(|s| self.backward_subsumed.contains_key(s))
            {
                continue;
            }

            let full_assumptions =
                self.build_expansion_constraint(expansion.clause_index, &expansion.states);

            if let Some(edge) =
                self.try_generate_edge(&expansion.states, expansion.clause_index, &full_assumptions)
            {
                let is_query = self.problem.clauses()[expansion.clause_index]
                    .head
                    .is_query();
                if is_query {
                    // Save expansion info for potential postponed re-enqueuing
                    self.last_cex_expansion =
                        Some((expansion.states.clone(), expansion.clause_index));
                    let edge_idx = self.edges.len();
                    self.edges.push(edge);
                    return ExpandResult::Counterexample(edge_idx);
                }

                self.add_edge(edge);
            }
        }

        ExpandResult::QueueEmpty
    }

    /// Record successful template-only refinement and apply cap policy.
    /// Returns true when the success is within cap and resets postponed counter.
    ///
    /// After `MIN_TEMPLATE_RESETS`, further resets are allowed only when the
    /// predicate store has grown since the last reset. This prevents stall
    /// cycles from novel-but-unhelpful templates (#3085) while allowing
    /// extended refinement when templates produce genuinely new predicates
    /// (needed for s_multipl benchmarks, #3121).
    fn record_template_refinement_success(&mut self) -> bool {
        self.template_resets += 1;
        let current_pred_count = self.predicates.len();

        if self.template_resets <= MIN_TEMPLATE_RESETS {
            self.postponed_count = 0;
            self.predicates_at_last_reset = current_pred_count;
            return true;
        }

        // Beyond the minimum, allow reset only if predicate count grew
        // (genuine novel predicates, not recycled ones).
        if current_pred_count > self.predicates_at_last_reset {
            self.postponed_count = 0;
            self.predicates_at_last_reset = current_pred_count;
            return true;
        }

        false
    }

    /// Postpone a failed counterexample by re-enqueuing its expansion with a
    /// priority penalty. The expansion is pushed to the back of the queue,
    /// allowing other paths to be explored first.
    ///
    /// Reference: Eldarica CEGAR.scala:374-388 (POSTPONED_EXPANSION_PENALTY)
    fn postpone_counterexample(&mut self) {
        self.postponed_count += 1;
        if let Some((states, clause_index)) = self.last_cex_expansion.take() {
            self.queue.enqueue_postponed(states, clause_index, true);
            if self.config.base.verbose {
                safe_eprintln!(
                    "CEGAR: postponed counterexample (total={}, queue={})",
                    self.postponed_count,
                    self.queue.len()
                );
            }
        }
    }

    fn build_expansion_constraint(
        &self,
        clause_index: usize,
        body_states: &[AbstractState],
    ) -> ChcExpr {
        let clause = &self.problem.clauses()[clause_index];
        let mut conjuncts = Vec::new();

        if let Some(ref constraint) = clause.body.constraint {
            conjuncts.push(constraint.clone());
        }

        for (state_idx, state) in body_states.iter().enumerate() {
            if state_idx >= clause.body.predicates.len() {
                break;
            }
            let (_pred_id, ref body_args) = clause.body.predicates[state_idx];
            let canonical_vars = self.canonical_vars(state.relation);

            for &pred_idx in &state.predicates {
                if let Some(pred) = self.predicates.get(pred_idx) {
                    let subst: Vec<_> = canonical_vars
                        .iter()
                        .zip(body_args.iter())
                        .map(|(v, arg)| (v.clone(), arg.clone()))
                        .collect();
                    conjuncts.push(pred.formula.substitute(&subst));
                }
            }
        }

        ChcExpr::and_all(conjuncts)
    }

    fn canonical_vars(&self, relation: PredicateId) -> Vec<ChcVar> {
        self.problem
            .get_predicate(relation)
            .map(|pred| {
                pred.arg_sorts
                    .iter()
                    .enumerate()
                    .map(|(i, sort)| {
                        ChcVar::new(format!("_cegar_P{}_{}", relation.index(), i), sort.clone())
                    })
                    .collect()
            })
            .unwrap_or_default()
    }

    /// Log cache hit/miss statistics when verbose mode is enabled.
    fn log_cache_stats(&self, context: &str) {
        if self.config.base.verbose {
            let stats = self.cache.stats();
            let total_feas = stats.feasibility_hits + stats.feasibility_misses;
            let total_impl = stats.implication_hits + stats.implication_misses;
            let feas_rate = if total_feas > 0 {
                (stats.feasibility_hits as f64 / total_feas as f64) * 100.0
            } else {
                0.0
            };
            let impl_rate = if total_impl > 0 {
                (stats.implication_hits as f64 / total_impl as f64) * 100.0
            } else {
                0.0
            };
            safe_eprintln!(
                "CEGAR cache stats ({context}): feasibility {}/{} ({feas_rate:.0}% hit), \
                 implication {}/{} ({impl_rate:.0}% hit)",
                stats.feasibility_hits,
                total_feas,
                stats.implication_hits,
                total_impl,
            );
        }
    }

    fn seed_facts(&mut self) {
        for (idx, clause) in self.problem.clauses().iter().enumerate() {
            if clause.body.predicates.is_empty() {
                let is_query = clause.head.is_query();
                self.queue.enqueue(vec![], idx, is_query);
            }
        }
    }
}

mod analysis;
mod expansion;
mod interpolation;
mod interpolation_cascade;
mod invariants;
mod refinement;

#[allow(clippy::unwrap_used, clippy::panic)]
#[cfg(test)]
mod tests;
