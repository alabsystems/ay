// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! MAX-SAT solver front-end.
//!
//! Collects hard and soft clauses and solves weighted partial MaxSAT with
//! the core-guided OLL engine in [`crate::oll`]: incremental assumption-based
//! SAT solving with unsat cores, lazily extended totalizers, weight-aware
//! core splitting, stratification, and hardening.

use std::time::Instant;

use ay_sat::{Literal, SignedClause};

use crate::oll::{ClauseStore, OllEngine, OllOutcome};

/// Weight type for soft clauses
pub(crate) type Weight = u64;

/// Result of MAX-SAT solving
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MaxSatResult {
    /// Found optimal solution
    Optimal {
        /// The satisfying assignment (variable -> value)
        model: Vec<bool>,
        /// Total cost (sum of weights of unsatisfied soft clauses)
        cost: u64,
    },
    /// Hard clauses are unsatisfiable
    Unsatisfiable,
    /// Unknown result (timeout, resource limit)
    Unknown,
}

/// Statistics for MAX-SAT solving
#[derive(Debug, Clone, Default)]
pub struct MaxSatStats {
    /// Number of SAT solver calls
    pub sat_calls: u64,
    /// Number of cardinality constraints (totalizers) added
    pub cardinality_constraints: u64,
    /// Number of UNSAT cores processed
    pub cores_found: u64,
    /// #core-mine: incremented when the mined-core pass detected that `lb`
    /// exceeded an already-REACHED cost and abandoned itself. Non-zero means
    /// the accounting is inconsistent and must be investigated — it is the
    /// fail-safe that turns a would-be wrong answer into a lost solve.
    pub core_mine_abandoned: u64,
    /// Number of soft clauses hardened via bound reasoning
    pub hardened: u64,
    /// Number of successful core-exhaustion probes (forced extra violations)
    pub exhaust_steps: u64,
    /// Number of intrinsic at-most-one groups folded during preprocessing
    pub am1_groups: u64,
    /// Number of solution-improving (LSU) descent steps
    pub lsu_steps: u64,
    /// Number of abstraction sets formed (abstract cores)
    pub abstraction_sets: u64,
    /// Number of LP-boost dual-packing rounds run (#lp-boost)
    pub lp_boost_runs: u64,
    /// Number of LP-boost rounds that raised the certified lower bound
    pub lp_boost_improvements: u64,
    /// Number of stratification levels scheduled (#climit-discipline);
    /// exactly 1 on uniform-weight (in particular unweighted) instances.
    pub strat_levels: u64,
    /// Number of WCE flush points that materialized deferred core
    /// relaxations (#wce)
    pub wce_flushes: u64,
    /// Total deferred cores materialized across all WCE flushes (#wce)
    pub wce_relaxed_cores: u64,
    /// Largest number of cores materialized by a single WCE flush (#wce)
    pub wce_max_flush_batch: u64,
    /// Cores strictly shrunk by deletion-based minimization (#minimize)
    pub cores_minimized: u64,
    /// Total core members removed by deletion-based minimization (#minimize)
    pub minimize_removed_literals: u64,
    /// UP-probe AM1 passes run at stratification level changes
    /// (#maxsat-am1-probe)
    pub am1_probe_passes: u64,
    /// Selectors hardened by an AM1 probe pass because assuming them
    /// propagated to a conflict (failed literals; #maxsat-am1-probe)
    pub am1_probe_failed: u64,
    /// Semantic AM1 cliques relaxed by an AM1 probe pass — conflicts found
    /// only through UP-implication chains, not direct binary edges
    /// (#maxsat-am1-probe)
    pub am1_probe_groups: u64,
    /// Totalizer REVERSE-direction ("equivalence") clauses emitted so a
    /// proven-true output can propagate downward (#tot-eqs)
    pub tot_eq_clauses: u64,
    /// Proven-true totalizer outputs handed to the reverse-direction pass
    /// (#tot-eqs): one per relaxed core plus one per hardened sum bound
    pub tot_eq_forced: u64,
    /// Extracted core disjunctions pinned permanently into the hard formula
    /// (#core-clause)
    pub core_clauses_added: u64,
    /// #descent-residual: incremented when the residual descent cap refused to
    /// arm because `lb` exceeded an already-REACHED cost. Non-zero means the
    /// residual accounting is inconsistent and must be investigated — it is the
    /// fail-safe (sibling of `core_mine_abandoned`) that turns a would-be wrong
    /// answer into a slower, exact-encoding descent.
    pub descent_residual_abandoned: u64,
}

/// MAX-SAT Solver
///
/// Supports weighted partial MAX-SAT:
/// - Hard clauses must be satisfied
/// - Soft clauses have weights; goal is to minimize total weight of
///   unsatisfied soft clauses
pub struct MaxSatSolver {
    /// Hard clauses (converted to Literal at the API boundary)
    hard_clauses: ClauseStore,
    /// Soft clause literals, parallel to `soft_weights`
    soft_clauses: ClauseStore,
    /// Soft clause weights
    soft_weights: Vec<Weight>,
    /// One past the maximum raw variable id seen in any clause
    next_var: u32,
    /// Statistics (populated by solve)
    stats: MaxSatStats,
    /// #core-mine evidence from the last solve, for certificate emission only.
    paid_mined_cores: Vec<crate::oll::PaidMinedCore>,
    /// SAT-call core evidence from the last solve, for certificate emission
    /// only. Same write-only rule as `paid_mined_cores`.
    paid_sat_cores: Vec<crate::oll::PaidSatCore>,
    /// Best (cost, model) seen by the last interrupted solve, if any
    best: Option<(Weight, Vec<bool>)>,
    /// Wall-clock deadline for the whole solve, when the caller knows one.
    deadline: Option<Instant>,
}

impl MaxSatSolver {
    /// Create a new MAX-SAT solver
    pub fn new() -> Self {
        Self {
            hard_clauses: ClauseStore::new(),
            soft_clauses: ClauseStore::new(),
            soft_weights: Vec::new(),
            next_var: 1,
            stats: MaxSatStats::default(),
            paid_mined_cores: Vec::new(),
            paid_sat_cores: Vec::new(),
            best: None,
            deadline: None,
        }
    }

    /// Tell the engine when the solve must end.
    ///
    /// Without this the engine is BUDGET-BLIND: `should_stop` reports whether
    /// to stop *now* but never how much budget remains, so every internal
    /// policy — descent slice lengths, stall bars, probe budgets — is a fixed
    /// absolute constant that necessarily suits exactly one timeout. Measured
    /// consequence: AY's solved count barely moves between 60s and 3600s while
    /// the MSE24 field's leaders climb, because they switch strategy on a
    /// schedule (CASHWMaxSAT-S6/S9 step at exactly 600s/900s) and AY has no
    /// schedule to switch on.
    ///
    /// Optional and non-breaking: `None` preserves the previous behaviour
    /// exactly.
    pub fn set_deadline(&mut self, deadline: Option<Instant>) {
        self.deadline = deadline;
    }

    /// Track the variable ids used by a clause.
    fn track_vars(&mut self, clause: &SignedClause) {
        for &lit in clause {
            let var = lit.unsigned_abs();
            if var >= self.next_var {
                // saturating: a var id at u32::MAX leaves no room for a successor;
                // capping is the only sound outcome and proves overflow-free.
                self.next_var = var.saturating_add(1);
            }
        }
    }

    /// Add a hard clause (must be satisfied)
    pub fn add_hard_clause(&mut self, clause: SignedClause) {
        self.track_vars(&clause);
        self.hard_clauses
            .push_from_iter(clause.iter().map(|&l| Literal::from(l)));
    }

    /// Add a soft clause with weight
    pub fn add_soft_clause(&mut self, clause: SignedClause, weight: Weight) {
        self.track_vars(&clause);
        self.soft_clauses
            .push_from_iter(clause.iter().map(|&l| Literal::from(l)));
        self.soft_weights.push(weight);
    }

    /// Mined cores the last solve charged, as proof evidence.
    ///
    /// Write-only (see `ay::maxsat_proof`): this exists so a certificate can
    /// name the lower bound's derivation. No caller may turn it into a verdict.
    pub fn paid_mined_cores(&self) -> &[crate::oll::PaidMinedCore] {
        &self.paid_mined_cores
    }

    /// Cores returned by SAT calls that the last solve charged, as proof
    /// evidence.
    ///
    /// Write-only (see `ay::maxsat_proof`). These are REFUTATIONS, not input
    /// rows: the emitter must justify each one for itself before it may state
    /// it, and drops the ones it cannot. No caller may turn this into a
    /// verdict.
    pub fn paid_sat_cores(&self) -> &[crate::oll::PaidSatCore] {
        &self.paid_sat_cores
    }

    /// Get solver statistics
    pub fn stats(&self) -> &MaxSatStats {
        &self.stats
    }

    /// Best (cost, model) found by the last [`Self::solve_interruptible`]
    /// call that returned [`MaxSatResult::Unknown`], if any. Enables anytime
    /// behavior: an interrupted solve can still report its incumbent.
    pub fn best_solution(&self) -> Option<(u64, &[bool])> {
        self.best.as_ref().map(|(c, m)| (*c, m.as_slice()))
    }

    /// Solve the MAX-SAT instance to optimality.
    ///
    /// Solving consumes the added clauses: a subsequent `solve` on the same
    /// instance sees an empty formula. Add clauses again to re-solve.
    pub fn solve(&mut self) -> MaxSatResult {
        self.solve_interruptible(&|| false, &mut |_| {})
    }

    /// Solve with an interrupt callback and an upper-bound callback.
    ///
    /// `should_stop` is polled during SAT search; returning `true` aborts
    /// the solve with [`MaxSatResult::Unknown`] (the incumbent, if any, is
    /// available via [`Self::best_solution`]). `on_upper_bound` fires each
    /// time a better solution is found, with its cost.
    pub fn solve_interruptible(
        &mut self,
        should_stop: &dyn Fn() -> bool,
        on_upper_bound: &mut dyn FnMut(u64),
    ) -> MaxSatResult {
        // Handle empty instance
        if self.hard_clauses.is_empty() && self.soft_clauses.is_empty() {
            return MaxSatResult::Optimal {
                model: vec![],
                cost: 0,
            };
        }

        let hard = std::mem::take(&mut self.hard_clauses);
        let soft = std::mem::take(&mut self.soft_clauses);
        let weights = std::mem::take(&mut self.soft_weights);
        let mut engine = OllEngine::new(self.next_var, hard, soft, weights);
        engine.set_deadline(self.deadline);
        let outcome = engine.solve(should_stop, on_upper_bound);
        self.stats = engine.stats().clone();
        self.paid_mined_cores = engine.take_paid_mined_cores();
        self.paid_sat_cores = engine.take_paid_sat_cores();
        self.best = None;

        match outcome {
            OllOutcome::Optimal { model, cost } => MaxSatResult::Optimal { model, cost },
            OllOutcome::Unsatisfiable => MaxSatResult::Unsatisfiable,
            OllOutcome::Unknown { best } => {
                self.best = best;
                MaxSatResult::Unknown
            }
        }
    }
}

impl Default for MaxSatSolver {
    fn default() -> Self {
        Self::new()
    }
}

#[allow(clippy::panic)]
#[cfg(test)]
#[path = "solver_tests.rs"]
mod tests;
