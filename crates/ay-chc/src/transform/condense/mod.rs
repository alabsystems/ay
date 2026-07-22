// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Unified fixpoint condense superpass for CHC preprocessing.
//!
//! Iterates a round of shrink transforms until the problem size stabilizes,
//! following the *ideas* of Eldarica's `DefaultPreprocessor` fixpoint condense
//! loop, Golem's double-pass transformation pipeline with the
//! `SlightlyBetterNodeEliminator` `|in|*|out| <= |in|+|out|` vertex rule, and
//! Z3/Spacer's eager inlining + slicing defaults (all reimplemented from
//! scratch; no competitor code copied):
//!
//! 1. [`UnreachableClauseEliminator`] — fwd/bwd reachability pruning.
//! 2. [`ConstantPropagator`] — inter-clause constant argument propagation
//!    plus constraint folding.
//! 2.5. [`ArrayStoreForwarder`] — clause-local array store-to-load
//!    forwarding + dead-store elimination (reused; makes threaded memory
//!    arrays dead so step 6 can slice their argument positions).
//! 3. [`LocalVarEliminator`] — equality propagation / constraint
//!    simplification for clause-local variables (reused).
//! 4. [`ClauseInliner`] with the graph-collapse node rule — unique-definition
//!    linear-chain composition (`h_i => h_{i+1}` copy edges) plus the golem
//!    `|in|*|out| <= |in|+|out|` node-elimination policy, capped at
//!    constraint size 10k (reused).
//! 5. [`MultiEdgeMerger`] — parallel-edge disjunction (reused).
//! 6. [`DeadParamEliminator`] — argument cone-of-influence slicing with model
//!    reconstruction on back-translation (reused).
//!
//! Every constituent ships an exact `BackTranslator` (G1): SAT models are
//! reconstructed and re-validated against the ORIGINAL clauses, UNSAT
//! witnesses are remapped/replayed there, and any back-translation failure is
//! treated fail-closed as Unknown by the portfolio firewall
//! (`TransformMemoryReport::is_identity_grade` forces original validation for
//! every non-identity stack).
//!
//! Kill switch: `AY_CHC_DISABLE_CONDENSE=1` disables the pass entirely.

mod constant_prop;
mod reachability;

pub(crate) use constant_prop::ConstantPropagator;
pub(crate) use reachability::UnreachableClauseEliminator;

use crate::{ChcExpr, ChcProblem, ClauseBody, ClauseHead, HornClause, PredicateId};
use ay_core::kani_compat::DetHashSet as FxHashSet;
use std::time::Duration;
// The workspace-wide monotonic clock shim (#wasm port): byte-identical to
// `std::time::Instant` on native targets, host-clock-backed on wasm32 (raw
// `std::time::Instant` panics there and breaks the wasm build).
use ay_core::time::Instant;

use super::{
    ArrayStoreForwarder, BackTranslator, ClauseInliner, CompositeBackTranslator,
    DeadParamEliminator, GroundTableReadConcretizer, IdentityBackTranslator, InvalidityWitness,
    LocalVarEliminator, MultiEdgeMerger, TransformationResult, Transformer,
};

/// Problems larger than this skip the condense loop entirely: the constituent
/// transforms rebuild the clause vector several times per round, so huge
/// systems would pay a large constant factor for little routing benefit.
const MAX_CONDENSE_CLAUSES: usize = 4096;

/// Bound on condense rounds. Rounds must strictly shrink the problem
/// (predicates-in-use or clause count) to continue, so this is a safety cap.
const MAX_CONDENSE_ROUNDS: usize = 8;

/// Default per-superpass wall budget (FIX #2a). `MAX_CONDENSE_CLAUSES` gates
/// clause COUNT, which is the wrong quantity for runtime: a 34-pred/114-clause
/// system whose round-1 inlining composes giant constraints can hang round 2
/// for minutes. The budget is checked before every constituent transform, and
/// on expiry the loop returns the best-so-far result — the transform stack up
/// to any prefix is exact, so bailing anywhere is sound.
/// Env-tunable via `AY_CHC_CONDENSE_BUDGET_SECS` (`0` disables the budget).
const DEFAULT_CONDENSE_BUDGET_SECS: f64 = 10.0;

/// Default mean-constraint-size gate (FIX #2a): once a round has grown the
/// MEAN constraint node count past this threshold, further rounds operate on
/// giant composed constraints (quadratic constituent walks) for little
/// benefit — stop iterating and return the best-so-far result.
/// Env-tunable via `AY_CHC_CONDENSE_MAX_MEAN_NODES` (`0` disables the gate).
const DEFAULT_CONDENSE_MEAN_NODE_GATE: usize = 2048;

/// Per-clause traversal cap used when estimating the mean constraint size:
/// `node_count` stops at the cap, so pathological trees are never walked in
/// full. The cap is a multiple of the gate so the capped mean still detects a
/// whole-problem blowup.
const MEAN_NODE_GATE_CLAUSE_CAP_FACTOR: usize = 4;

fn condense_wall_budget_from_env() -> Option<Duration> {
    match std::env::var("AY_CHC_CONDENSE_BUDGET_SECS") {
        Ok(v) => match v.trim().parse::<f64>() {
            Ok(secs) if secs > 0.0 && secs.is_finite() => Some(Duration::from_secs_f64(secs)),
            Ok(_) => None, // 0 (or negative) disables the wall budget.
            Err(_) => Some(Duration::from_secs_f64(DEFAULT_CONDENSE_BUDGET_SECS)),
        },
        Err(_) => Some(Duration::from_secs_f64(DEFAULT_CONDENSE_BUDGET_SECS)),
    }
}

fn condense_mean_node_gate_from_env() -> usize {
    std::env::var("AY_CHC_CONDENSE_MAX_MEAN_NODES")
        .ok()
        .and_then(|v| v.trim().parse::<usize>().ok())
        .unwrap_or(DEFAULT_CONDENSE_MEAN_NODE_GATE)
}

/// Kill switch: `AY_CHC_DISABLE_CONDENSE=1` (or any value other than `0`)
/// disables the condense superpass. Default: enabled.
pub(crate) fn condense_enabled() -> bool {
    std::env::var("AY_CHC_DISABLE_CONDENSE")
        .map(|v| v == "0")
        .unwrap_or(true)
}

/// Unified fixpoint condense superpass (see module docs).
pub(crate) struct CondenseSuperpass {
    verbose: bool,
    /// Mirror `portfolio_clause_inliner`: on pure-Int problems the inliner
    /// must not eat query-body predicates (the invalidity back-translator
    /// cannot reconstruct the extra derivation node, so Unsafe wins would
    /// degrade to fail-closed Unknowns).
    preserve_query_body_predicates: bool,
    /// FIX #2a: per-superpass wall budget. `None` disables the budget.
    wall_budget: Option<Duration>,
    /// FIX #2a: mean-constraint-node-count gate. `0` disables the gate.
    mean_node_gate: usize,
}

impl CondenseSuperpass {
    pub(crate) fn new() -> Self {
        Self {
            verbose: false,
            preserve_query_body_predicates: false,
            wall_budget: condense_wall_budget_from_env(),
            mean_node_gate: condense_mean_node_gate_from_env(),
        }
    }

    pub(crate) fn with_verbose(mut self, verbose: bool) -> Self {
        self.verbose = verbose;
        self
    }

    pub(crate) fn preserve_query_body_predicates(mut self) -> Self {
        self.preserve_query_body_predicates = true;
        self
    }

    /// Override the env-derived wall budget (item 4 Stage 3: the
    /// condense-first direct acyclic lane bounds the superpass to
    /// `min(stage_budget/3, 15s)`). The loop polls the budget between
    /// constituents and returns the best-so-far (exact) prefix on expiry.
    pub(crate) fn with_wall_budget(mut self, budget: Option<Duration>) -> Self {
        self.wall_budget = budget;
        self
    }

    /// Override the env-derived mean-size gate (`0` disables).
    /// (From the CONDENSE-BOX work, ef7757ec; exposed alongside
    /// [`Self::with_wall_budget`] for the condense-first lane and tests.)
    #[allow(dead_code)]
    pub(crate) fn with_mean_node_gate(mut self, gate: usize) -> Self {
        self.mean_node_gate = gate;
        self
    }

    /// Capped mean constraint node count across all clauses. Each clause walk
    /// stops at a small multiple of the gate, so pathological composed
    /// constraints are never traversed in full.
    fn capped_mean_constraint_nodes(problem: &ChcProblem, gate: usize) -> usize {
        let n = problem.clauses().len();
        if n == 0 || gate == 0 {
            return 0;
        }
        let per_clause_cap = gate.saturating_mul(MEAN_NODE_GATE_CLAUSE_CAP_FACTOR);
        let total: usize = problem
            .clauses()
            .iter()
            .map(|clause| {
                clause
                    .body
                    .constraint
                    .as_ref()
                    .map_or(0, |c| c.node_count(per_clause_cap))
            })
            .sum();
        total / n
    }

    /// FIX #2a bail check, run before every constituent transform: budget
    /// expiry or a mean-constraint-size blowup stops the fixpoint. The
    /// transform stack composed so far is exact, so returning the best-so-far
    /// problem is always sound — the loop must never hang.
    fn should_bail(&self, start: Instant, current: &ChcProblem) -> Option<String> {
        if let Some(budget) = self.wall_budget {
            let elapsed = start.elapsed();
            if elapsed >= budget {
                return Some(format!(
                    "wall budget exhausted ({:.1}s >= {:.1}s)",
                    elapsed.as_secs_f64(),
                    budget.as_secs_f64()
                ));
            }
        }
        if self.mean_node_gate > 0 {
            let mean = Self::capped_mean_constraint_nodes(current, self.mean_node_gate);
            if mean > self.mean_node_gate {
                return Some(format!(
                    "mean constraint size {} nodes > gate {}",
                    mean, self.mean_node_gate
                ));
            }
        }
        None
    }

    /// Size measure driving the fixpoint: predicates still referenced by
    /// clauses, plus the clause count.
    fn problem_size(problem: &ChcProblem) -> (usize, usize) {
        let mut used: FxHashSet<PredicateId> = FxHashSet::default();
        for clause in problem.clauses() {
            for (pid, _) in &clause.body.predicates {
                used.insert(*pid);
            }
            if let Some(pid) = clause.head.predicate_id() {
                used.insert(pid);
            }
        }
        (used.len(), problem.clauses().len())
    }

    fn round_inliner(&self) -> ClauseInliner {
        let inliner = ClauseInliner::new()
            .with_verbose(self.verbose)
            .with_graph_collapse_node_rule();
        if self.preserve_query_body_predicates {
            inliner.preserve_query_body_predicates()
        } else {
            inliner
        }
    }
}

impl Transformer for CondenseSuperpass {
    fn transform(self: Box<Self>, problem: ChcProblem) -> TransformationResult {
        if problem.clauses().is_empty()
            || problem.clauses().len() > MAX_CONDENSE_CLAUSES
            || problem.predicates().len() < 2
        {
            return TransformationResult {
                problem,
                back_translator: Box::new(IdentityBackTranslator),
            };
        }

        let initial = Self::problem_size(&problem);
        // The constituent transforms rebuild via `ChcProblem::new()`, which
        // drops problem-level metadata. Snapshot it here and restore after the
        // loop so downstream stages still see it: datatype definitions feed
        // the stage-0.5 DtFlattener and SMT contexts, action names feed TLA+
        // per-action reports, and the query-evidence bit keeps
        // `ChcProblem::validate` satisfied when every query arm is pruned.
        let datatype_defs = problem.datatype_defs().clone();
        let action_names: Vec<String> = problem.action_names().to_vec();
        let had_query_evidence = problem.has_query_evidence();
        let mut current = problem;
        let mut translators: Vec<Box<dyn BackTranslator>> = Vec::new();
        let start = Instant::now();

        'rounds: for round_idx in 0..MAX_CONDENSE_ROUNDS {
            let before = Self::problem_size(&current);

            let round: Vec<Box<dyn Transformer>> = vec![
                Box::new(UnreachableClauseEliminator::new().with_verbose(self.verbose)),
                Box::new(ConstantPropagator::new().with_verbose(self.verbose)),
                // Store-to-load forwarding runs AFTER constant propagation
                // (so propagated constants materialize constant indices) and
                // BEFORE LocalVarEliminator (forwarded loads become scalar
                // equalities LVE eliminates; the round's trailing
                // DeadParamEliminator then slices array args made dead).
                Box::new(ArrayStoreForwarder::new().with_verbose(self.verbose)),
                // Ground-table read concretization (item 4 Stage 1) runs
                // right after forwarding: read-only ground-pin table arrays
                // become dead so ConstantPropagator/ClauseInliner/DPE can
                // shrink further in the same round. Self-gating global
                // analysis; identity on any check failure.
                Box::new(GroundTableReadConcretizer::new().with_verbose(self.verbose)),
                Box::new(LocalVarEliminator::new().with_verbose(self.verbose)),
                Box::new(self.round_inliner()),
                Box::new(MultiEdgeMerger::new()),
                Box::new(DeadParamEliminator::new().with_verbose(self.verbose)),
            ];
            for (step_idx, transformer) in round.into_iter().enumerate() {
                // FIX #2a: never hang. Check the wall budget and the mean
                // constraint-size gate before every constituent; on bail,
                // return the best-so-far result (the stack so far is exact).
                if let Some(reason) = self.should_bail(start, &current) {
                    if self.verbose {
                        safe_eprintln!(
                            "CHC condense: bailing at round {} step {} ({}); returning best-so-far",
                            round_idx + 1,
                            step_idx + 1,
                            reason
                        );
                    }
                    break 'rounds;
                }
                let result = transformer.transform(current);
                current = result.problem;
                translators.push(result.back_translator);
            }

            let after = Self::problem_size(&current);
            // Continue only while the round strictly shrinks the problem.
            if after.0 >= before.0 && after.1 >= before.1 {
                break;
            }
        }

        // Restore problem-level metadata lost to constituent rebuilds. The
        // loss is all-or-nothing per rebuild, so emptiness marks a rebuild.
        if current.datatype_defs().is_empty() {
            for (name, ctors) in datatype_defs {
                current.add_datatype_def(name, ctors);
            }
        }
        if current.action_names().is_empty() {
            for name in action_names {
                current.declare_action(name);
            }
        }
        // If condense pruned EVERY query arm (each was vacuous or rode an
        // underivable predicate), the condensed problem is trivially safe but
        // would fail `ChcProblem::validate` (NoQuery) and push engines to
        // Unknown. Mimic the parser: register a vacuously-false query that
        // `add_clause` prunes while recording pruned-query evidence.
        if had_query_evidence && !current.has_query_evidence() {
            current.add_clause(HornClause::new(
                ClauseBody::new(Vec::new(), Some(ChcExpr::Bool(false))),
                ClauseHead::False,
            ));
        }

        if self.verbose {
            let after = Self::problem_size(&current);
            if after != initial {
                safe_eprintln!(
                    "CHC condense: {} predicates / {} clauses -> {} / {} ({:.1}s)",
                    initial.0,
                    initial.1,
                    after.0,
                    after.1,
                    start.elapsed().as_secs_f64()
                );
            } else {
                safe_eprintln!(
                    "CHC condense: completed with no shrink ({:.1}s)",
                    start.elapsed().as_secs_f64()
                );
            }
        }

        translators.reverse();
        TransformationResult {
            problem: current,
            back_translator: Box::new(CompositeBackTranslator { inner: translators }),
        }
    }
}

/// Kept-clause index -> original clause index bookkeeping shared by the
/// condense constituents that drop or rewrite clauses.
///
/// `ChcProblem::add_clause` may itself prune a clause whose constraint folds
/// to `false`; recording indices through [`record_add`](Self::record_add)
/// keeps the map exact in that case too. Unmapped indices are cleared so the
/// portfolio's original-clause replay stays fail-closed instead of replaying
/// against the wrong clause.
pub(crate) struct ClauseIndexMap {
    kept_to_original: Vec<usize>,
    identity: bool,
}

impl ClauseIndexMap {
    pub(crate) fn new() -> Self {
        Self {
            kept_to_original: Vec::new(),
            identity: true,
        }
    }

    /// Add `clause` (originally at `original_idx`) to `problem`, recording
    /// the index it lands at (if any).
    pub(crate) fn record_add(
        &mut self,
        problem: &mut ChcProblem,
        clause: HornClause,
        original_idx: usize,
    ) {
        let before = problem.clauses().len();
        problem.add_clause(clause);
        if problem.clauses().len() > before {
            if before != original_idx {
                self.identity = false;
            }
            self.kept_to_original.push(original_idx);
        } else {
            // add_clause pruned the clause (constraint folded to false).
            self.identity = false;
        }
    }

    fn translate_clause_index(&self, clause_index: usize) -> Option<usize> {
        self.kept_to_original.get(clause_index).copied()
    }

    /// Ground back-translator for this map: the kept→original index map is
    /// exactly the 1:1 clause correspondence the ground translator needs.
    pub(crate) fn ground_translator(
        &self,
        name: &'static str,
        input_problem: std::sync::Arc<ChcProblem>,
    ) -> crate::ground_derivation::clause_map::ClauseMapGroundTranslator {
        crate::ground_derivation::clause_map::ClauseMapGroundTranslator::from_index_map(
            name,
            input_problem,
            &self.kept_to_original,
        )
    }

    pub(crate) fn translate_invalidity(&self, mut witness: InvalidityWitness) -> InvalidityWitness {
        if self.identity {
            return witness;
        }
        for step in &mut witness.steps {
            if let Some(clause_index) = step.clause_index {
                step.clause_index = self.translate_clause_index(clause_index);
            }
        }
        if let Some(derivation) = &mut witness.witness {
            if let Some(query_clause) = derivation.query_clause {
                derivation.query_clause = self.translate_clause_index(query_clause);
            }
            for entry in &mut derivation.entries {
                if let Some(incoming_clause) = entry.incoming_clause {
                    entry.incoming_clause = self.translate_clause_index(incoming_clause);
                }
            }
        }
        witness
    }
}

#[allow(clippy::unwrap_used)]
#[cfg(test)]
#[path = "tests.rs"]
mod tests;
