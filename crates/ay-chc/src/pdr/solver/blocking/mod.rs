// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Proof-obligation blocking and lemma generalization.
//!
//! ## Submodules
//!
//! - `generalization`: Lemma generalization (try_strengthen, generalize_blocking_formula, IUC shrinking)
//! - `utils`: Model projection, integer minimization, hyperedge derivation allocation

mod array_skolem;
mod bool_normalization;
mod bv_generalization;
mod generalization;
mod generalization_implication;
mod generalization_iuc;
mod generalization_weakening;
mod global_generalize;
mod interpolation;
mod lemma;
mod lemma_refinement;
mod property_indices;
mod reachability;
mod utils;

#[allow(clippy::unwrap_used, clippy::panic)]
#[cfg(test)]
mod tests;

pub(super) use array_skolem::ArraySkolemState;
pub(super) use property_indices::PropertyArrayIndices;

use bool_normalization::{denormalize_int_to_bool, extract_farkas_from_result};
use reachability::{ClauseInterpolationData, ReachabilityData};

use super::{
    filter_out_lit, filter_out_lit_with_eq_retry, BlockResult, BvBitDecompositionGeneralizer,
    BvFlagGuardGeneralizer, ChcExpr, ChcOp, ChcSort, ChcVar, FxHashMap, FxHashSet, Lemma,
    LemmaGeneralizer, LiteralWeakeningGeneralizer, PdrGeneralizerAdapter, PdrSolver, PobKind,
    PredecessorState, PredicateId, ProofObligation, SmtResult, SmtValue,
};
use crate::pdr::solver::ArraySessionKey;
use crate::proof_interpolation::InterpolantKind;
use crate::smt::IncrementalCheckResult;
use std::sync::Arc;

impl PdrSolver {
    pub(in crate::pdr::solver) fn record_reachable_pob_countermodel(
        &mut self,
        pob: &ProofObligation,
        head_args: &[ChcExpr],
        model: &FxHashMap<String, SmtValue>,
    ) {
        let canonical_vars = self.canonical_vars(pob.predicate).map(|vars| vars.to_vec());
        let frame_epoch = self.frames_lemma_epoch();
        super::core::record_validated_blocking_countermodel_from_head_args(
            &mut self.caches.implication_cache,
            frame_epoch,
            canonical_vars.as_deref(),
            pob.predicate,
            pob.level,
            head_args,
            model,
            &pob.state,
        );
    }

    /// Try to block a proof obligation using SMT queries (with local blocked states)
    ///
    /// NOTE: `pob` is mutable to allow storing `smt_model` from already-blocked checks (#801).
    pub(in crate::pdr::solver) fn block_obligation_with_local_blocked(
        &mut self,
        pob: &mut ProofObligation,
        _blocked_at_level_0: &[(PredicateId, ChcExpr)],
        unknown_predecessors: &[(usize, PredicateId, ChcExpr)],
    ) -> BlockResult {
        // Step 0a: Quick syntactic check for relational contradictions.
        // This catches cases where the SMT solver returns Unknown due to mod/parity constraints
        // but the relational invariants clearly block the bad state.
        // Example: frame has (a <= b), bad state has (a > b) → contradiction!
        if self.relational_invariant_blocks_state(pob.predicate, pob.level, &pob.state) {
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: State blocked by relational invariant at level {}",
                    pob.level
                );
            }
            return BlockResult::AlreadyBlocked;
        }

        // Step 0b: Quick syntactic check for parity (modular) contradictions.
        // This catches cases where the SMT solver returns Unknown on mod arithmetic
        // but the parity invariants clearly block the bad state.
        // Example: frame has (= (mod x 6) 0), bad state is (not (= (mod x 6) 0)) → contradiction!
        if self.parity_invariant_blocks_state(pob.predicate, pob.level, &pob.state) {
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: State blocked by parity invariant at level {}",
                    pob.level
                );
            }
            return BlockResult::AlreadyBlocked;
        }

        // Early cancellation check before expensive SMT work
        if self.is_cancelled() {
            return BlockResult::Unknown;
        }

        // Step 1: Check if pob.state is already blocked by lemmas AT THIS LEVEL ONLY
        // (Not cumulative - we need to check reachability even if blocked at lower levels)
        //
        // #6358: Use the incremental blocking context when available. This avoids
        // the full reset→convert→Tseitin→CDCL cycle on every query. The persistent
        // SAT solver keeps learned clauses and VSIDS scores across queries.
        if let Some(frame_constraint) =
            self.frames[pob.level].get_predicate_constraint(pob.predicate)
        {
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: Checking already-blocked at level {} for pred {}, state={}",
                    pob.level,
                    pob.predicate.index(),
                    pob.state
                );
            }

            // #6358: Per-predicate prop_solver for already-blocked checks.
            //
            // Pure-LIA + incremental enabled: one solve via prop_solver, trusted.
            // Non-pure-LIA or incremental disabled: one solve via non-incremental.
            // No double-solve: each query goes to exactly one solver.
            let blocked_result = if self.incremental_pdr_enabled() {
                let bounded_state = self.bound_int_vars(pob.state.clone());
                let check_timeout = self.smt.current_timeout();
                let prop = self.ensure_prop_solver(pob.predicate);
                prop.check_already_blocked(pob.level, &bounded_state, check_timeout)
            } else {
                // #7984: Use persistent executor backend for integer arithmetic.
                // Falls back to non-incremental internally on Unknown.
                let query = self.bound_int_vars(ChcExpr::and(frame_constraint, pob.state.clone()));
                match self.check_sat_via_executor_backend(&query) {
                    SmtResult::Sat(m) => IncrementalCheckResult::Sat(m),
                    SmtResult::Unsat
                    | SmtResult::UnsatWithCore(_)
                    | SmtResult::UnsatWithFarkas(_) => IncrementalCheckResult::Unsat,
                    SmtResult::Unknown => IncrementalCheckResult::Unknown,
                }
            };

            match blocked_result {
                IncrementalCheckResult::Unsat => {
                    if self.config.verbose {
                        safe_eprintln!("PDR: State already blocked at level {}", pob.level);
                    }
                    return BlockResult::AlreadyBlocked;
                }
                IncrementalCheckResult::Sat(m) => {
                    if self.config.verbose {
                        safe_eprintln!("PDR: already-blocked check returned SAT: {:?}", m);
                    }
                    // Store model in POB for point blocking fallback (#801)
                    pob.smt_model = Some(m);
                    // State is not blocked at this level, continue to check reachability
                }
                IncrementalCheckResult::Unknown => {
                    if self.config.verbose {
                        safe_eprintln!("PDR: already-blocked check returned Unknown");
                    }
                    // State is not blocked at this level, continue to check reachability
                }
            }
        } else if self.config.verbose {
            safe_eprintln!(
                "PDR: No frame constraint for pred {} at level {}",
                pob.predicate.index(),
                pob.level
            );
        }

        // Step 2: Check reachability.
        //
        // We only extract predecessors for linear clauses (<= 1 predicate in the body).
        // For interpolation-based lemma learning (Golem/Spacer technique), we collect
        // transition constraints from each UNSAT clause to compute an interpolant.
        //
        // N1 approach (#917): Track per-clause data for interpolation in clause-local names.
        // We keep both the combined constraints (for combined interpolation) and per-clause
        // info (for per-clause interpolation with proper variable naming).
        let mut transition_constraints: Vec<ChcExpr> = Vec::new();

        let mut clause_interpolation_data: Vec<ClauseInterpolationData> = Vec::new();

        if pob.level == 0 {
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: Level 0 checking init reachability for state={}",
                    pob.state
                );
            }
            let mut found_clause = false;
            let mut had_sat_no_cube = false;
            for (clause_index, clause) in self
                .problem
                .clauses_defining_with_index(pob.predicate)
                .filter(|(_, clause)| clause.is_fact())
            {
                // #2887: Check cancellation between SMT queries in clause loop.
                if self.is_cancelled() {
                    return BlockResult::Unknown;
                }
                found_clause = true;

                let fact_constraint = clause
                    .body
                    .constraint
                    .clone()
                    .unwrap_or(ChcExpr::Bool(true));
                let head_args = match &clause.head {
                    crate::ClauseHead::Predicate(_, a) => a.as_slice(),
                    crate::ClauseHead::False => continue,
                };
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: Level 0 clause {}: fact_constraint={}, head_args={:?}",
                        clause_index,
                        fact_constraint,
                        head_args
                    );
                }
                let state_on_fact = match self.apply_to_args(pob.predicate, &pob.state, head_args) {
                    Some(e) => e,
                    None => {
                        if self.config.verbose {
                            safe_eprintln!("PDR: Level 0: apply_to_args failed");
                        }
                        return BlockResult::Unknown;
                    }
                };
                // Clone fact_constraint for MBP - it's used in query but also needed for projection
                let query = self
                    .bound_int_vars(ChcExpr::and(fact_constraint.clone(), state_on_fact.clone()));
                if self.config.verbose {
                    safe_eprintln!("PDR: Level 0 query: {}", query);
                }

                let projection_vars = self.projection_vars_for_args(pob.predicate, head_args);
                // #6366: Skip O(expr_size) tree walk for pure-LIA problems.
                // When uses_arrays is false, no query can contain array ops.
                let result = if self.uses_arrays && query.contains_array_ops() {
                    Self::check_array_clause_query(
                        &mut self.smt,
                        &mut self.array_clause_sessions,
                        ArraySessionKey::HeadFact { clause_index },
                        &fact_constraint,
                        &state_on_fact,
                        &query,
                        self.max_array_params,
                    )
                } else {
                    // #6358: Per-predicate prop_solver for clause predecessor.
                    // Pure-LIA: one solve via prop_solver. Non-pure-LIA: one solve
                    // via non-incremental. No double-solve.
                    if self.incremental_pdr_enabled() {
                        let check_timeout = self.smt.current_timeout();
                        let seg_key =
                            super::prop_solver::SegmentKey::ClauseBlocking { clause_index };
                        let prop = super::core::ensure_prop_solver_split(
                            &mut self.prop_solvers,
                            &self.frames,
                            pob.predicate,
                        );
                        prop.register_segment(seg_key, &fact_constraint);
                        let incr_result = prop.check_clause_blocking(
                            0,
                            clause_index,
                            &[state_on_fact.clone()],
                            check_timeout,
                            pob.smt_model.as_ref(),
                        );
                        match incr_result {
                            IncrementalCheckResult::Unsat => SmtResult::Unsat,
                            IncrementalCheckResult::Sat(model) => SmtResult::Sat(model),
                            IncrementalCheckResult::Unknown => SmtResult::Unknown,
                        }
                    } else {
                        self.smt.reset();
                        self.smt
                            .with_phase_seed_model(pob.smt_model.as_ref(), |smt| {
                                smt.check_sat(&query)
                            })
                    }
                };
                // #6484: Extract Farkas conflicts before the match consumes the result
                let farkas_conflicts = if result.is_unsat() {
                    extract_farkas_from_result(result.clone())
                } else {
                    Vec::new()
                };
                match result {
                    SmtResult::Sat(model) => {
                        let model = Self::minimize_projection_model_with_context(
                            &mut self.smt,
                            &projection_vars,
                            &query,
                            model,
                        );
                        if self.config.verbose {
                            safe_eprintln!("PDR: Level 0: SAT with model {:?}", model);
                        }
                        // #8660: Prefer scalar-only cubes for array problems,
                        // but keep property-relevant array selects when the
                        // property reads arrays (Mem-track fix).
                        let cube = if self.uses_arrays {
                            self.cube_from_model_array_aware(
                                pob.predicate,
                                head_args,
                                &fact_constraint,
                                &model,
                            )
                        } else {
                            self.cube_with_mbp(pob.predicate, head_args, &fact_constraint, &model)
                        };
                        let cube = match cube {
                            Some(c) => c,
                            None => {
                                if self.config.verbose {
                                    safe_eprintln!(
                                        "PDR: Level 0: cube_from_model failed, trying next clause"
                                    );
                                }
                                had_sat_no_cube = true;
                                self.telemetry.sat_no_cube_events += 1;
                                continue;
                            }
                        };
                        return BlockResult::Reachable(Box::new(PredecessorState {
                            predicate: pob.predicate,
                            state: cube,
                            clause_index,
                            smt_model: model,
                            derivation_id: None,
                        }));
                    }
                    SmtResult::Unsat
                    | SmtResult::UnsatWithCore(_)
                    | SmtResult::UnsatWithFarkas(_) => {
                        if self.config.verbose {
                            safe_eprintln!("PDR: Level 0: UNSAT");
                        }
                        // Collect transition constraint for interpolation
                        if self.config.use_interpolation {
                            // Translate clause constraint to canonical names for consistent
                            // A/B naming in interpolation (#966)
                            let constraint_canonical =
                                if let Some(canon_vars) = self.canonical_vars(pob.predicate) {
                                    Self::translate_to_canonical_names(
                                        &fact_constraint,
                                        head_args,
                                        canon_vars,
                                    )
                                } else {
                                    fact_constraint.clone()
                                };
                            transition_constraints.push(constraint_canonical);
                            // N1: Also track per-clause data for clause-local interpolation
                            clause_interpolation_data.push(ClauseInterpolationData {
                                head_args: head_args.to_vec(),
                                constraint: fact_constraint.clone(),
                                farkas_conflicts,
                            });
                        }
                        continue;
                    }
                    SmtResult::Unknown => {
                        if self.config.verbose {
                            safe_eprintln!("PDR: Level 0: SMT Unknown");
                        }
                        // #6047: Previously stripped array conjuncts and retried
                        // with integer-only constraints. This created "Swiss cheese"
                        // where arrays never participated in invariant discovery.
                        // The executor adapter (check_sat.rs) now dispatches array
                        // queries to ay-dpll's full Executor with array theory
                        // support. If it still returns Unknown, accept it.
                        return BlockResult::Unknown;
                    }
                }
            }
            if had_sat_no_cube {
                return BlockResult::Unknown;
            }
            if self.config.verbose && !found_clause {
                safe_eprintln!("PDR: Level 0: no matching fact clause found");
            }
        } else {
            match self.check_predecessor_reachability(pob, unknown_predecessors) {
                Ok(ReachabilityData {
                    transition_constraints: new_transition_constraints,
                    clause_interpolation_data: new_clause_interpolation_data,
                }) => {
                    transition_constraints = new_transition_constraints;
                    clause_interpolation_data = new_clause_interpolation_data;
                }
                Err(result) => return result,
            }
        }

        // Cancellation check before lemma generalization (can involve multiple SMT queries)
        if self.is_cancelled() {
            return BlockResult::Unknown;
        }

        self.block_unreachable_obligation(pob, transition_constraints, clause_interpolation_data)
    }

    /// Extract a variable and constant from an equality or negated distinct.
    /// Delegated to generalization module.
    pub(in crate::pdr::solver) fn extract_equality_or_not_distinct(
        expr: &ChcExpr,
    ) -> Option<(ChcVar, i128)> {
        crate::pdr::generalization::extract_equality_or_not_distinct(expr)
    }
}
