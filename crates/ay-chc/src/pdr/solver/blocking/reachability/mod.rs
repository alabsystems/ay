// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

mod nonlinear;
mod single_body;

pub(in crate::pdr::solver) use nonlinear::NlRound;

use super::*;
use crate::pdr::cube::literals::LitCube;
use crate::pdr::solver::spacer_core::stats::{CubeSource, Q1CoreSource};
use crate::pdr::solver::spacer_core::Budget;
use crate::smt::types::FarkasConflict;

/// Per-clause interpolation data preserved during predecessor reachability checks.
pub(in crate::pdr::solver) struct ClauseInterpolationData {
    pub head_args: Vec<ChcExpr>,
    pub constraint: ChcExpr,
    /// Clause-local Farkas conflicts preserved from the SMT result (#6484).
    pub farkas_conflicts: Vec<FarkasConflict>,
}

/// Result of ONE clause's (or (clause, fact) pair's) blocking query (Workstream B,
/// `DESIGN` §3.3, contract C2). Indices refer to `pob.cube().lits()`.
///
/// Coverage rule (C2): P emits exactly one record per UNSAT `(clause, fact?)`
/// pair, INCLUDING the `propagate_equalities() == false` shortcut (all-true,
/// `exact: false`) and hyperedge clauses (all-true, `exact: false`). L treats
/// any defining clause without a record as all-true inexact (INV-L1).
#[derive(Debug, Clone)]
#[allow(dead_code)] // `uses_level` is written by the session backend only (R4)
pub(in crate::pdr::solver) struct ClauseCore {
    pub clause_index: usize,
    /// `Some(i)` for the per-fact expansion at prev_level 0 / level 0.
    pub fact_index: Option<usize>,
    /// `core[i]` ⇔ literal `i` is needed; all-true when unknown. `len() == pob.cube().len()`.
    pub core: Vec<bool>,
    /// Came from a solver core (proxied / session), not "all literals".
    pub exact: bool,
    /// The Q1 that produced it carried a non-trivial `exclusion_constraint`.
    pub had_exclusion: bool,
    /// Session only; `None` on legacy.
    pub uses_level: Option<usize>,
}

impl ClauseCore {
    /// The all-true inexact record (coverage placeholder).
    pub(in crate::pdr::solver) fn all_true(
        clause_index: usize,
        fact_index: Option<usize>,
        n: usize,
        had_exclusion: bool,
    ) -> Self {
        Self {
            clause_index,
            fact_index,
            core: vec![true; n],
            exact: false,
            had_exclusion,
            uses_level: None,
        }
    }
}

/// Data collected during predecessor reachability, passed to lemma construction.
pub(in crate::pdr::solver) struct ReachabilityData {
    pub transition_constraints: Vec<ChcExpr>,
    pub clause_interpolation_data: Vec<ClauseInterpolationData>,
    /// Per-clause blocking cores (Workstream B, C2); empty on the legacy path.
    #[allow(dead_code)] // read by `lemma_from_cores` (WP-B1-L, R1)
    pub cores: Vec<ClauseCore>,
}

impl PdrSolver {
    /// Whether the Spacer lane consumes this POB's blocking evidence: the
    /// lane is on and `block_linear` (C4) will read `ReachabilityData.cores`
    /// for this predicate. Off ⇒ no core solve is issued and `cores` stays
    /// empty (legacy path).
    pub(super) fn lane_records_cores(&self, pob: &ProofObligation) -> bool {
        self.spacer_core && (self.lane_nonlinear || self.linear_pred(pob.predicate))
    }

    /// The unknown-predecessor states recorded at `parent_level` for `pred`
    /// (canonical form) — the free constructor's step-4 exclusion check.
    pub(super) fn excluded_states(
        parent_level: usize,
        pred: PredicateId,
        unknown_predecessors: &[(usize, PredicateId, ChcExpr)],
    ) -> Vec<ChcExpr> {
        unknown_predecessors
            .iter()
            .filter(|(level, p, _)| *level == parent_level && *p == pred)
            .map(|(_, _, state)| state.clone())
            .collect()
    }

    /// The literal view of a child cube under the lane (`PredecessorState.lits`,
    /// contract C8): `Some` whenever the lane is on (R1: the legacy cube's
    /// top-level conjuncts; R2 replaces the constructor), `None` otherwise.
    pub(super) fn lane_child_lits(&self, cube: &ChcExpr) -> Option<LitCube> {
        if self.spacer_core {
            Some(LitCube::from_expr(cube))
        } else {
            None
        }
    }

    /// C2/C3: the `ClauseCore` of one UNSAT `(clause, fact?)` pair — the core
    /// of `background ∧ lits_on_head` over `pob.cube().lits()` by index, where
    /// `lits_on_head[i] = apply_to_args(pred, lits[i], head_args)`. The
    /// background carries NO exclusion (`q1_core_for_clause` is itself an
    /// exclusion-free query; an exclusion-dependent UNSAT therefore comes back
    /// all-true inexact and `had_exclusion` tells Phase 0 to decide, D4). A
    /// literal that cannot be instantiated on the head ⇒ all-true inexact.
    /// Never changes the Q1 verdict (S4).
    pub(super) fn lane_clause_core(
        &mut self,
        pob: &ProofObligation,
        clause_index: usize,
        fact_index: Option<usize>,
        background: &[ChcExpr],
        head_args: &[ChcExpr],
        had_exclusion: bool,
    ) -> ClauseCore {
        let cube = pob.cube();
        let n = cube.len();
        let mut lits_on_head = Vec::with_capacity(n);
        for lit in cube.lits() {
            match self.apply_to_args(pob.predicate, lit, head_args) {
                Some(l) => lits_on_head.push(l),
                None => {
                    self.spacer_stats
                        .record_q1(Q1CoreSource::None, Some(n), false, None, 0);
                    return ClauseCore::all_true(clause_index, fact_index, n, had_exclusion);
                }
            }
        }
        let mut per_call = self
            .smt
            .current_timeout()
            .unwrap_or(std::time::Duration::from_secs(5));
        if self.lane_nonlinear {
            // The nonlinear lane's backgrounds carry every atom's summary (a
            // disjunction of facts at frame index 0): an assumption solve that
            // does not finish fast is cut to the all-true inexact core, which
            // Phase A recovers through verdict-only queries (CONST_sum_6_5:
            // 14 clauses × the 5 s query cap per blocked POB).
            per_call = per_call.min(nonlinear::NL_CORE_PER_CALL);
        }
        let mut budget = Budget::per_call_only(per_call);
        // C3 records its own `record_q1` (source / size / exactness / solve
        // time); P records only the pairs L never sees (the propagate
        // shortcut above and the uninstantiable-literal arm).
        let (core, exact) = self.q1_core_for_clause(background, &lits_on_head, &mut budget);
        debug_assert_eq!(core.len(), n, "BUG (C3): core length != cube length");
        let core = if core.len() == n { core } else { vec![true; n] };
        let exact = exact && core.len() == n;
        let core_size = core.iter().filter(|b| **b).count();
        if self.config.verbose {
            safe_eprintln!(
                "PDR-SPACER: q1 core clause={} fact={:?} |core|={}/{} exact={} exclusion={}",
                clause_index,
                fact_index,
                core_size,
                n,
                exact,
                had_exclusion
            );
        }
        ClauseCore {
            clause_index,
            fact_index,
            core,
            exact,
            had_exclusion,
            uses_level: None,
        }
    }

    #[allow(clippy::result_large_err)]
    pub(in crate::pdr::solver) fn check_predecessor_reachability(
        &mut self,
        pob: &mut ProofObligation,
        unknown_predecessors: &[(usize, PredicateId, ChcExpr)],
    ) -> Result<ReachabilityData, BlockResult> {
        let prev_level = pob.level - 1;
        let mut transition_constraints: Vec<ChcExpr> = Vec::new();
        let mut clause_interpolation_data: Vec<ClauseInterpolationData> = Vec::new();
        // Workstream B (C2): one `ClauseCore` per UNSAT (clause, fact?) pair
        // under the lane; empty on the legacy path.
        let mut cores: Vec<ClauseCore> = Vec::new();
        let lane = self.lane_records_cores(pob);
        // Track whether any clause returned SAT but cube extraction failed.
        // If so, we must NOT create a blocking lemma (the state may be reachable
        // via that clause), but we can try other clauses first in case they produce
        // a complete model (#3121).
        let mut had_sat_no_cube = false;

        // #5877: Collect eligible clause indices and rotate to diversify CTI
        // generation. Without rotation, the first SAT clause always wins,
        // producing CTIs from only one transition branch. Rotation ensures
        // different branches fire across successive blocking calls.
        let eligible_clause_indices: Vec<usize> = self
            .problem
            .clauses_defining_with_index(pob.predicate)
            .map(|(index, _)| index)
            .collect();
        let rotation = self.telemetry.clause_rotation_counter;
        self.telemetry.clause_rotation_counter = rotation.wrapping_add(1);

        for offset in 0..eligible_clause_indices.len() {
            let clause_index =
                eligible_clause_indices[(rotation + offset) % eligible_clause_indices.len()];
            let clause = self.problem.clauses()[clause_index].clone();
            if self.is_cancelled() {
                return Err(BlockResult::Unknown);
            }
            let head_args = match &clause.head {
                crate::ClauseHead::Predicate(_, a) => a.as_slice(),
                crate::ClauseHead::False => continue,
            };

            let clause_constraint = clause
                .body
                .constraint
                .clone()
                .unwrap_or(ChcExpr::Bool(true));
            let state_on_head = match self.apply_to_args(pob.predicate, &pob.state, head_args) {
                Some(e) => e,
                None => return Err(BlockResult::Unknown),
            };
            let guarded =
                self.clause_guarded_constraint(pob.predicate, clause_index, head_args, pob.level);
            // The nonlinear lane: ONE multi-atom query per clause (facts and
            // linear clauses included), must coverage by reach facts.
            if self.lane_nonlinear {
                let cl = nonlinear::NlClause {
                    index: clause_index,
                    clause: &clause,
                    head_args,
                    constraint: &clause_constraint,
                    state_on_head: &state_on_head,
                    guarded: &guarded,
                };
                match self.nl_check_clause(
                    pob,
                    unknown_predecessors,
                    &cl,
                    &mut cores,
                    &mut had_sat_no_cube,
                ) {
                    None => continue,
                    Some(result) => return Err(result),
                }
            }
            let base = ChcExpr::and_all([
                clause_constraint.clone(),
                state_on_head.clone(),
                guarded.clone(),
            ]);

            if clause.body.predicates.is_empty() {
                let query = self.bound_int_vars(base.clone());
                let projection_vars = self.projection_vars_for_args(pob.predicate, head_args);
                let result = if self.uses_arrays && query.contains_array_ops() {
                    let query_delta = ChcExpr::and(state_on_head.clone(), guarded.clone());
                    Self::check_array_clause_query(
                        &mut self.smt,
                        &mut self.array_clause_sessions,
                        ArraySessionKey::HeadFact { clause_index },
                        &clause_constraint,
                        &query_delta,
                        &query,
                        self.max_array_params,
                    )
                } else if self.incremental_pdr_enabled() {
                    let check_timeout = self.smt.current_timeout();
                    let seg_key =
                        super::super::prop_solver::SegmentKey::ClauseBlocking { clause_index };
                    let prop = super::super::core::ensure_prop_solver_split(
                        &mut self.prop_solvers,
                        &self.frames,
                        pob.predicate,
                    );
                    prop.register_segment(seg_key, &clause_constraint);
                    let incr_result = prop.check_clause_blocking(
                        0,
                        clause_index,
                        &[state_on_head.clone(), guarded.clone()],
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
                        .with_phase_seed_model(pob.smt_model.as_ref(), |smt| smt.check_sat(&query))
                };
                let farkas_conflicts = if result.is_unsat() {
                    extract_farkas_from_result(result.clone())
                } else {
                    Vec::new()
                };
                match result {
                    SmtResult::Sat(model) => {
                        self.record_reachable_pob_countermodel(pob, head_args, &model);
                        // Workstream B R2 (§4.1.2): under `free_pob` the child is
                        // the projection of `T_fact ∧ post` onto the POB's own
                        // canonical variables (today only the fact is projected,
                        // which drops the POB's constraint); S spawns it at level 0.
                        if self.lane_free_pob(pob.predicate) {
                            let child = self.child_cube_from_model(
                                pob.predicate,
                                head_args,
                                &clause_constraint,
                                &state_on_head,
                                &model,
                                None,
                                &[],
                            );
                            self.spacer_stats.record_free_child(
                                child.source,
                                child.substituted,
                                &child.exact,
                            );
                            let Some(cube) = child.cube else {
                                had_sat_no_cube = true;
                                self.telemetry.sat_no_cube_events += 1;
                                continue;
                            };
                            return Err(BlockResult::Reachable(Box::new(PredecessorState {
                                predicate: pob.predicate,
                                state: cube.expr().clone(),
                                clause_index,
                                smt_model: model,
                                derivation_id: None,
                                lits: Some(cube),
                            })));
                        }
                        if self.spacer_core {
                            self.spacer_stats.minimize_calls += 1;
                        }
                        let model = Self::minimize_projection_model_with_context(
                            &mut self.smt,
                            &projection_vars,
                            &query,
                            model,
                        );
                        // #8660: Prefer scalar-only cubes for array problems,
                        // but keep property-relevant array selects when the
                        // property reads arrays (Mem-track fix).
                        let cube = if self.uses_arrays {
                            self.cube_from_model_array_aware(
                                pob.predicate,
                                head_args,
                                &clause_constraint,
                                &model,
                            )
                        } else {
                            self.cube_with_mbp(pob.predicate, head_args, &clause_constraint, &model)
                        };
                        let cube = match cube {
                            Some(c) => c,
                            None => {
                                had_sat_no_cube = true;
                                self.telemetry.sat_no_cube_events += 1;
                                continue;
                            }
                        };
                        let lits = self.lane_child_lits(&cube);
                        if lits.is_some() {
                            self.spacer_stats.record_cube_source(CubeSource::Legacy, 0);
                        }
                        return Err(BlockResult::Reachable(Box::new(PredecessorState {
                            predicate: pob.predicate,
                            state: cube,
                            clause_index,
                            smt_model: model,
                            derivation_id: None,
                            lits,
                        })));
                    }
                    SmtResult::Unsat
                    | SmtResult::UnsatWithCore(_)
                    | SmtResult::UnsatWithFarkas(_) => {
                        // Workstream B (C2/C3): the fact clause of the POB's own
                        // predicate at level > 0 — background `T_fact ∧ guarded`,
                        // no exclusion, `fact_index: None` (it is the clause).
                        if lane {
                            let core = self.lane_clause_core(
                                pob,
                                clause_index,
                                None,
                                &[clause_constraint.clone(), guarded.clone()],
                                head_args,
                                false,
                            );
                            cores.push(core);
                        }
                        if self.config.use_interpolation {
                            let constraint_canonical =
                                if let Some(canon_vars) = self.canonical_vars(pob.predicate) {
                                    Self::translate_to_canonical_names(
                                        &clause_constraint,
                                        head_args,
                                        canon_vars,
                                    )
                                } else {
                                    clause_constraint.clone()
                                };
                            transition_constraints.push(constraint_canonical);
                            clause_interpolation_data.push(ClauseInterpolationData {
                                head_args: head_args.to_vec(),
                                constraint: clause_constraint.clone(),
                                farkas_conflicts,
                            });
                        }
                        continue;
                    }
                    SmtResult::Unknown => return Err(BlockResult::Unknown),
                }
            }

            if clause.body.predicates.len() > 1 {
                // Workstream B (C2 coverage rule): a hyperedge clause is
                // recorded all-true inexact. Unreachable under `lane` today
                // (a predicate with a hyperedge clause is not `linear_pred`);
                // kept so the rule holds if the gate ever widens.
                if lane {
                    let n = pob.cube().len();
                    cores.push(ClauseCore::all_true(clause_index, None, n, false));
                }
                if !self.config.use_mixed_summaries {
                    continue;
                }

                let num_body_preds = clause.body.predicates.len();
                for last_may_index in 0..num_body_preds {
                    // Deadline check per hyperedge body: each iteration issues an
                    // SMT query, and the enclosing clause loop only checks the
                    // deadline between clauses (line ~56). Degrade to Unknown
                    // (fail-closed) rather than running these SMT queries past the
                    // solve timeout.
                    if self.is_cancelled() {
                        return Err(BlockResult::Unknown);
                    }
                    if let Some((mixed_summary, refine_pred, refine_args)) =
                        self.get_edge_mixed_summary(&clause, prev_level, last_may_index)
                    {
                        let projection_vars =
                            self.projection_vars_for_args(refine_pred, &refine_args);
                        let query = self.bound_int_vars(ChcExpr::and_all([
                            mixed_summary.clone(),
                            state_on_head.clone(),
                        ]));

                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: Checking hyperedge with {} body predicates, last_may_index={}",
                                num_body_preds, last_may_index
                            );
                            safe_eprintln!("  mixed_summary={}", mixed_summary);
                            safe_eprintln!("  state_on_head={}", state_on_head);
                            safe_eprintln!("  query={}", query);
                        }

                        let result = if self.incremental_pdr_enabled() {
                            let bounded_mixed = self.bound_int_vars(mixed_summary.clone());
                            let check_timeout = self.smt.current_timeout();
                            let prop = super::super::core::ensure_prop_solver_split(
                                &mut self.prop_solvers,
                                &self.frames,
                                pob.predicate,
                            );
                            let incr_result = prop.check_hyperedge_blocking(
                                pob.level,
                                &[bounded_mixed, state_on_head.clone()],
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
                        };
                        match result {
                            SmtResult::Sat(model) => {
                                self.record_reachable_pob_countermodel(pob, head_args, &model);
                                let model = Self::minimize_projection_model_with_context(
                                    &mut self.smt,
                                    &projection_vars,
                                    &query,
                                    model,
                                );
                                if self.config.verbose {
                                    safe_eprintln!(
                                        "  Result: SAT -> refining predicate {} at index {}",
                                        refine_pred.index(),
                                        last_may_index
                                    );
                                }
                                let projection_formula = ChcExpr::and_all([
                                    mixed_summary.clone(),
                                    state_on_head.clone(),
                                ]);
                                let cube = self.cube_with_mbp(
                                    refine_pred,
                                    &refine_args,
                                    &projection_formula,
                                    &model,
                                );
                                if let Some(cube) = cube {
                                    let derivation_id = if self.config.use_derivations {
                                        let body_preds: Vec<_> = clause.body.predicates.clone();
                                        Some(self.allocate_hyperedge_derivation_from_preds(
                                            &body_preds,
                                            clause_index,
                                            last_may_index,
                                            pob.predicate,
                                            pob.level,
                                            pob.state.clone(),
                                            pob.query_clause,
                                            prev_level,
                                        ))
                                    } else {
                                        None
                                    };
                                    let lits = self.lane_child_lits(&cube);
                                    return Err(BlockResult::Reachable(Box::new(
                                        PredecessorState {
                                            predicate: refine_pred,
                                            state: cube,
                                            clause_index,
                                            smt_model: model,
                                            derivation_id,
                                            lits,
                                        },
                                    )));
                                }
                                had_sat_no_cube = true;
                                self.telemetry.sat_no_cube_events += 1;
                            }
                            SmtResult::Unsat
                            | SmtResult::UnsatWithCore(_)
                            | SmtResult::UnsatWithFarkas(_) => {
                                if self.config.verbose {
                                    safe_eprintln!("  Result: UNSAT, trying next index");
                                }
                                continue;
                            }
                            SmtResult::Unknown => break,
                        }
                    }
                }
                continue;
            }

            let single_body_result = if prev_level == 0 {
                self.check_prev_level_zero_predecessor(
                    pob,
                    unknown_predecessors,
                    clause_index,
                    &base,
                    &clause_constraint,
                    head_args,
                    &state_on_head,
                    &guarded,
                    &clause,
                    &mut transition_constraints,
                    &mut clause_interpolation_data,
                    &mut had_sat_no_cube,
                    &mut cores,
                )
            } else {
                self.check_single_body_predecessor(
                    pob,
                    prev_level,
                    unknown_predecessors,
                    clause_index,
                    &base,
                    &clause_constraint,
                    head_args,
                    &state_on_head,
                    &guarded,
                    &clause,
                    &mut transition_constraints,
                    &mut clause_interpolation_data,
                    &mut had_sat_no_cube,
                    &mut cores,
                )
            };
            match single_body_result {
                Ok(()) => continue,
                Err(result) => return Err(result),
            }
        }

        if had_sat_no_cube {
            return Err(BlockResult::Unknown);
        }

        Ok(ReachabilityData {
            transition_constraints,
            clause_interpolation_data,
            cores,
        })
    }
}
