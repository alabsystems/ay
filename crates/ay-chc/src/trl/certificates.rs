// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! TRL certificate helpers: unsafe replay, diameter verification, invariant
//! synthesis, and trace reconstruction.
//!
//! Extracted from `trl/mod.rs` as part of #4701 wave 2.

use super::*;

/// Result of verifying a diameter claim with a fresh solver.
#[derive(Debug)]
pub(super) enum DiameterResult {
    /// Diameter genuinely reached: no path exists even without blocking clauses.
    Confirmed,
    /// False diameter: blocking clauses caused the UNSAT. Paths still exist.
    Spurious,
    /// Fresh solver returned Unknown — cannot determine.
    Inconclusive,
}

/// Result of replaying an unsafe TRL witness against the original transition system.
#[derive(Debug)]
pub(super) enum UnsafeReplayResult {
    /// Exact-depth replay confirmed the original system is genuinely unsafe.
    Confirmed(Counterexample),
    /// The learned shortcut path was spurious; the original system has no such trace.
    Spurious,
    /// Fresh replay returned Unknown, so soundness cannot be decided.
    Inconclusive,
}

impl TrlSolver {
    /// Get the set of state variables for CVP.
    pub(super) fn get_state_var_set(&self) -> FxHashSet<ChcVar> {
        self.ts.vars.iter().cloned().collect()
    }

    /// Replay a TRL-reported unsafe depth against the original transition system.
    ///
    /// The incremental TRL encoding may reach the query through learned shortcut
    /// relations. Before returning `Unsafe`, re-check exact-depth reachability
    /// using only the original transition system and extract a concrete witness.
    pub(super) fn replay_unsafe_depth(&self, depth: usize) -> UnsafeReplayResult {
        let reachability = ChcExpr::and_all(vec![
            self.ts.init_at(0),
            self.ts.k_transition(depth),
            self.ts.query_at(depth),
        ]);
        let mut smt = SmtContext::new();
        // Use executor fallback — this is a critical soundness check where
        // completeness matters. The internal DPLL(T) loop may return Unknown
        // on formulas the full executor can solve (#7181).
        match smt.check_sat_with_executor_fallback_timeout(&reachability, TRL_PER_CHECK_TIMEOUT) {
            SmtResult::Sat(model) => {
                UnsafeReplayResult::Confirmed(self.extract_counterexample_from_model(depth, &model))
            }
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                UnsafeReplayResult::Spurious
            }
            SmtResult::Unknown => UnsafeReplayResult::Inconclusive,
        }
    }

    fn extract_counterexample_from_model(
        &self,
        depth: usize,
        model: &FxHashMap<String, SmtValue>,
    ) -> Counterexample {
        let steps = (0..=depth)
            .map(|time| {
                let assignments = self
                    .ts
                    .vars
                    .iter()
                    .filter_map(|var| {
                        let versioned = TransitionSystem::version_var(var, time);
                        model.get(&versioned.name).and_then(|value| {
                            Self::counterexample_assignment_value(value)
                                .map(|numeric| (var.name.clone(), numeric))
                        })
                    })
                    .collect();
                CounterexampleStep::new(self.ts.predicate, assignments)
            })
            .collect();
        Counterexample::new(steps)
    }

    fn counterexample_assignment_value(value: &SmtValue) -> Option<i64> {
        match value {
            SmtValue::Bool(b) => Some(if *b { 1 } else { 0 }),
            // i128-lockstep: pdr::CounterexampleStep assignments are an i64
            // boundary; drop (fail closed) witness values outside i64 instead
            // of truncating, matching the BitVec arm below.
            SmtValue::Int(n) => i64::try_from(*n).ok(),
            SmtValue::BitVec(v, _) => i64::try_from(*v).ok(),
            // Beyond-i128 witnesses never fit i64 (canonical-form invariant);
            // drop fail-closed like the out-of-range Int case above.
            SmtValue::BigInt(_)
            | SmtValue::Real(_)
            | SmtValue::Opaque(_)
            | SmtValue::ConstArray(_)
            | SmtValue::ArrayMap { .. }
            | SmtValue::Datatype(..) => None,
        }
    }

    // ---- Diameter verification and invariant construction ----

    /// Verify diameter claim with a fresh solver (no blocking clauses).
    ///
    /// Uses only the ORIGINAL transition system — learned transitions are
    /// derived shortcuts that don't add new reachable states. If no path
    /// of length `depth` exists using only the original transition from
    /// init, the system's state space is bounded. Option A from #7181.
    ///
    /// - UNSAT → genuine diameter (no path exists in original system)
    /// - SAT → blocking clauses caused false diameter (paths still exist)
    /// - Unknown → inconclusive
    pub(super) fn verify_diameter_fresh(&self, depth: usize) -> DiameterResult {
        // Build: init@0 AND T_orig(0,1) AND T_orig(1,2) AND ... AND T_orig(D-1,D)
        // Using TransitionSystem's BMC helpers keeps the formula clean
        // (no trace_id, no __trp_n, no disjunctions over learned relations).
        let formula = ChcExpr::and(self.ts.init_at(0), self.ts.k_transition(depth));
        let mut smt = SmtContext::new();
        let timeout = Duration::from_secs(5);
        // Use executor fallback — this is a critical soundness check where
        // completeness matters (#7181).
        match smt.check_sat_with_executor_fallback_timeout(&formula, timeout) {
            SmtResult::Sat(_) => DiameterResult::Spurious,
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                DiameterResult::Confirmed
            }
            SmtResult::Unknown => DiameterResult::Inconclusive,
        }
    }

    pub(super) fn synthesize_safe_model_from_expanded_system(
        &self,
        depth: usize,
    ) -> Option<InvariantModel> {
        let expanded_problem = self.build_expanded_problem();
        let pdr_config = PdrConfig {
            max_frames: depth.saturating_add(10).max(10),
            max_iterations: depth.saturating_mul(32).max(128),
            max_obligations: 50_000,
            verbose: self.config.base.verbose,
            cancellation_token: self.config.base.cancellation_token.clone(),
            solve_timeout: Some(Duration::from_secs(5)),
            ..PdrConfig::default()
        };
        let mut pdr = PdrSolver::new(expanded_problem.clone(), pdr_config);
        match pdr.solve() {
            ChcEngineResult::Safe(model) => {
                return self.remap_synthesized_model(model);
            }
            ChcEngineResult::Unsafe(_)
            | ChcEngineResult::Unknown
            | ChcEngineResult::NotApplicable => {}
        }

        let kind_config = KindConfig::with_engine_config(
            depth.saturating_add(10).max(10),
            TRL_PER_CHECK_TIMEOUT,
            Duration::from_secs(5),
            self.config.base.verbose,
            self.config.base.cancellation_token.clone(),
        );
        let mut kind = KindSolver::new(expanded_problem, kind_config);
        match kind.solve() {
            ChcEngineResult::Safe(model) => self.remap_synthesized_model(model),
            ChcEngineResult::Unsafe(_)
            | ChcEngineResult::Unknown
            | ChcEngineResult::NotApplicable => None,
        }
    }

    fn build_expanded_problem(&self) -> ChcProblem {
        let mut problem = ChcProblem::new();
        let pred = problem.declare_predicate(
            "trl_expanded_inv",
            self.ts.vars.iter().map(|var| var.sort.clone()).collect(),
        );
        let state_args: Vec<ChcExpr> = self.ts.vars.iter().cloned().map(ChcExpr::var).collect();
        let next_args: Vec<ChcExpr> = self
            .ts
            .vars
            .iter()
            .map(|v| {
                let next_var = ChcVar::new(format!("{}_next", v.name), v.sort.clone());
                ChcExpr::var(next_var)
            })
            .collect();

        problem.add_clause(HornClause::fact(
            self.ts.init.clone(),
            pred,
            state_args.clone(),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(pred, state_args.clone())],
                Some(self.expanded_transition_relation()),
            ),
            ClauseHead::Predicate(pred, next_args),
        ));
        problem.add_clause(HornClause::query(ClauseBody::new(
            vec![(pred, state_args)],
            Some(self.ts.query.clone()),
        )));
        problem
    }

    fn expanded_transition_relation(&self) -> ChcExpr {
        match self.learned.as_slice() {
            [single] => single.clone(),
            many => ChcExpr::or_all(many.to_vec()),
        }
    }

    /// Remap expanded-system PDR/KIND invariant to use the transition system's
    /// actual state variables instead of PDR's internal `__p0_a{i}` naming.
    ///
    /// This preserves the state-space form so that the portfolio adapter's
    /// `SingleLoopSafeWitness::from_trl()` receives vars matching the
    /// SingleLoop `state_vars`, enabling correct per-location back-translation.
    ///
    /// Previous approach renamed to `__p{pred}_a{i}` which lost the state-space
    /// structure needed for multi-predicate SingleLoop problems (#7170).
    fn remap_synthesized_model(&self, model: InvariantModel) -> Option<InvariantModel> {
        let synthetic_interp = model.iter().next().map(|(_, interp)| interp.clone())?;
        // Use the TS state vars directly — preserves state-space form for
        // SingleLoop back-translation via the shared singleloop_safe adapter.
        let target_vars: Vec<ChcVar> = self.ts.vars.clone();
        let subst: Vec<(ChcVar, ChcExpr)> = synthetic_interp
            .vars
            .iter()
            .zip(target_vars.iter())
            .map(|(old, new)| (old.clone(), ChcExpr::var(new.clone())))
            .collect();

        let mut remapped = InvariantModel::new();
        remapped.set(
            self.ts.predicate,
            PredicateInterpretation::new(target_vars, synthetic_interp.formula.substitute(&subst)),
        );
        remapped.verification_method = InvariantVerificationMethod::TrlExpandedSystem;
        remapped.individually_inductive = model.individually_inductive;
        Some(remapped)
    }

    /// Build trace from model.
    pub(super) fn build_trace_from_model(
        &mut self,
        depth: usize,
        model: &FxHashMap<String, SmtValue>,
    ) {
        let rule_map = self.build_rule_map();
        let state_var_names: Vec<String> = self.ts.vars.iter().map(|v| v.name.clone()).collect();
        build_trace(
            &mut self.trace,
            depth,
            "trace_id",
            &state_var_names,
            &rule_map,
            model,
            &self.mbp,
        );
    }

    /// Build rule map for trace building.
    fn build_rule_map(&self) -> FxHashMap<i128, ChcExpr> {
        self.learned
            .iter()
            .enumerate()
            .map(|(id, trans)| {
                // LoAT encodes each transition disjunct as `t AND (trace_id = id)`.
                let trace_var = ChcVar::new("trace_id", ChcSort::Int);
                let id_constraint = ChcExpr::eq(ChcExpr::var(trace_var), ChcExpr::int(id as i128));
                (id as i128, ChcExpr::and(id_constraint, trans.clone()))
            })
            .collect()
    }
}
