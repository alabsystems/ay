// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::ChcVar;
use ay_core::kani_compat::DetHashSet as FxHashSet;

impl KindSolver {
    /// Remaining wall-clock budget for this Kind run.
    pub(super) fn remaining_total_budget(
        &self,
        run_start: ay_core::time::Instant,
    ) -> std::time::Duration {
        self.config
            .total_timeout
            .saturating_sub(run_start.elapsed())
    }

    /// Cap a nominal timeout by the remaining total Kind budget.
    pub(super) fn timeout_for_remaining(
        &self,
        remaining: std::time::Duration,
        nominal: std::time::Duration,
    ) -> std::time::Duration {
        remaining.min(nominal)
    }

    /// Cap the standard Kind query timeout by the remaining total budget.
    pub(super) fn query_timeout_for_remaining(
        &self,
        remaining: std::time::Duration,
    ) -> std::time::Duration {
        self.timeout_for_remaining(remaining, self.config.query_timeout)
    }

    /// Cap the standard Kind query timeout by the remaining total budget.
    pub(super) fn query_timeout_for_run(
        &self,
        run_start: ay_core::time::Instant,
    ) -> std::time::Duration {
        self.query_timeout_for_remaining(self.remaining_total_budget(run_start))
    }

    /// Cap a fixed-cost helper stage by the remaining total Kind budget.
    pub(super) fn stage_timeout_for_run(
        &self,
        run_start: ay_core::time::Instant,
        nominal: std::time::Duration,
    ) -> std::time::Duration {
        self.timeout_for_remaining(self.remaining_total_budget(run_start), nominal)
    }

    /// Remaining budget for PROOF VALIDATION stages: `total_timeout` plus
    /// `validation_grace` minus elapsed. Search stages must keep using
    /// `remaining_total_budget`; only validation of an already-found proof
    /// may draw on the grace (see `KindConfig::validation_grace`).
    pub(super) fn remaining_validation_budget(
        &self,
        run_start: ay_core::time::Instant,
    ) -> std::time::Duration {
        (self.config.total_timeout + self.config.validation_grace)
            .saturating_sub(run_start.elapsed())
    }

    /// Cap a fixed-cost proof-validation stage by the validation budget.
    pub(super) fn validation_stage_timeout_for_run(
        &self,
        run_start: ay_core::time::Instant,
        nominal: std::time::Duration,
    ) -> std::time::Duration {
        self.timeout_for_remaining(self.remaining_validation_budget(run_start), nominal)
    }

    /// Derive the timeout for a fresh induction cross-check (#7739).
    ///
    /// Contract: `min(remaining_budget, 2 * query_timeout)`.
    pub(super) fn fresh_cross_check_timeout_for_remaining(
        &self,
        remaining: std::time::Duration,
    ) -> std::time::Duration {
        let nominal = self.config.query_timeout.saturating_mul(2);
        self.timeout_for_remaining(remaining, nominal)
    }

    /// Derive the timeout for a fresh induction cross-check (#7739).
    ///
    /// Contract: `min(remaining_validation_budget, 2 * query_timeout)`.
    /// Cross-checks validate an induction proof the search already found,
    /// so they draw on the validation budget (incl. grace) — a found proof
    /// must not be dropped because the search budget ran dry (#lustre).
    pub(super) fn fresh_cross_check_timeout(
        &self,
        run_start: ay_core::time::Instant,
    ) -> std::time::Duration {
        let remaining = self.remaining_validation_budget(run_start);
        self.fresh_cross_check_timeout_for_remaining(remaining)
    }

    /// Verify that an invariant satisfies init containment, query exclusion,
    /// and 1-inductiveness.
    ///
    /// Checks:
    ///   1. init => inv  (UNSAT of init ∧ ¬inv)
    ///   2. inv => ¬query  (UNSAT of inv ∧ query)
    ///   3. inv(x) ∧ Tr(x,x') => inv(x')  (defense in depth)
    ///
    /// The inductiveness check (3) catches cases where k-to-1 conversion fails
    /// and the returned invariant is only k-inductive, not 1-inductive.
    pub(super) fn verify_invariant_init_query(
        &self,
        ts: &TransitionSystem,
        inv: &ChcExpr,
        run_start: ay_core::time::Instant,
    ) -> bool {
        let mut ctx = self.problem.make_smt_context();
        let nominal_timeout = std::time::Duration::from_secs(2);

        // 1. init => inv
        let verify_timeout = self.validation_stage_timeout_for_run(run_start, nominal_timeout);
        if verify_timeout.is_zero() {
            if self.config.base.verbose {
                safe_eprintln!(
                    "KIND: invariant verification skipped: budget exhausted before init check"
                );
            }
            return false;
        }
        let init_check = ChcExpr::and(ts.init.clone(), ChcExpr::not(inv.clone()));
        if !ctx
            .check_sat_with_timeout(&init_check, verify_timeout)
            .is_unsat()
        {
            if self.config.base.verbose {
                safe_eprintln!("KIND: invariant verification FAILED: init =/=> inv");
            }
            return false;
        }

        // 2. inv => ¬query
        ctx.reset();
        let verify_timeout = self.validation_stage_timeout_for_run(run_start, nominal_timeout);
        if verify_timeout.is_zero() {
            if self.config.base.verbose {
                safe_eprintln!(
                    "KIND: invariant verification skipped: budget exhausted before query check"
                );
            }
            return false;
        }
        let query_check = ChcExpr::and(inv.clone(), ts.query.clone());
        if !ctx
            .check_sat_with_timeout(&query_check, verify_timeout)
            .is_unsat()
        {
            if self.config.base.verbose {
                safe_eprintln!("KIND: invariant verification FAILED: inv ∧ query is SAT");
            }
            return false;
        }

        // 3. inv(x) ∧ Tr(x,x') => inv(x')  (1-inductiveness)
        ctx.reset();
        let inv_at_0 = ts.send_through_time(inv, 0);
        let trans = ts.transition_at(0);
        let neg_inv_at_1 = ChcExpr::not(ts.send_through_time(inv, 1));
        let inductive_check = ChcExpr::and_all([inv_at_0, trans, neg_inv_at_1]);
        let verify_timeout = self.validation_stage_timeout_for_run(run_start, nominal_timeout);
        if verify_timeout.is_zero() {
            if self.config.base.verbose {
                safe_eprintln!(
                    "KIND: invariant verification skipped: budget exhausted before 1-inductiveness check"
                );
            }
            return false;
        }
        if !ctx
            .check_sat_with_timeout(&inductive_check, verify_timeout)
            .is_unsat()
        {
            if self.config.base.verbose {
                safe_eprintln!(
                    "KIND: invariant verification FAILED: not 1-inductive (inv ∧ Tr ∧ ¬inv' is SAT)"
                );
            }
            return false;
        }

        true
    }

    /// Independently re-verify a k-induction proof using fresh SMT contexts.
    ///
    /// Defense-in-depth for BV problems (#5877): the incremental solver used during
    /// the main solve loop may produce false-UNSAT due to accumulated BV bitblast
    /// state. Re-checking the critical induction formula with a fresh non-incremental
    /// context reduces the risk of accepting a false-UNSAT result.
    ///
    /// Checks both the induction step AND that init ∧ query is UNSAT (base property).
    /// Returns true only if both checks pass with the fresh context.
    pub(super) fn verify_bv_induction_fresh(
        &self,
        ts: &TransitionSystem,
        k: usize,
        is_forward: bool,
        run_start: ay_core::time::Instant,
    ) -> bool {
        let nominal_timeout = std::time::Duration::from_secs(5);
        let timeout = self.validation_stage_timeout_for_run(run_start, nominal_timeout);
        if timeout.is_zero() {
            if self.config.base.verbose {
                safe_eprintln!(
                    "KIND: BV fresh verification skipped at k={} (budget exhausted)",
                    k
                );
            }
            return false;
        }

        // 1. Re-check the induction step with a fresh context.
        // Forward: ¬Q(x0) ∧ Tr(x0,x1) ∧ ¬Q(x1) ∧ ... ∧ ¬Q(xk) ∧ Q(x{k+1})
        // Backward: Init(x0) ∧ Tr(x0,x1) ∧ ¬Init(x1) ∧ ... ∧ Tr(xk,x{k+1}) ∧ ¬Init(x{k+1})
        let mut ctx = self.problem.make_smt_context();
        let induction_formula = if is_forward {
            let mut conjuncts = Vec::new();
            for i in 0..=k {
                conjuncts.push(ts.neg_query_at(i));
                conjuncts.push(ts.transition_at(i));
            }
            conjuncts.push(ts.query_at(k + 1));
            ChcExpr::and_all(conjuncts)
        } else {
            let mut conjuncts = vec![ts.init_at(0)];
            for i in 0..=k {
                conjuncts.push(ts.transition_at(i));
                conjuncts.push(ts.neg_init_at(i + 1));
            }
            ChcExpr::and_all(conjuncts)
        };

        let induction_result = ctx.check_sat_with_timeout(&induction_formula, timeout);
        if !induction_result.is_unsat() {
            if self.config.base.verbose {
                safe_eprintln!(
                    "KIND: BV fresh induction re-check at k={} FAILED ({} induction) — \
                     original was false-UNSAT",
                    k,
                    if is_forward { "forward" } else { "backward" }
                );
            }
            return false;
        }

        // 2. Re-check init ∧ query is UNSAT (base property: init states are safe).
        ctx.reset();
        let timeout = self.validation_stage_timeout_for_run(run_start, nominal_timeout);
        if timeout.is_zero() {
            if self.config.base.verbose {
                safe_eprintln!(
                    "KIND: BV fresh base verification skipped at k={} (budget exhausted)",
                    k
                );
            }
            return false;
        }
        let base_formula = ChcExpr::and(ts.init.clone(), ts.query.clone());
        let base_result = ctx.check_sat_with_timeout(&base_formula, timeout);
        if !base_result.is_unsat() {
            if self.config.base.verbose {
                safe_eprintln!(
                    "KIND: BV fresh base check (init ∧ query) FAILED — init contains bad states"
                );
            }
            return false;
        }

        if self.config.base.verbose {
            safe_eprintln!(
                "KIND: BV fresh verification passed at k={} ({} induction)",
                k,
                if is_forward { "forward" } else { "backward" }
            );
        }
        true
    }

    /// Cross-check forward induction at depth k with a fresh SMT context (#6789).
    ///
    /// Returns `FreshCheckOutcome` so callers can distinguish an explicit SAT
    /// counterexample from a budget-limited UNKNOWN.
    pub(super) fn verify_forward_induction_fresh(
        &self,
        ts: &TransitionSystem,
        k: usize,
        run_start: ay_core::time::Instant,
    ) -> FreshCheckOutcome {
        let timeout = self.fresh_cross_check_timeout(run_start);
        let outcome = if timeout.is_zero() {
            FreshCheckOutcome::BudgetUnknown { timeout }
        } else {
            let mut ctx = self.problem.make_smt_context();
            let mut conjuncts = Vec::new();
            for i in 0..=k {
                conjuncts.push(ts.neg_query_at(i));
                conjuncts.push(ts.transition_at(i));
            }
            conjuncts.push(ts.query_at(k + 1));
            let formula = ChcExpr::and_all(conjuncts);
            let result = ctx.check_sat_with_timeout(&formula, timeout);
            FreshCheckOutcome::from_smt_result(&result, timeout)
        };
        if !matches!(outcome, FreshCheckOutcome::ConfirmedUnsat) {
            if self.config.base.verbose {
                safe_eprintln!(
                    "KIND: Fresh forward induction cross-check at k={} = {} (timeout={timeout:?}, incremental UNSAT not confirmed)",
                    k,
                    outcome.as_str(),
                );
            }
        }
        outcome
    }

    /// Cross-check backward induction at depth k with a fresh SMT context (#6789).
    ///
    /// Returns `FreshCheckOutcome` so callers can distinguish an explicit SAT
    /// counterexample from a budget-limited UNKNOWN.
    pub(super) fn verify_backward_induction_fresh(
        &self,
        ts: &TransitionSystem,
        k: usize,
        run_start: ay_core::time::Instant,
    ) -> FreshCheckOutcome {
        let timeout = self.fresh_cross_check_timeout(run_start);
        let outcome = if timeout.is_zero() {
            FreshCheckOutcome::BudgetUnknown { timeout }
        } else {
            let mut ctx = self.problem.make_smt_context();
            let mut conjuncts = vec![ts.init_at(0)];
            for i in 0..=k {
                conjuncts.push(ts.transition_at(i));
                conjuncts.push(ts.neg_init_at(i + 1));
            }
            let formula = ChcExpr::and_all(conjuncts);
            let result = ctx.check_sat_with_timeout(&formula, timeout);
            FreshCheckOutcome::from_smt_result(&result, timeout)
        };
        if !matches!(outcome, FreshCheckOutcome::ConfirmedUnsat) {
            if self.config.base.verbose {
                safe_eprintln!(
                    "KIND: Fresh backward induction cross-check at k={} = {} (timeout={timeout:?}, incremental UNSAT not confirmed)",
                    k,
                    outcome.as_str(),
                );
            }
        }
        outcome
    }

    /// Diagnostic: cross-check the forward induction formula at depth k
    /// using a completely fresh (non-incremental) SMT context (#6789).
    ///
    /// Builds the formula: ¬Q(x0) ∧ Tr(x0,x1) ∧ ¬Q(x1) ∧ ... ∧ ¬Q(xk) ∧ Tr(xk,x{k+1}) ∧ Q(x{k+1})
    /// and checks satisfiability with a fresh solver. If this returns SAT while the
    /// incremental solver said UNSAT, we have a false-UNSAT bug (H2 in the design).
    /// If this also returns UNSAT, the formula itself encodes a degenerate TS (H1/H3).
    ///
    /// Also performs TS sanity checks: is the query satisfiable? Is init ∧ transition
    /// satisfiable? A degenerate TS (unsatisfiable transition, unsatisfiable query)
    /// would make induction trivially pass.
    pub(super) fn diagnose_induction_at_k(
        &self,
        ts: &TransitionSystem,
        k: usize,
        run_start: ay_core::time::Instant,
    ) {
        let nominal_timeout = std::time::Duration::from_secs(10);

        fn smt_label(r: &crate::smt::SmtResult) -> &'static str {
            if matches!(r, crate::smt::SmtResult::Sat(_)) {
                "SAT"
            } else if r.is_unsat() {
                "UNSAT"
            } else {
                "UNKNOWN"
            }
        }

        // Sanity check 1: Is the query alone satisfiable?
        let mut ctx = self.problem.make_smt_context();
        let timeout = self.stage_timeout_for_run(run_start, nominal_timeout);
        if timeout.is_zero() {
            safe_eprintln!("KIND DIAG: skipped (budget exhausted)");
            return;
        }
        let r = ctx.check_sat_with_timeout(&ts.query, timeout);
        safe_eprintln!(
            "KIND DIAG: query sat = {} {}",
            smt_label(&r),
            if r.is_unsat() {
                "(BUG: query unsatisfiable — induction trivially passes)"
            } else {
                ""
            }
        );

        // Sanity check 2: Is the transition satisfiable?
        ctx.reset();
        let timeout = self.stage_timeout_for_run(run_start, nominal_timeout);
        if timeout.is_zero() {
            safe_eprintln!("KIND DIAG: stopped before transition check (budget exhausted)");
            return;
        }
        let r = ctx.check_sat_with_timeout(&ts.transition_at(0), timeout);
        safe_eprintln!(
            "KIND DIAG: transition sat = {} {}",
            smt_label(&r),
            if r.is_unsat() {
                "(BUG: transition unsatisfiable — induction trivially passes)"
            } else {
                ""
            }
        );

        // Sanity check 3: Is init ∧ ¬query satisfiable? (Are there any safe init states?)
        ctx.reset();
        let timeout = self.stage_timeout_for_run(run_start, nominal_timeout);
        if timeout.is_zero() {
            safe_eprintln!("KIND DIAG: stopped before init/query check (budget exhausted)");
            return;
        }
        let init_neg_query = ChcExpr::and(ts.init.clone(), ChcExpr::not(ts.query.clone()));
        let r = ctx.check_sat_with_timeout(&init_neg_query, timeout);
        safe_eprintln!(
            "KIND DIAG: init ∧ ¬query sat = {} {}",
            smt_label(&r),
            if r.is_unsat() {
                "(all init states are bad — should be Unsafe!)"
            } else {
                ""
            }
        );

        // Cross-check: build the forward induction formula from scratch and check
        // with a fresh solver.
        ctx.reset();
        let mut conjuncts = Vec::new();
        for i in 0..=k {
            conjuncts.push(ts.neg_query_at(i));
            conjuncts.push(ts.transition_at(i));
        }
        conjuncts.push(ts.query_at(k + 1));
        let fwd_formula = ChcExpr::and_all(conjuncts);
        safe_eprintln!(
            "KIND DIAG: forward induction formula at k={} has {} nodes",
            k,
            fwd_formula.node_count(100_000),
        );
        let timeout = self.stage_timeout_for_run(run_start, nominal_timeout);
        if timeout.is_zero() {
            safe_eprintln!("KIND DIAG: stopped before fresh forward check (budget exhausted)");
            return;
        }
        let r = ctx.check_sat_with_timeout(&fwd_formula, timeout);
        let fwd_label = smt_label(&r);
        safe_eprintln!(
            "KIND DIAG: fresh fwd induction k={} = {} {}",
            k,
            fwd_label,
            if matches!(r, crate::smt::SmtResult::Sat(_)) {
                "(FALSE-UNSAT in incremental! H2 confirmed)"
            } else if r.is_unsat() {
                "(formula genuinely UNSAT — problem in TS, H1/H3)"
            } else {
                ""
            }
        );

        // Cross-check: base case formula at k=0.
        ctx.reset();
        let timeout = self.stage_timeout_for_run(run_start, nominal_timeout);
        if timeout.is_zero() {
            safe_eprintln!("KIND DIAG: stopped before base-case check (budget exhausted)");
            return;
        }
        let base_formula = ChcExpr::and(ts.init_at(0), ts.query_at(0));
        let r = ctx.check_sat_with_timeout(&base_formula, timeout);
        safe_eprintln!(
            "KIND DIAG: fresh base (init ∧ query) k=0 = {} {}",
            smt_label(&r),
            if matches!(r, crate::smt::SmtResult::Sat(_)) {
                "(BUG: init intersects query!)"
            } else {
                ""
            }
        );

        // Dump the extracted TS formulas for external Z3 cross-check.
        // Read from the centralized `TraceConfig` singleton (#8495, #8834);
        // populated via `--kind-dump-dir=DIR` (B72: the env fallback is
        // retired).
        if let Some(dump_dir) = ay_core::trace_config().kind_dump_dir.as_deref() {
            let dump_path = std::path::Path::new(dump_dir);
            if let Err(e) = std::fs::create_dir_all(dump_path) {
                safe_eprintln!("KIND DIAG: cannot create dump dir: {e}");
                return;
            }
            let fwd_path = dump_path.join(format!("kind_fwd_induction_k{k}.smt2"));
            let base_path = dump_path.join("kind_base_k0.smt2");
            let ts_path = dump_path.join("kind_ts_info.txt");

            // Write TS info (not valid SMT-LIB, but useful for inspection)
            let _ = std::fs::write(
                &ts_path,
                format!(
                    "Vars: {:?}\nInit: {}\nTransition: {}\nQuery: {}\n",
                    ts.vars
                        .iter()
                        .map(|v| format!("{}: {}", v.name, v.sort))
                        .collect::<Vec<_>>(),
                    ts.init,
                    ts.transition,
                    ts.query,
                ),
            );
            safe_eprintln!("KIND DIAG: TS info dumped to {}", ts_path.display());

            // Write forward induction formula
            let _ = std::fs::write(&fwd_path, format!("{fwd_formula}"));
            safe_eprintln!(
                "KIND DIAG: forward induction formula dumped to {}",
                fwd_path.display()
            );

            // Write base case formula
            let _ = std::fs::write(&base_path, format!("{base_formula}"));
            safe_eprintln!(
                "KIND DIAG: base case formula dumped to {}",
                base_path.display()
            );
        }
    }

    /// Convert a k-inductive invariant to 1-inductive, falling back to the original.
    ///
    /// When k > 0, attempts interpolation-based conversion via [`k_to_1_inductive::convert`].
    /// Returns the original invariant if conversion fails or k == 0.
    pub(super) fn strengthen_to_1_inductive(
        &self,
        inv: &ChcExpr,
        k: usize,
        ts: &TransitionSystem,
        run_start: ay_core::time::Instant,
    ) -> ChcExpr {
        if k > 0 {
            let convert_timeout = self
                .stage_timeout_for_run(run_start, crate::k_to_1_inductive::DEFAULT_CONVERT_TIMEOUT);
            if convert_timeout.is_zero() {
                if self.config.base.verbose {
                    safe_eprintln!(
                        "KIND: skipping k-to-1 conversion at k={} (budget exhausted)",
                        k
                    );
                }
                return inv.clone();
            }
            crate::k_to_1_inductive::convert_with_timeout(inv, k, ts, convert_timeout)
                .unwrap_or_else(|| {
                    if self.config.base.verbose {
                        safe_eprintln!(
                            "KIND: k-to-1 conversion failed at k={}, using k-inductive invariant",
                            k
                        );
                    }
                    inv.clone()
                })
        } else {
            inv.clone()
        }
    }

    /// Return true only for non-empty models over the original predicate
    /// argument vocabulary.
    ///
    /// Kind constructs invariants over transition-system variables (`v0`,
    /// `v1`, ...). `build_single_pred_model` maps those to the canonical CHC
    /// model variables (`__pN_aM`). Any remaining variable is a clause local,
    /// timestep variable, or other internal symbol; such a model cannot be
    /// accepted as an original-CHC SAFE witness.
    pub(super) fn safe_model_has_original_vocabulary(&self, model: &InvariantModel) -> bool {
        if model.is_empty() || model.len() != self.problem.predicates().len() {
            return false;
        }

        for pred in self.problem.predicates() {
            let Some(interp) = model.get(&pred.id) else {
                return false;
            };
            if interp.vars.len() != pred.arg_sorts.len() {
                return false;
            }

            for (arg_idx, (var, sort)) in interp.vars.iter().zip(&pred.arg_sorts).enumerate() {
                let expected_name = format!("__p{}_a{arg_idx}", pred.id.index());
                if var.name != expected_name || var.sort != *sort {
                    return false;
                }
            }

            let allowed_vars: FxHashSet<ChcVar> = interp.vars.iter().cloned().collect();
            if interp
                .formula
                .vars()
                .into_iter()
                .any(|var| !allowed_vars.contains(&var))
            {
                return false;
            }
        }

        true
    }

    /// Build a Safe result from an invariant expression, using the unified model format.
    /// Requires prior verification via `verify_invariant_init_query`.
    pub(super) fn make_safe(&self, invariant: ChcExpr) -> KindResult {
        match build_single_pred_model(&self.problem, invariant) {
            Some(model) if self.safe_model_has_original_vocabulary(&model) => {
                KindResult::Safe(model)
            }
            Some(model) => {
                if self.config.base.verbose {
                    safe_eprintln!(
                        "KIND: Safe invariant rejected: model is empty or contains non-original vocabulary (predicates={})",
                        model.len(),
                    );
                }
                KindResult::Unknown
            }
            None => {
                if self.config.base.verbose {
                    safe_eprintln!("KIND: Safe invariant rejected: could not build model");
                }
                KindResult::Unknown
            }
        }
    }

    /// Build an Unsafe result with concrete trace extracted from the SMT model.
    ///
    /// Kind's base case SAT result contains values for all versioned variables
    /// (time 0: `x`, time k>0: `x_k`). We extract per-step assignments to build
    /// a proper counterexample that passes portfolio validation without the
    /// skeleton rejection path (#5010).
    pub(super) fn make_unsafe_with_trace(
        &self,
        ts: &TransitionSystem,
        model: &FxHashMap<String, SmtValue>,
        depth: usize,
    ) -> KindResult {
        let pred = self
            .problem
            .predicates()
            .first()
            .map_or(PredicateId::new(0), |p| p.id);

        let steps: Vec<CounterexampleStep> = (0..=depth)
            .map(|step| {
                let var_names = ts.state_var_names_at(step);
                let assignments: FxHashMap<String, i64> = model
                    .iter()
                    .filter(|(k, _)| var_names.contains(k.as_str()))
                    .filter_map(|(k, v)| {
                        // i128-lockstep: pdr::CounterexampleStep assignments
                        // are an i64 boundary; drop (fail closed) witness
                        // values outside i64 instead of truncating (the old
                        // BitVec arm silently wrapped via `as i64`).
                        let val = match v {
                            SmtValue::Int(n) => i64::try_from(*n).ok(),
                            SmtValue::Bool(b) => Some(if *b { 1 } else { 0 }),
                            SmtValue::BitVec(val, _) => i64::try_from(*val).ok(),
                            _ => None,
                        };
                        val.map(|v| (k.clone(), v))
                    })
                    .collect();
                CounterexampleStep::new(pred, assignments)
            })
            .collect();

        KindResult::Unsafe(Counterexample::new(steps))
    }
}
