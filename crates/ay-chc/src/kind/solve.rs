// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl KindSolver {
    /// Run K-Induction algorithm using 3 persistent incremental solver contexts.
    ///
    /// Ports Golem's Kind.cc pattern (lines 57-59): one solver per check type
    /// (base case, forward induction, backward induction) that accumulates
    /// constraints across k-steps. This eliminates redundant Tseitin encoding
    /// and SAT solver reconstruction at each depth.
    ///
    /// Incremental pattern:
    /// - **Base**: Init(x0) permanent; Tr(xk,x{k+1}) added per-k; Query(xk) as assumption
    /// - **Forward**: ¬Query(x0) permanent; Tr + ¬Query added per-k; Query(x{k+1}) as assumption
    /// - **Backward**: Init(x0) permanent; Tr + ¬Init added per-k; no assumptions
    pub fn solve(&mut self) -> KindResult {
        let start_time = ay_core::time::Instant::now();

        let ts = match TransitionSystem::from_chc_problem(&self.problem) {
            Ok(ts) => ts,
            Err(_) => {
                return self.finish_with_result_trace(0, KindResult::NotApplicable);
            }
        };

        if self.config.base.verbose {
            safe_eprintln!(
                "KIND: Problem has {} predicates, {} clauses",
                self.problem.predicates().len(),
                self.problem.clauses().len(),
            );
            safe_eprintln!("KIND: Extracted TS with {} vars", ts.vars.len());
            safe_eprintln!("KIND: Init expr size: {}", ts.init.node_count(10_000));
            safe_eprintln!(
                "KIND: Transition expr size: {}",
                ts.transition.node_count(10_000)
            );
            safe_eprintln!("KIND: Query expr size: {}", ts.query.node_count(10_000));
            safe_eprintln!("KIND: Init: {}", ts.init);
            safe_eprintln!("KIND: Transition: {}", ts.transition);
            safe_eprintln!("KIND: Query: {}", ts.query);
        }

        // LRA soundness guard (#5856): Kind's correctness relies on SMT completeness
        // (no false-UNSAT). For problems with Real-sorted variables, the SMT solver
        // can produce false-UNSAT on induction/BMC checks, leading to wrong safe
        // results. Skip Kind entirely until LRA model support is implemented.
        if self.problem.has_real_sorts() {
            if self.config.base.verbose {
                safe_eprintln!("KIND: Skipping for LRA problem (soundness guard #5856)");
            }
            return self.finish_with_result_trace(0, KindResult::NotApplicable);
        }

        // Array soundness guard (#8675): Kind's correctness relies on SMT
        // completeness (no false-UNSAT). For problems with Array-sorted
        // variables, the SMT solver can produce false-UNSAT on induction
        // checks. Skip Kind for array problems; PDR has its own guards.
        if self.problem.has_array_sorts() {
            if self.config.base.verbose {
                safe_eprintln!("KIND: Skipping for array problem (soundness guard #8675)");
            }
            return self.finish_with_result_trace(0, KindResult::NotApplicable);
        }

        // Check trivial case: init is empty (one-shot, not incremental)
        {
            let init_timeout = self.query_timeout_for_run(start_time);
            if init_timeout.is_zero() {
                if self.config.base.verbose {
                    safe_eprintln!("KIND: Total timeout exhausted before init check");
                }
                return self.finish_with_result_trace(0, KindResult::Unknown);
            }
            let mut ctx = self.problem.make_smt_context();
            if ctx
                .check_sat_with_timeout(&ts.init, init_timeout)
                .is_unsat()
            {
                if self.config.base.verbose {
                    safe_eprintln!("KIND: Init is empty, trivially safe");
                }
                return self.finish_with_result_trace(0, self.make_safe(ChcExpr::Bool(true)));
            }
        }

        // Shared SMT context for incremental expression conversion.
        // Shared SMT context for expression conversion.
        let mut smt = self.problem.make_smt_context();

        // Initialize 3 incremental query contexts (Golem Kind.cc:57-59).
        let (mut base_ctx, mut fwd_ctx, mut bwd_ctx) = (
            IncrementalQueryContext::new(),
            IncrementalQueryContext::new(),
            IncrementalQueryContext::new(),
        );

        // Base case background: Init(x0)
        base_ctx.assert_background(&ts.init_at(0), &mut smt);
        base_ctx.finalize_background(&smt);

        // Forward induction background: ¬Query(x0)
        fwd_ctx.assert_background(&ts.neg_query_at(0), &mut smt);
        fwd_ctx.finalize_background(&smt);

        // Backward induction background: Init(x0)
        bwd_ctx.assert_background(&ts.init_at(0), &mut smt);
        bwd_ctx.finalize_background(&smt);

        // Track whether ALL base cases k=0..current have been UNSAT (#3022).
        let mut all_base_cases_unsat = true;

        // Track the last k value where ALL base cases up to k were verified UNSAT.
        // This enables partial-BMC acceptance: if backward/forward induction succeeds
        // at depth d and we verify base cases UNSAT up to d + MIN_BMC_MARGIN,
        // we accept the deferred Safe even if later base cases time out (#5653).
        let mut last_all_unsat_k: Option<usize> = None;

        // Minimum number of base cases beyond the induction depth that must be
        // verified UNSAT before accepting a deferred Safe when full BMC validation
        // times out. Higher values = more defense against SMT false-UNSAT.
        const MIN_BMC_MARGIN: usize = 8;

        // When induction succeeds but invariant extraction fails, record the
        // depth and continue checking base cases for validation. A base case
        // SAT at k' > k_induction invalidates the induction (SMT-level bug).
        // Only return Safe after all base cases to max_k are validated UNSAT.
        let mut deferred_safe_k: Option<usize> = None;
        // Track which induction type produced the deferred safe: true=forward, false=backward.
        // Needed for BV independent re-verification (#5877).
        let mut deferred_safe_is_forward = false;
        for k in 0..=self.config.max_k {
            // TLA trace: emit IncrementK when k advances past 0
            if k > 0 {
                self.trace_phase.set("idle");
                self.trace_base_case_checked.set(false);
                self.kind_trace_step_at(k, "Running", Some("IncrementK"));
            }

            if self.config.base.is_cancelled() {
                if deferred_safe_k.is_some() {
                    if self.config.base.verbose {
                        safe_eprintln!(
                            "KIND: Cancelled at k={}, breaking to deferred acceptance",
                            k
                        );
                    }
                    break;
                }
                if self.config.base.verbose {
                    safe_eprintln!("KIND: Cancelled by portfolio after k = {}", k);
                }
                return self.finish_with_result_trace(k, KindResult::Unknown);
            }
            if start_time.elapsed() > self.config.total_timeout {
                if deferred_safe_k.is_some() {
                    if self.config.base.verbose {
                        safe_eprintln!("KIND: Timeout at k={}, breaking to deferred acceptance", k);
                    }
                    break;
                }
                if self.config.base.verbose {
                    safe_eprintln!("KIND: Total timeout exceeded after k = {}", k);
                }
                return self.finish_with_result_trace(k, KindResult::Unknown);
            }

            if self.config.base.verbose {
                safe_eprintln!("KIND: Trying k = {}", k);
            }

            // === Base case: Init(x0) ∧ Tr^k ∧ Query(xk) ===
            // Query(xk) is a temporary assumption; transitions accumulate permanently.
            self.trace_phase.set("base");
            self.trace_base_case_checked.set(true);
            self.kind_trace_step_at(k, "Running", Some("CheckBaseCase"));
            let base_timeout = self.query_timeout_for_run(start_time);
            if base_timeout.is_zero() {
                if deferred_safe_k.is_some() {
                    if self.config.base.verbose {
                        safe_eprintln!(
                            "KIND: Timeout before base case k={}, breaking to deferred acceptance",
                            k
                        );
                    }
                    break;
                }
                if self.config.base.verbose {
                    safe_eprintln!("KIND: Total timeout exceeded before base case k = {}", k);
                }
                return self.finish_with_result_trace(k, KindResult::Unknown);
            }

            let base_result = match base_ctx.check_sat_incremental(
                &[ts.query_at(k)],
                &mut smt,
                Some(base_timeout),
            ) {
                IncrementalCheckResult::Unknown => {
                    // #1362: Incremental solver returned Unknown (e.g., false-SAT
                    // caught by model verification). Retry with a direct fresh
                    // context before poisoning the base case chain.
                    // Build the full formula explicitly (init ∧ Tr^k ∧ query)
                    // to avoid any incremental context artifacts.
                    let mut fresh_exprs: Vec<ChcExpr> = vec![ts.init_at(0)];
                    for j in 0..k {
                        fresh_exprs.push(ts.transition_at(j));
                    }
                    fresh_exprs.push(ts.query_at(k));
                    let fresh_formula = ChcExpr::and_vec(fresh_exprs);
                    let mut fresh_ctx = self.problem.make_smt_context();
                    let retry_timeout = self.query_timeout_for_run(start_time);
                    let r = if retry_timeout.is_zero() {
                        crate::smt::SmtResult::Unknown
                    } else {
                        fresh_ctx.check_sat_with_timeout(&fresh_formula, retry_timeout)
                    };
                    if self.config.base.verbose {
                        safe_eprintln!(
                            "KIND: Base case Unknown at k={}, fresh retry = {}",
                            k,
                            if r.is_unsat() {
                                "UNSAT"
                            } else if matches!(r, crate::smt::SmtResult::Sat(_)) {
                                "SAT"
                            } else {
                                "UNKNOWN"
                            }
                        );
                    }
                    if r.is_unsat() {
                        IncrementalCheckResult::Unsat
                    } else if let crate::smt::SmtResult::Sat(model) = r {
                        IncrementalCheckResult::Sat(model)
                    } else {
                        IncrementalCheckResult::Unknown
                    }
                }
                other => other,
            };

            if let IncrementalCheckResult::Sat(ref model) = base_result {
                // #7371: Cross-validate base-case SAT with a fresh SMT context.
                // The incremental DPLL(T) can produce false SAT on formulas with
                // ITE + mod auxiliary variables. A fresh context re-checks from
                // scratch — only accept the counterexample when fresh also says SAT.
                let mut fresh_exprs: Vec<ChcExpr> = vec![ts.init_at(0)];
                for j in 0..k {
                    fresh_exprs.push(ts.transition_at(j));
                }
                fresh_exprs.push(ts.query_at(k));
                let fresh_conjunction = ChcExpr::and_vec(fresh_exprs);
                let mut fresh_ctx = self.problem.make_smt_context();
                let confirm_timeout = self.query_timeout_for_run(start_time);
                if confirm_timeout.is_zero() {
                    if self.config.base.verbose {
                        safe_eprintln!(
                            "KIND: Base SAT at k={} could not be confirmed before budget exhaustion",
                            k
                        );
                    }
                    return self.finish_with_result_trace(k, KindResult::Unknown);
                }
                let fresh_result =
                    fresh_ctx.check_sat_with_timeout(&fresh_conjunction, confirm_timeout);
                if fresh_result.is_sat() {
                    if self.config.base.verbose {
                        safe_eprintln!("KIND: Found counterexample at k = {}", k);
                    }
                    return self
                        .finish_with_result_trace(k, self.make_unsafe_with_trace(&ts, model, k));
                } else if fresh_result.is_unknown() {
                    if self.config.base.verbose {
                        safe_eprintln!(
                            "KIND: Base SAT at k={} not confirmed before budget exhaustion",
                            k
                        );
                    }
                    return self.finish_with_result_trace(k, KindResult::Unknown);
                }
                // Fresh context disagrees (UNSAT) — incremental produced a
                // false SAT. Skip this k for base-case tracking;
                // do NOT break the UNSAT streak since no real counterexample
                // was found. The forward induction proof is the primary
                // evidence of safety; base case checks are validation.
                if self.config.base.verbose {
                    safe_eprintln!(
                        "KIND: Base SAT at k={} not confirmed by fresh check, skipping",
                        k
                    );
                }
            } else if matches!(base_result, IncrementalCheckResult::Unknown) {
                if self.config.base.verbose {
                    safe_eprintln!("KIND: Base case unknown at k = {}", k);
                }
                all_base_cases_unsat = false;
            } else {
                if self.config.base.verbose {
                    safe_eprintln!("KIND: No path of length {} to bad state", k);
                }
                if all_base_cases_unsat {
                    last_all_unsat_k = Some(k);
                }
            }

            // Permanently add transition Tr(xk, x{k+1}) for all future base case depths.
            base_ctx.assert_permanent(&ts.transition_at(k), &mut smt);

            // #5877: Check total timeout between queries. Non-incremental BV queries
            // can exceed query_timeout due to large formula encoding. Without this
            // check, a single slow query at k=2 can consume the entire KIND budget,
            // starving the portfolio's BMC engine of time for counterexample search.
            if start_time.elapsed() > self.config.total_timeout {
                if deferred_safe_k.is_some() {
                    if self.config.base.verbose {
                        safe_eprintln!(
                            "KIND: Timeout after base case k={}, breaking to deferred acceptance",
                            k
                        );
                    }
                    break;
                }
                if self.config.base.verbose {
                    safe_eprintln!("KIND: Total timeout exceeded after base case k = {}", k);
                }
                return self.finish_with_result_trace(k, KindResult::Unknown);
            }

            // If we already have a deferred Safe result, skip induction — only
            // validate with base case checks. This avoids expensive induction
            // queries during the validation phase.
            if let Some(d) = deferred_safe_k {
                // Partial-BMC acceptance (#5653): if we've verified enough base
                // cases UNSAT beyond the induction depth, accept the deferred Safe
                // even if a later base case times out. This recovers benchmarks
                // where backward/forward induction succeeds at small k but
                // extended BMC cannot reach max_k due to query timeouts.
                //
                // Soundness: the k-induction proof establishes safety. The BMC
                // validation is defense-in-depth against SMT false-UNSAT. If we've
                // verified d + MIN_BMC_MARGIN base cases without finding a
                // counterexample, the risk of false-UNSAT is negligible.
                // BV problems are excluded (existing guard at deferred-safe exit).
                if !all_base_cases_unsat
                    && !self.problem.has_bv_sorts()
                    && !self.problem.has_real_sorts()
                    && !self.problem.has_array_sorts()
                {
                    if let Some(last_ok) = last_all_unsat_k {
                        let margin = MIN_BMC_MARGIN;
                        if last_ok >= d + margin {
                            if self.config.base.verbose {
                                safe_eprintln!(
                                    "KIND: Partial BMC validation: {} base cases verified UNSAT \
                                     (induction at k={}, last verified k={}, margin={}), accepting deferred Safe",
                                    last_ok + 1,
                                    d,
                                    last_ok,
                                    margin,
                                );
                            }
                            let inv = ChcExpr::not(ts.query_raw().clone());
                            return self.finish_with_result_trace(k, self.make_safe(inv));
                        }
                    }
                }
                continue;
            }

            // In BMC-only mode, skip forward/backward induction entirely.
            if self.config.bmc_only {
                continue;
            }

            // === Forward induction ===
            // ¬Q(x0) ∧ Tr(x0,x1) ∧ ¬Q(x1) ∧ ... ∧ Tr(xk,x{k+1}) ∧ Q(x{k+1})
            // Tr(xk,x{k+1}) is permanent; Q(x{k+1}) is a temporary assumption.
            self.trace_phase.set("forward");
            self.kind_trace_step_at(k, "Running", Some("CheckForwardInduction"));

            fwd_ctx.assert_permanent(&ts.transition_at(k), &mut smt);

            // #5877: Cap forward induction query by remaining total budget.
            let fwd_remaining = self
                .config
                .total_timeout
                .saturating_sub(start_time.elapsed());
            if fwd_remaining.is_zero() {
                if deferred_safe_k.is_some() {
                    if self.config.base.verbose {
                        safe_eprintln!(
                            "KIND: Timeout before forward induction k={}, breaking to deferred acceptance", k
                        );
                    }
                    break;
                }
                if self.config.base.verbose {
                    safe_eprintln!(
                        "KIND: Total timeout exceeded before forward induction k = {}",
                        k
                    );
                }
                return self.finish_with_result_trace(k, KindResult::Unknown);
            }
            let forward_timeout = fwd_remaining.min(self.config.query_timeout);

            let forward_result = match fwd_ctx.check_sat_incremental(
                &[ts.query_at(k + 1)],
                &mut smt,
                Some(forward_timeout),
            ) {
                IncrementalCheckResult::Unknown => {
                    let fresh_timeout = self.query_timeout_for_run(start_time);
                    if fresh_timeout.is_zero() {
                        IncrementalCheckResult::Unknown
                    } else {
                        fwd_ctx.check_sat_fresh_query(
                            &[ts.query_at(k + 1)],
                            &smt,
                            Some(fresh_timeout),
                        )
                    }
                }
                other => other,
            };

            // ¬Query(k+1) becomes permanent for the next iteration's induction chain.
            fwd_ctx.assert_permanent(&ts.neg_query_at(k + 1), &mut smt);

            if self.config.base.verbose {
                safe_eprintln!(
                    "KIND: Forward induction at k={}: {}",
                    k,
                    match &forward_result {
                        IncrementalCheckResult::Unsat => "UNSAT",
                        IncrementalCheckResult::Sat(_) => "SAT",
                        IncrementalCheckResult::Unknown => "UNKNOWN",
                    }
                );
            }
            if matches!(forward_result, IncrementalCheckResult::Unsat) && all_base_cases_unsat {
                if self.config.total_timeout <= std::time::Duration::from_secs(8) && k > 3 {
                    // For high k on short probes, skip cross-check — not enough
                    // budget to verify deep induction formulas reliably.
                    if self.config.base.verbose {
                        safe_eprintln!(
                            "KIND: Forward induction at k={} on short probe; returning Unknown to fallback",
                            k
                        );
                    }
                    return self.finish_with_result_trace(k, KindResult::Unknown);
                }

                // #6789 diagnostic: cross-check the induction formula with a fresh solver.
                if self.config.base.verbose {
                    self.diagnose_induction_at_k(&ts, k, start_time);
                }
                // Forward induction UNSAT + all base cases UNSAT = system is SAFE.
                // Use raw query to avoid free aux vars in the negation.
                let inv = ChcExpr::not(ts.query_raw().clone());
                let final_inv = self.strengthen_to_1_inductive(&inv, k, &ts, start_time);
                if self.verify_invariant_init_query(&ts, &final_inv, start_time) {
                    if self.config.base.verbose {
                        safe_eprintln!("KIND: Forward induction succeeded at k = {}", k);
                    }
                    return self.finish_with_result_trace(k, self.make_safe(final_inv));
                }
                // Invariant extraction failed — verify the induction formula
                // with a fresh solver before deferring Safe (#6789).
                // If the fresh check also says UNSAT, the induction is genuine
                // (the invariant just failed k-to-1 conversion). If the fresh
                // check says SAT, the incremental solver had a false-UNSAT and
                // we must NOT accept this as a safety proof.
                if deferred_safe_k.is_none() {
                    match self.verify_forward_induction_fresh(&ts, k, start_time) {
                        FreshCheckOutcome::ConfirmedUnsat => {
                            if self.config.base.verbose {
                                safe_eprintln!(
                                    "KIND: Forward induction at k={} verified fresh, validating with extended BMC",
                                    k
                                );
                            }
                            deferred_safe_k = Some(k);
                            deferred_safe_is_forward = true;
                        }
                        FreshCheckOutcome::CounterexampleSat => {
                            if self.config.base.verbose {
                                safe_eprintln!(
                                    "KIND: Forward induction at k={} rejected by fresh cross-check (false-UNSAT)",
                                    k
                                );
                            }
                            if self.config.total_timeout <= std::time::Duration::from_secs(8) {
                                if self.config.base.verbose {
                                    safe_eprintln!(
                                        "KIND: Forward induction at k={} false-UNSAT on short probe; returning Unknown to fallback",
                                        k
                                    );
                                }
                                return self.finish_with_result_trace(k, KindResult::Unknown);
                            }
                        }
                        FreshCheckOutcome::BudgetUnknown { timeout } => {
                            // UNKNOWN is not proof. Keep searching for a concrete
                            // base-case counterexample or a fresh UNSAT
                            // cross-check; otherwise fail closed to fallback.
                            if self.config.base.verbose {
                                safe_eprintln!(
                                    "KIND: Forward induction at k={} fresh cross-check UNKNOWN \
                                     (timeout={timeout:?}); continuing without deferred Safe",
                                    k
                                );
                            }
                        }
                    }
                }
            } else if matches!(forward_result, IncrementalCheckResult::Unsat)
                && self.config.base.verbose
            {
                safe_eprintln!(
                    "KIND: Forward induction holds at k = {} but base case incomplete",
                    k
                );
            }

            // === Backward induction ===
            // Init(x0) ∧ Tr(x0,x1) ∧ ¬Init(x1) ∧ ... ∧ Tr(xk,x{k+1}) ∧ ¬Init(x{k+1})
            // All constraints are permanent (cumulative). No temporary assumptions.
            self.trace_phase.set("backward");
            self.kind_trace_step_at(k, "Running", Some("CheckBackwardInduction"));

            bwd_ctx.assert_permanent(&ts.transition_at(k), &mut smt);
            bwd_ctx.assert_permanent(&ts.neg_init_at(k + 1), &mut smt);

            let remaining = self
                .config
                .total_timeout
                .saturating_sub(start_time.elapsed());
            if remaining.is_zero() {
                if deferred_safe_k.is_some() {
                    if self.config.base.verbose {
                        safe_eprintln!(
                            "KIND: Timeout before backward induction k={}, breaking to deferred acceptance",
                            k
                        );
                    }
                    break;
                }
                if self.config.base.verbose {
                    safe_eprintln!(
                        "KIND: Total timeout exceeded before backward induction k = {}",
                        k
                    );
                }
                return self.finish_with_result_trace(k, KindResult::Unknown);
            }
            let backward_timeout = remaining.min(self.config.query_timeout);

            let backward_result =
                match bwd_ctx.check_sat_incremental(&[], &mut smt, Some(backward_timeout)) {
                    IncrementalCheckResult::Unknown => {
                        let fresh_timeout = self.query_timeout_for_run(start_time);
                        if fresh_timeout.is_zero() {
                            IncrementalCheckResult::Unknown
                        } else {
                            bwd_ctx.check_sat_fresh_query(&[], &smt, Some(fresh_timeout))
                        }
                    }
                    other => other,
                };

            if self.config.base.verbose {
                safe_eprintln!(
                    "KIND: Backward induction at k={}: {}",
                    k,
                    match &backward_result {
                        IncrementalCheckResult::Unsat => "UNSAT",
                        IncrementalCheckResult::Sat(_) => "SAT",
                        IncrementalCheckResult::Unknown => "UNKNOWN",
                    }
                );
            }
            if matches!(backward_result, IncrementalCheckResult::Unsat) && all_base_cases_unsat {
                if self.config.total_timeout <= std::time::Duration::from_secs(8) && k > 3 {
                    // For high k on short probes, skip cross-check — not enough
                    // budget to verify deep induction formulas reliably.
                    if self.config.base.verbose {
                        safe_eprintln!(
                            "KIND: Backward induction at k={} on short probe; returning Unknown to fallback",
                            k
                        );
                    }
                    return self.finish_with_result_trace(k, KindResult::Unknown);
                }

                // #6789 diagnostic: if we haven't already diagnosed forward induction,
                // diagnose the backward path.
                if self.config.base.verbose && deferred_safe_k.is_none() {
                    safe_eprintln!(
                        "KIND DIAG: backward induction UNSAT at k={}, running cross-check",
                        k
                    );
                    self.diagnose_induction_at_k(&ts, k, start_time);
                }
                // Backward induction UNSAT + all base cases UNSAT = system is SAFE.
                // Now try to extract a nice 1-inductive invariant for the witness.
                //
                // Golem Kind.cc:141-147: reverse system, convert ¬Init on reversed, negate.
                // Use raw query (pre-mod-elimination) for the negation to avoid free
                // auxiliary variables. See TransitionSystem::init_raw doc.
                let reversed_ts = ts.reverse();
                let neg_reversed_query = ChcExpr::not(reversed_ts.query_raw().clone());
                let converted = self.strengthen_to_1_inductive(
                    &neg_reversed_query,
                    k,
                    &reversed_ts,
                    start_time,
                );
                let final_inv = ChcExpr::not(converted);
                if self.verify_invariant_init_query(&ts, &final_inv, start_time) {
                    if self.config.base.verbose {
                        safe_eprintln!("KIND: Backward induction succeeded at k = {}", k);
                    }
                    return self.finish_with_result_trace(k, self.make_safe(final_inv));
                }
                // Invariant extraction failed — verify the backward induction
                // formula with a fresh solver before deferring Safe (#6789).
                if deferred_safe_k.is_none() {
                    match self.verify_backward_induction_fresh(&ts, k, start_time) {
                        FreshCheckOutcome::ConfirmedUnsat => {
                            if self.config.base.verbose {
                                safe_eprintln!(
                                    "KIND: Backward induction at k={} verified fresh, validating with extended BMC",
                                    k
                                );
                            }
                            deferred_safe_k = Some(k);
                        }
                        FreshCheckOutcome::CounterexampleSat => {
                            if self.config.base.verbose {
                                safe_eprintln!(
                                    "KIND: Backward induction at k={} rejected by fresh cross-check (false-UNSAT)",
                                    k
                                );
                            }
                            if self.config.total_timeout <= std::time::Duration::from_secs(8) {
                                if self.config.base.verbose {
                                    safe_eprintln!(
                                        "KIND: Backward induction at k={} false-UNSAT on short probe; returning Unknown to fallback",
                                        k
                                    );
                                }
                                return self.finish_with_result_trace(k, KindResult::Unknown);
                            }
                        }
                        FreshCheckOutcome::BudgetUnknown { timeout } => {
                            // UNKNOWN is not proof. Keep searching for a concrete
                            // base-case counterexample or a fresh UNSAT
                            // cross-check; otherwise fail closed to fallback.
                            if self.config.base.verbose {
                                safe_eprintln!(
                                    "KIND: Backward induction at k={} fresh cross-check UNKNOWN \
                                     (timeout={timeout:?}); continuing without deferred Safe",
                                    k
                                );
                            }
                        }
                    }
                }
            } else if matches!(backward_result, IncrementalCheckResult::Unsat)
                && self.config.base.verbose
            {
                safe_eprintln!(
                    "KIND: Backward induction holds at k = {} but base case incomplete",
                    k
                );
            }
        }

        // If induction succeeded but invariant extraction failed, return Safe
        // only after all base cases to max_k validated UNSAT. This catches
        // SMT false-UNSAT bugs (e.g., accumulator_unsafe: forward induction
        // claims UNSAT at k=4 but base case SAT at k=11).
        //
        // DISABLED for BV problems (#5595): BV SMT queries can produce
        // false-UNSAT in backward/forward induction, and BMC to max_k is
        // insufficient for BV programs with long counterexample paths.
        // The ¬query invariant bypasses transition checking (validated with
        // Duration::ZERO), so false-UNSAT in induction → false-safe output.
        // Confirmed on nested9.c, s3_clnt_2_unsafe, svd-some-loop.c, svd4.c.
        if let Some(k) = deferred_safe_k {
            if self.problem.has_bv_sorts() {
                // BV soundness guard (#5595, #5877): BV SMT queries can produce
                // false-UNSAT in backward/forward induction. All 4 confirmed
                // false-Safe benchmarks (nested9.c, s3_clnt_2_unsafe, svd-some-loop.c,
                // svd4.c) had induction depth k >= 1.
                //
                // Strategy: require all_base_cases_unsat AND independent fresh
                // re-verification of the induction formula. The fresh SMT context
                // avoids incremental solver state corruption. If the fresh check
                // also returns UNSAT, the result is trustworthy.
                //
                // Partial-BMC acceptance is NOT allowed for BV (too risky with
                // long counterexample paths in BV programs).
                if all_base_cases_unsat
                    && self.verify_bv_induction_fresh(&ts, k, deferred_safe_is_forward, start_time)
                {
                    if self.config.base.verbose {
                        safe_eprintln!(
                            "KIND: BV deferred Safe at k={} accepted: all {} base cases UNSAT + \
                             fresh induction re-verified",
                            k,
                            self.config.max_k + 1,
                        );
                    }
                    let inv = ChcExpr::not(ts.query_raw().clone());
                    return self.finish_with_result_trace(self.config.max_k, self.make_safe(inv));
                }
                if self.config.base.verbose {
                    safe_eprintln!(
                        "KIND: BV deferred Safe from k={} rejected (all_bmc={}, fresh_verify=failed_or_skipped)",
                        k,
                        all_base_cases_unsat,
                    );
                }
            } else if self.problem.has_array_sorts() {
                // Array soundness guard (#8675, defense-in-depth): Array problems
                // are skipped at entry, but guard the deferred-safe path in case
                // a SingleLoop transformation or other encoding introduces array
                // sorts after the initial check. The SMT solver can produce
                // false-UNSAT on array formulas in both incremental and fresh
                // contexts, making all cross-checks unreliable.
                if self.config.base.verbose {
                    safe_eprintln!(
                        "KIND: Deferred Safe from k={} rejected for array problem (soundness guard #8675)",
                        k
                    );
                }
            } else if self.problem.has_real_sorts() {
                // LRA soundness guard (#5856): the CHC solver lacks Real value
                // representation in SmtValue/cube extraction. Kind's SMT-level
                // induction may produce false-UNSAT on complex LRA formulas,
                // yielding a spurious ¬query invariant that passes query-only
                // validation trivially. Reject deferred safe until Real model
                // support is implemented.
                if self.config.base.verbose {
                    safe_eprintln!(
                        "KIND: Deferred Safe from k={} rejected for LRA problem (soundness guard #5856)",
                        k
                    );
                }
            } else if all_base_cases_unsat {
                if self.config.base.verbose {
                    safe_eprintln!(
                        "KIND: Extended BMC validated to k={}, accepting deferred Safe from k={}",
                        self.config.max_k,
                        k
                    );
                }
                let inv = ChcExpr::not(ts.query_raw().clone());
                return self.finish_with_result_trace(self.config.max_k, self.make_safe(inv));
            } else if let Some(last_ok) = last_all_unsat_k {
                // Partial-BMC acceptance (#5653): accept if we verified enough
                // base cases beyond the induction depth, even if later ones timed out.
                let margin = MIN_BMC_MARGIN;
                if last_ok >= k + margin {
                    if self.config.base.verbose {
                        safe_eprintln!(
                            "KIND: Partial BMC: {} base cases verified (induction k={}, last verified k={}, margin={}), accepting deferred Safe",
                            last_ok + 1,
                            k,
                            last_ok,
                            margin,
                        );
                    }
                    let inv = ChcExpr::not(ts.query_raw().clone());
                    return self.finish_with_result_trace(self.config.max_k, self.make_safe(inv));
                } else if self.config.base.verbose {
                    safe_eprintln!(
                        "KIND: Extended BMC insufficient: only {} base cases verified UNSAT \
                         (need {} beyond induction k={}), returning Unknown",
                        last_ok + 1,
                        margin,
                        k,
                    );
                }
            } else if self.config.base.verbose {
                safe_eprintln!(
                    "KIND: Extended BMC found issue after deferred Safe at k={}, returning Unknown",
                    k
                );
            }
        }

        self.finish_with_result_trace(self.config.max_k, KindResult::Unknown)
    }

    /// Convert K-Induction result to PDR InvariantModel format
    pub fn to_model(&self, result: &KindResult) -> Option<InvariantModel> {
        match result {
            KindResult::Safe(model) => Some(model.clone()),
            _ => None,
        }
    }
}
