// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! PDKIND push operation and verification helpers.

use super::reachability::{ReachabilityChecker, ReachabilityResult};
use super::types::*;
use super::PdkindSolver;
use crate::bmc::{BmcConfig, BmcSolver};
use crate::engine_utils::check_sat_with_timeout;
use crate::smt::{
    IncrementalCheckResult, IncrementalQueryContext, SmtContext, SmtResult, SmtValue,
};
use crate::transition_system::TransitionSystem;
use crate::{ChcExpr, ChcSort, ChcVar};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};
use std::collections::VecDeque;

impl PdkindSolver {
    pub(super) fn push(
        &self,
        ts: &TransitionSystem,
        iframe: &mut InductionFrame,
        n: usize,
        k: usize,
        _incremental_mode: &IncrementalMode,
        reachability: &mut ReachabilityChecker,
        obligation_timeout_secs: u64,
    ) -> PushResult {
        // Per-check timeout (#4823) and total budget for reachability.
        // #421: this deadline is PER push() call, and push() runs up to
        // max_iterations times, so the per-push budget must scale with the
        // configured per-obligation budget — otherwise a small config (e.g.
        // soundness tests with per_obligation_timeout_secs=1) still gets a 20s
        // floor per push × max_iterations (5) = 100s > the 60s test timeout.
        // Scale as 6× the per-obligation budget with only a tiny floor; this
        // leaves the default config (5s → 30s) unchanged while honoring small
        // budgets. SOUND: a tighter reachability deadline only yields Unknown
        // sooner, never a wrong verdict.
        reachability.set_smt_timeout(std::time::Duration::from_secs(obligation_timeout_secs));
        let reachability_budget_secs = (obligation_timeout_secs * 6).max(2);
        reachability.set_deadline(
            ay_core::time::Instant::now()
                + std::time::Duration::from_secs(reachability_budget_secs),
        );
        let mut queue: VecDeque<IFrameElement> = iframe.iter().cloned().collect();
        let mut new_iframe = InductionFrame::default();
        let mut np = n + k;
        let mut invalid = false;
        let mut steps_to_cex = 0usize;
        let mut unknown = false;
        let mut kinduction_unknown = false;
        let mut kinduction_proved: usize = 0;
        let obligation_timeout = Some(std::time::Duration::from_secs(obligation_timeout_secs));
        // Build k-transition (fixed background for all obligations).
        let k_transition = ts.k_transition(k);
        // When incremental_mode is FreshOnly or Degraded, route through the
        // existing FreshOnly plan so each obligation solves from
        // background_exprs + assumptions (#8161, #6692).
        let mut inc_smt = SmtContext::new();
        let mut inc_ctx = {
            let mut ctx = IncrementalQueryContext::new();
            ctx.assert_background(&k_transition, &mut inc_smt);

            // Pre-register state variables as tautologies (#2690).
            for var in ts.state_vars() {
                for t in 0..=k {
                    let versioned = TransitionSystem::version_var(var, t);
                    let var_expr = ChcExpr::var(versioned);
                    // Keep the variable live in the SMT encoding with a
                    // sort-neutral tautology. Arithmetic self-comparisons
                    // panic on Array state vars in CHC portfolios.
                    let tautology = ChcExpr::eq(var_expr.clone(), var_expr);
                    ctx.assert_background(&tautology, &mut inc_smt);
                }
            }

            // Pre-register extra vars from iframe lemmas/counterexamples (#2690).
            {
                let mut extra_vars: FxHashSet<ChcVar> = FxHashSet::default();
                let state_var_names: FxHashSet<String> =
                    ts.state_vars().iter().map(|v| v.name.clone()).collect();
                for elem in iframe.iter() {
                    for v in elem.lemma.vars() {
                        if !state_var_names.contains(&v.name) {
                            extra_vars.insert(v);
                        }
                    }
                    for v in elem.counter_example.formula.vars() {
                        if !state_var_names.contains(&v.name) {
                            extra_vars.insert(v);
                        }
                    }
                }
                for var in &extra_vars {
                    for t in 0..=k {
                        let versioned = TransitionSystem::version_var(var, t);
                        let var_expr = ChcExpr::var(versioned);
                        let tautology = ChcExpr::eq(var_expr.clone(), var_expr);
                        ctx.assert_background(&tautology, &mut inc_smt);
                    }
                }
            }

            ctx.finalize_background(&inc_smt);
            ctx
        };

        // Cache the frame abstraction: only rebuild when iframe changes.
        // build_frame_abstraction iterates all elements × k timesteps, which is
        // O(|iframe| * k) per obligation. Caching avoids redundant reconstruction.
        let mut cached_iframe_abs: Option<ChcExpr> = None;
        let mut cached_iframe_size = 0usize;

        while !invalid && !queue.is_empty() {
            // Check for cooperative cancellation or memory budget (#2769)
            if self.config.base.is_cancelled() {
                if self.config.base.verbose {
                    safe_eprintln!("PDKIND: Cancelled during push()");
                }
                return PushResult {
                    i_frame: iframe.clone(),
                    new_i_frame: iframe.clone(),
                    n: np,
                    is_invalid: false,
                    steps_to_cex: 0,
                    is_unknown: true,
                    has_unknown_kinduction: false,
                    kinduction_all_timed_out: false,
                };
            }

            let obligation = queue.pop_front().expect("loop guard checked non-empty");

            // Build frame abstraction (conjunction of all lemmas).
            // Rebuild only when iframe has changed (size differs from cached).
            let iframe_abs = if cached_iframe_abs.is_some() && iframe.len() == cached_iframe_size {
                cached_iframe_abs.clone().expect("checked is_some above")
            } else {
                let abs = self.build_frame_abstraction(iframe, ts, k);
                cached_iframe_size = iframe.len();
                cached_iframe_abs = Some(abs.clone());
                abs
            };

            // Check: iframe_abs ∧ Trans^k ∧ ¬lemma' SAT?
            let neg_lemma_versioned =
                ts.send_through_time(&ChcExpr::not(obligation.lemma.clone()), k);

            // K-induction check (incremental, k_transition is background).
            let kinduction_result = {
                let assumptions = vec![iframe_abs.clone(), neg_lemma_versioned.clone()];
                inc_ctx.push();
                let result =
                    inc_ctx.check_sat_incremental(&assumptions, &mut inc_smt, obligation_timeout);
                inc_ctx.pop();
                result
            };

            let induction_failure_model = match kinduction_result {
                IncrementalCheckResult::Unsat => {
                    kinduction_proved += 1;
                    new_iframe.insert(obligation);
                    continue;
                }
                IncrementalCheckResult::Unknown => {
                    kinduction_unknown = true;
                    new_iframe.insert(obligation);
                    // Early exit if all obligations timeout (#4823).
                    if kinduction_proved == 0 {
                        #[allow(clippy::iter_with_drain)]
                        for remaining in queue.drain(..) {
                            new_iframe.insert(remaining);
                        }
                        break;
                    }
                    continue;
                }
                IncrementalCheckResult::Sat(model) => {
                    debug_assert!(
                        !model.is_empty(),
                        "BUG: k-induction SAT model is empty at k={k}, n={n}",
                    );
                    model
                }
            };

            // Check if counterexample is reachable
            let cex_versioned = ts.send_through_time(&obligation.counter_example.formula, k);

            let (cex_is_sat, cex_model_opt) = {
                let cex_assumptions = vec![iframe_abs.clone(), cex_versioned.clone()];
                inc_ctx.push();
                let cex_inc = inc_ctx.check_sat_incremental(
                    &cex_assumptions,
                    &mut inc_smt,
                    obligation_timeout,
                );
                inc_ctx.pop();
                match cex_inc {
                    IncrementalCheckResult::Sat(model) => (true, Some(model)),
                    // Trust incremental UNSAT here. If it's a false UNSAT (#2690),
                    // the frame will be incorrectly stabilized, but
                    // validate_inductive_invariant() catches that at frame-stable
                    // level and retries with non-incremental solving.
                    IncrementalCheckResult::Unsat => (false, None),
                    IncrementalCheckResult::Unknown => {
                        unknown = true;
                        break;
                    }
                }
            };

            if let Some(cex_model) = cex_model_opt.filter(|_| cex_is_sat) {
                // SOUNDNESS FIX (#421): generalize with model-based fallback (#4823).
                let g_cex_formula = Self::generalize_with_fallback(
                    reachability,
                    &cex_model,
                    &k_transition,
                    &cex_versioned,
                    ts,
                );
                debug_assert!(
                    g_cex_formula != ChcExpr::Bool(false),
                    "BUG: generalize() produced Bool(false) for CEX at k={k}, n={n}",
                );
                if g_cex_formula == ChcExpr::Bool(true) {
                    new_iframe.insert(obligation);
                    continue;
                }

                let g_cex = CounterExample {
                    formula: g_cex_formula.clone(),
                    num_of_steps: obligation.counter_example.num_of_steps + k,
                };

                // Check reachability from init
                let from_n = n.saturating_sub(k.saturating_sub(1));
                match reachability.check_reachability(from_n, n, &g_cex.formula) {
                    ReachabilityResult::Reachable { steps } => {
                        invalid = true;
                        steps_to_cex = g_cex.num_of_steps + steps;
                    }
                    ReachabilityResult::Unreachable { explanation } => {
                        // Add new obligation to block g_cex
                        let new_obligation = IFrameElement {
                            lemma: explanation,
                            counter_example: g_cex,
                        };
                        iframe.insert(new_obligation.clone());
                        cached_iframe_abs = None; // iframe changed
                        queue.push_back(new_obligation);
                        queue.push_back(obligation);
                    }
                    ReachabilityResult::Unknown => {
                        unknown = true;
                        break;
                    }
                }
            } else {
                // CTI case: SOUNDNESS FIX (#421) with model-based fallback (#4823).
                let g_cti = Self::generalize_with_fallback(
                    reachability,
                    &induction_failure_model,
                    &k_transition,
                    &neg_lemma_versioned,
                    ts,
                );
                debug_assert!(
                    g_cti != ChcExpr::Bool(false),
                    "BUG: generalize() produced Bool(false) for CTI at k={k}, n={n}",
                );
                if g_cti == ChcExpr::Bool(true) {
                    new_iframe.insert(obligation);
                    continue;
                }

                let from_n = n.saturating_sub(k.saturating_sub(1));
                match reachability.check_reachability(from_n, n, &g_cti) {
                    ReachabilityResult::Reachable { steps } => {
                        // Second reachability check: when is not(lemma) reachable?
                        // Port from Golem PDKind.cc:349-355 for tighter np bound.
                        let not_lemma = ChcExpr::not(obligation.lemma.clone());
                        match reachability.check_reachability(n + 1, steps + k, &not_lemma) {
                            ReachabilityResult::Reachable { steps: real_steps } => {
                                np = np.min(real_steps);
                            }
                            _ => {
                                np = np.min(steps + k);
                            }
                        }
                        let new_obligation = IFrameElement {
                            lemma: ChcExpr::not(obligation.counter_example.formula.clone()),
                            counter_example: obligation.counter_example.clone(),
                        };
                        iframe.insert(new_obligation.clone());
                        cached_iframe_abs = None; // iframe changed
                        new_iframe.insert(new_obligation);
                    }
                    ReachabilityResult::Unreachable { explanation } => {
                        // Strengthen lemma
                        let strengthened =
                            ChcExpr::and_all([obligation.lemma.clone(), explanation]);
                        let new_obligation = IFrameElement {
                            lemma: strengthened,
                            counter_example: obligation.counter_example.clone(),
                        };
                        iframe.insert(new_obligation.clone());
                        iframe.remove(&obligation);
                        cached_iframe_abs = None; // iframe changed (swap)
                        queue.push_back(new_obligation);
                    }
                    ReachabilityResult::Unknown => {
                        unknown = true;
                        break;
                    }
                }
            }
        }

        PushResult {
            i_frame: iframe.clone(),
            new_i_frame: new_iframe,
            n: np,
            is_invalid: invalid,
            steps_to_cex,
            is_unknown: unknown,
            has_unknown_kinduction: kinduction_unknown,
            kinduction_all_timed_out: kinduction_unknown && kinduction_proved == 0,
        }
    }

    /// Validate a stable frame: init ⇒ inv, inv ⇒ ¬query, and k-inductiveness (#2813).
    ///
    /// SOUNDNESS FIX (#6787): Uses the ay-dpll Executor path instead of SmtContext
    /// for verification checks. SmtContext::check_sat can produce false UNSAT on
    /// certain formula patterns (#5384), causing PDKIND to accept invalid invariants.
    /// The Executor path goes through SMT-LIB parsing and ay-dpll's DPLL(T) loop,
    /// which handles theory conflicts correctly.
    ///
    pub(super) fn verify_non_incremental_stable_invariant(
        &self,
        ts: &TransitionSystem,
        invariant: &ChcExpr,
        k: usize,
    ) -> bool {
        debug_assert!(
            *invariant != ChcExpr::Bool(true) && *invariant != ChcExpr::Bool(false),
            "BUG: trivial invariant {invariant:?} at k={k}",
        );
        let verbose = self.config.base.verbose;
        let mut ctx = SmtContext::new();

        // Check 0 (#6787): k-step non-vacuity — verify that the k-inductiveness
        // premise (inv@0 ∧ ... ∧ inv@(k-1) ∧ T^k) is satisfiable.
        //
        // A too-strong invariant (e.g., x=0 ∧ pc=0) passes k-inductiveness
        // vacuously because the premise is contradictory — the invariant
        // constraining consecutive states is incompatible with the transition
        // relation. The k-inductiveness formula `premise ∧ ¬inv@k` is trivially
        // UNSAT when the premise itself is UNSAT, regardless of whether ¬inv@k
        // contributes.
        //
        // For k=1, inv ∧ T may be SAT (one step is compatible), but for k≥2,
        // inv@0 ∧ inv@1 ∧ T can become UNSAT (the invariant pins values that
        // transitions must change). We check the full k-step premise.
        {
            let mut nv_conjuncts = Vec::with_capacity(2 * k);
            for i in 0..k {
                nv_conjuncts.push(ts.send_through_time(invariant, i));
            }
            nv_conjuncts.push(ts.k_transition(k));
            let nonvacuity = ChcExpr::and_all(nv_conjuncts);
            if ctx.check_sat(&nonvacuity).is_unsat() {
                if verbose {
                    safe_eprintln!(
                        "PDKIND: stable frame: REJECTED vacuously k-inductive invariant \
                         at k={k} — premise (inv^k ∧ T^k) is UNSAT (#6787)"
                    );
                }
                return false;
            }
        }

        // Check 1: init ⇒ inv  <=>  UNSAT(init ∧ ¬inv)
        ctx.reset();
        if !ctx
            .check_sat(&ChcExpr::and_all([
                ts.init.clone(),
                ChcExpr::not(invariant.clone()),
            ]))
            .is_unsat()
        {
            if verbose {
                safe_eprintln!("PDKIND: stable frame: init failed at k={k}");
            }
            return false;
        }

        // Check 2: inv ⇒ ¬query  <=>  UNSAT(inv ∧ query)
        ctx.reset();
        if !ctx
            .check_sat(&ChcExpr::and_all([invariant.clone(), ts.query.clone()]))
            .is_unsat()
        {
            if verbose {
                safe_eprintln!("PDKIND: stable frame: query failed at k={k}");
            }
            return false;
        }

        // Check 3 (#2813): k-step inductiveness
        // UNSAT(inv@0 ∧ ... ∧ inv@(k-1) ∧ T^k ∧ ¬inv@k)
        ctx.reset();
        let mut conjuncts = Vec::with_capacity(2 * k + 1);
        for i in 0..k {
            conjuncts.push(ts.send_through_time(invariant, i));
        }
        conjuncts.push(ts.k_transition(k));
        conjuncts.push(ChcExpr::not(ts.send_through_time(invariant, k)));
        if !ctx.check_sat(&ChcExpr::and_all(conjuncts)).is_unsat() {
            if verbose {
                safe_eprintln!("PDKIND: stable frame: k-inductiveness failed at k={k}");
            }
            return false;
        }

        if verbose {
            safe_eprintln!("PDKIND: k={k} invariant verified (init+query+k-inductive)");
        }
        true
    }

    /// Build the frame abstraction (conjunction of all lemmas) versioned for k steps
    fn build_frame_abstraction(
        &self,
        iframe: &InductionFrame,
        ts: &TransitionSystem,
        k: usize,
    ) -> ChcExpr {
        let mut components = Vec::new();

        for elem in iframe {
            for i in 0..k {
                components.push(ts.send_through_time(&elem.lemma, i));
            }
        }

        if components.is_empty() {
            ChcExpr::Bool(true)
        } else {
            ChcExpr::and_all(components)
        }
    }

    /// Extract k-inductive invariant from frame
    pub(super) fn get_invariant(&self, iframe: &InductionFrame) -> ChcExpr {
        let lemmas: Vec<ChcExpr> = iframe.iter().map(|e| e.lemma.clone()).collect();

        if lemmas.is_empty() {
            ChcExpr::Bool(true)
        } else {
            ChcExpr::and_all(lemmas)
        }
    }

    /// Check-sat with 10s timeout. SingleLoop multi-predicate problems need
    /// 3-5s for inductiveness checks (#2675).
    pub(super) fn check_sat_10s(query: &ChcExpr) -> SmtResult {
        check_sat_with_timeout(query, std::time::Duration::from_secs(10))
    }

    /// Validate counterexample via BMC: `init@0 ∧ Trans^steps ∧ query@steps`.
    /// SOUNDNESS GUARD (#4729): catches spurious reachability from MBP/incremental bugs.
    pub(super) fn validate_counterexample(ts: &TransitionSystem, steps: usize) -> bool {
        // Cap unrolling depth; deep CEXes are unlikely spurious from MBP issues.
        if steps > 50 {
            return false;
        }

        let mut conjuncts = Vec::with_capacity(steps + 2);
        conjuncts.push(ts.init_at(0));
        for i in 0..steps {
            conjuncts.push(ts.transition_at(i));
        }
        conjuncts.push(ts.query_at(steps));

        let formula = ChcExpr::and_all(conjuncts);
        let result = Self::check_sat_10s(&formula);
        result.is_sat()
    }

    /// SOUNDNESS GUARD (#6787): run the existing CHC BMC engine on the original
    /// problem before trusting a stable-frame proof.
    ///
    /// After PDKIND's internal verification passes, do a quick bounded model
    /// check to confirm no concrete counterexample exists within a bounded
    /// depth. Reuse `BmcSolver` instead of re-encoding formulas manually: the
    /// BMC engine already has regression coverage for multi-transition problems
    /// like `two_phase_unsafe` and extracts a usable depth when it succeeds.
    ///
    /// Returns the first bounded counterexample depth if one is found.
    pub(super) fn bmc_sanity_counterexample_depth(&self, max_depth: usize) -> Option<usize> {
        let config = BmcConfig::with_engine_config(max_depth, false, None);
        match BmcSolver::new(self.problem.clone(), config).solve() {
            crate::engine_result::ChcEngineResult::Unsafe(cex) => {
                Some(cex.steps.len().saturating_sub(1))
            }
            _ => None,
        }
    }

    /// Generalize model via MBP, falling back to model-based cube on Bool(true).
    /// SOUNDNESS: #421 (pass k-transition), #4729/#4823 (Bool(true) fallback).
    fn generalize_with_fallback(
        reachability: &mut ReachabilityChecker,
        model: &FxHashMap<String, SmtValue>,
        k_transition: &ChcExpr,
        target: &ChcExpr,
        ts: &TransitionSystem,
    ) -> ChcExpr {
        let mbp_result = reachability.generalize(model, k_transition, target);
        if mbp_result == ChcExpr::Bool(true) {
            Self::model_to_state_cube(model, ts)
        } else {
            mbp_result
        }
    }

    /// Extract step-0 state variable assignments from a model as a blocking cube (#4823).
    fn model_to_state_cube(model: &FxHashMap<String, SmtValue>, ts: &TransitionSystem) -> ChcExpr {
        let names = ts.state_var_names();
        let conjuncts: Vec<_> = model
            .iter()
            .filter(|(n, _)| names.contains(n.as_str()))
            .filter_map(|(n, v)| {
                let sort = match v {
                    SmtValue::Bool(_) => ChcSort::Bool,
                    SmtValue::Int(_) | SmtValue::BigInt(_) => ChcSort::Int,
                    SmtValue::Real(_) => ChcSort::Real,
                    SmtValue::BitVec(_, w) => ChcSort::BitVec(*w),
                    SmtValue::Opaque(_)
                    | SmtValue::ConstArray(_)
                    | SmtValue::ArrayMap { .. }
                    | SmtValue::Datatype(..) => return None,
                };
                let var = ChcExpr::var(ChcVar::new(n, sort));
                Some(match v {
                    SmtValue::Bool(true) => var,
                    SmtValue::Bool(false) => ChcExpr::not(var),
                    SmtValue::Int(i) => ChcExpr::eq(var, ChcExpr::int(*i)),
                    // Beyond-i128 witness: exact Horner encoding (never wraps).
                    SmtValue::BigInt(b) => {
                        ChcExpr::eq(var, ChcExpr::from_bigint(b.as_ref().clone()))
                    }
                    SmtValue::Real(r) => {
                        use num_traits::ToPrimitive;
                        let n = r.numer().to_i64().unwrap_or(0);
                        let d = r.denom().to_i64().unwrap_or(1);
                        ChcExpr::eq(var, ChcExpr::Real(n, d))
                    }
                    SmtValue::BitVec(bv, w) => ChcExpr::eq(var, ChcExpr::BitVec(*bv, *w)),
                    SmtValue::Opaque(_)
                    | SmtValue::ConstArray(_)
                    | SmtValue::ArrayMap { .. }
                    | SmtValue::Datatype(..) => return None,
                })
            })
            .collect();
        if conjuncts.is_empty() {
            ChcExpr::Bool(true)
        } else {
            ChcExpr::and_all(conjuncts)
        }
    }
}
