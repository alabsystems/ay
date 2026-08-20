// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Persistent executor wrapper for repeated array-heavy CHC queries.

#![cfg_attr(not(test), allow(dead_code))]

use super::context::SmtContext;
use super::executor_adapter::{
    accept_reparsed_sat_model, detect_logic, parse_model_into, quote_symbol, sort_to_smtlib,
};
use super::types::{SmtResult, SmtValue};
use crate::pdr::model::InvariantModel;
use crate::{ChcExpr, ChcSort, ChcVar};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};
use ay_dpll::Executor;
use ay_frontend::{Command, ParseError};
use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};
use std::time::Duration;

#[derive(Debug, thiserror::Error)]
enum PersistentExecutorError {
    #[error("parse error: {0}")]
    Parse(#[from] ParseError),
    #[error("executor error: {0}")]
    Execute(#[from] ay_dpll::ExecutorError),
    #[error("sort mismatch for persistent symbol {name}: {existing} vs {new}")]
    SortMismatch {
        name: String,
        existing: ChcSort,
        new: ChcSort,
    },
    #[error("check-sat produced no result")]
    MissingResult,
}

struct PersistentExecutorAdapter {
    exec: Executor,
    background: Option<ChcExpr>,
    background_hash: Option<u64>,
    logic: Option<String>,
    declared_vars: FxHashMap<String, ChcSort>,
    query_count: usize,
}

impl PersistentExecutorAdapter {
    fn new() -> Self {
        Self {
            exec: Executor::new(),
            background: None,
            background_hash: None,
            logic: None,
            declared_vars: FxHashMap::default(),
            query_count: 0,
        }
    }

    fn reset(&mut self) {
        *self = Self::new();
    }

    fn ensure_background(
        &mut self,
        background: &ChcExpr,
        logic: &str,
        timeout: Duration,
    ) -> Result<(), PersistentExecutorError> {
        let background_hash = expr_hash(background);
        if self.background_hash == Some(background_hash) && self.logic.as_deref() == Some(logic) {
            return Ok(());
        }

        self.reset();

        let namespace = format!("bg{background_hash}");
        let normalized = SmtContext::preprocess_incremental_assumption(background, &namespace);
        let vars = collect_unique_vars(std::slice::from_ref(&normalized));

        let mut script = String::new();
        script.push_str(&format!("(set-logic {logic})\n"));
        script.push_str("(set-option :produce-models true)\n");
        script.push_str(&format_timeout_option(timeout));
        append_var_declarations(&mut script, &vars);
        append_assertion(&mut script, &normalized);

        self.execute_script(&script)?;
        self.background = Some(background.clone());
        self.background_hash = Some(background_hash);
        self.logic = Some(logic.to_string());
        self.declared_vars = vars
            .into_iter()
            .map(|var| (var.name, var.sort))
            .collect::<FxHashMap<_, _>>();
        Ok(())
    }

    fn declare_missing_vars(&mut self, expr: &ChcExpr) -> Result<(), PersistentExecutorError> {
        let vars = collect_unique_vars(std::slice::from_ref(expr));
        let mut missing = Vec::new();

        for var in vars {
            if let Some(existing) = self.declared_vars.get(&var.name) {
                if existing != &var.sort {
                    return Err(PersistentExecutorError::SortMismatch {
                        name: var.name,
                        existing: existing.clone(),
                        new: var.sort,
                    });
                }
                continue;
            }
            missing.push(var);
        }

        if missing.is_empty() {
            return Ok(());
        }

        let mut script = String::new();
        append_var_declarations(&mut script, &missing);
        self.execute_script(&script)?;
        for var in missing {
            self.declared_vars.insert(var.name, var.sort);
        }
        Ok(())
    }

    fn execute_script(&mut self, script: &str) -> Result<(), PersistentExecutorError> {
        if script.trim().is_empty() {
            return Ok(());
        }
        let commands = ay_frontend::parse(script)?;
        self.exec.execute_all(&commands)?;
        Ok(())
    }
}

pub(crate) struct PersistentExecutorSmtContext {
    scratch: SmtContext,
    backend: PersistentExecutorAdapter,
    /// Inc-21 session dv preference: seeded by dv-poisoned routes
    /// (`prefer_dv_off_first`) or learned once a dv-off retry rescues a raw
    /// executor unknown (definitive sat/unsat after the pass-ON attempt
    /// failed). Subsequent eligible queries then run a SINGLE full-budget
    /// pass-OFF attempt, so a dv-poisoned workload — e.g. the car_all
    /// houdini consecution family where the inc-14 pass fires 929× and
    /// defeats the model search — stops burning call caps on doomed pass-ON
    /// attempts. Selecting the per-run option changes no verdict trust:
    /// every attempt runs the identical pipeline. Survives `reset_backend`
    /// deliberately (workload knowledge, not session state).
    dv_off_preferred: bool,
}

impl Default for PersistentExecutorSmtContext {
    fn default() -> Self {
        Self::new()
    }
}

impl PersistentExecutorSmtContext {
    pub(crate) fn new() -> Self {
        Self {
            scratch: SmtContext::new(),
            backend: PersistentExecutorAdapter::new(),
            dv_off_preferred: false,
        }
    }

    /// Whether this session currently prefers the dv-off first attempt
    /// (either seeded via `prefer_dv_off_first` or learned from a dv-off
    /// retry rescue). Callers can forward this as a first-attempt hint to
    /// sibling validators (e.g. the houdini final-validation
    /// `ay_says_unsat` calls on the same queries).
    pub(crate) fn dv_off_preferred(&self) -> bool {
        self.dv_off_preferred
    }

    /// Seed the session preference to dv-off-first (inc-21).
    ///
    /// Used by the adaptive houdini conjunctive prepass: its workload is
    /// SAT-direction-heavy (model-based candidate dropping over a large
    /// guarded-eq background — the exact inc-18 cliff shape) and the inc-14
    /// pass taxes every check (~15ms × ~550 queries on car_all, pushing the
    /// fixpoint past the route window: 14.2s dv-on vs 8.1s dv-off). Seeding
    /// off-first reproduces the proven `AY_EQ_DIFFVAR=0` behavior for this
    /// route: every check runs ONE full-budget pass-OFF attempt (see
    /// `check_query` — reserving a retry slice for the pass-ON mode starves
    /// borderline queries in tight call-cap loops). Pure per-run option
    /// selection; verdict trust unchanged.
    pub(crate) fn prefer_dv_off_first(&mut self) {
        self.dv_off_preferred = true;
    }

    pub(crate) fn ensure_background(&mut self, background: &ChcExpr, timeout: Duration) -> bool {
        let vars = collect_unique_vars(std::slice::from_ref(background));
        let logic = detect_logic(&vars, background);
        match self.backend.ensure_background(background, logic, timeout) {
            Ok(()) => true,
            Err(error) => {
                tracing::debug!("persistent executor background setup failed: {error}");
                self.reset_backend();
                false
            }
        }
    }

    pub(crate) fn check_query(
        &mut self,
        query_delta: &ChcExpr,
        propagated_model: &FxHashMap<String, SmtValue>,
        timeout: Duration,
    ) -> SmtResult {
        let Some(background) = self.backend.background.clone() else {
            return SmtResult::Unknown;
        };

        let namespace = format!("q{}", self.backend.query_count);
        let normalized_query =
            SmtContext::preprocess_incremental_assumption(query_delta, &namespace);
        let combined = ChcExpr::and(background.clone(), normalized_query.clone());
        let vars = collect_unique_vars(&[background.clone(), normalized_query.clone()]);
        let required_logic = detect_logic(&vars, &combined);

        if self.backend.logic.as_deref() != Some(required_logic) {
            if let Err(error) = self
                .backend
                .ensure_background(&background, required_logic, timeout)
            {
                tracing::debug!("persistent executor logic upgrade failed: {error}");
                self.reset_backend();
                return SmtResult::Unknown;
            }
        }

        if let Err(error) = self.backend.declare_missing_vars(&normalized_query) {
            tracing::debug!("persistent executor declaration failed: {error}");
            self.reset_backend();
            return SmtResult::Unknown;
        }

        // Inc-21: port of the inc-18 EqDiffVar SAT-direction retry
        // (`SmtContext::executor_fallback_with_dv_retry`,
        // smt/check_sat/mod.rs) to the persistent session. The inc-14
        // EqDiffVar pass fires unconditionally inside the executor and can
        // defeat the SAT-direction model search (attribution: the adaptive
        // houdini conjunctive prepass lost car_all_e7_188_e7_743 because
        // this context had no dv-off treatment — sat@26.7s with
        // AY_EQ_DIFFVAR=0 vs unknown@116s with the pass on).
        //
        // Two regimes, selected by the session preference:
        // - default (dv-on first): the inc-18 pattern — reserve
        //   `min(timeout/3, 1.5s)`, run the pass-ON attempt on the rest, and
        //   on a RAW executor unknown re-run ONCE with `:ay-eq-diffvar
        //   false` on the remaining budget. A definitive dv-off rescue flips
        //   the session preference to dv-off-first.
        // - dv-off preferred (seeded by the houdini route or learned): a
        //   SINGLE full-budget pass-OFF attempt — exactly the proven
        //   `AY_EQ_DIFFVAR=0` behavior. No reserve: shaving the budget
        //   starves borderline queries in tight call-cap loops (measured on
        //   car_all consecution sweeps: the 2/3 slice flips them to unknown
        //   and exhausts the route window).
        //
        // Eligibility: Int vars present (the pass only rewrites Int equality
        // atoms) and a budget big enough that no slice rounds down to
        // `:timeout 0` ("no timeout" per Z3 convention). Kill switches:
        // `AY_EXEC_DV_RETRY=0`, `AY_EQ_DIFFVAR=0` (both handled in
        // `dv_unknown_retry_enabled`; both force the plain single attempt).
        //
        // Soundness: every attempt runs the IDENTICAL push/assert/check/pop
        // pipeline — UNSAT carries the same trust as every persistent
        // executor verdict, and SAT models pass the same strict
        // `accept_reparsed_sat_model` validation against the ORIGINAL
        // background+query. No new answer construction.
        let dv_retry = super::executor_adapter::dv_unknown_retry_enabled()
            && super::check_sat::expr_mentions_int_var(&combined)
            && timeout >= Duration::from_millis(3);
        if dv_retry && self.dv_off_preferred {
            let (result, _) = self.check_query_attempt(
                &background,
                &normalized_query,
                propagated_model,
                timeout,
                true,
            );
            return result;
        }
        let reserve = if dv_retry {
            (timeout / 3).min(Duration::from_millis(1500))
        } else {
            Duration::ZERO
        };
        let attempt_start = ay_core::time::Instant::now();
        let (first, raw_unknown) = self.check_query_attempt(
            &background,
            &normalized_query,
            propagated_model,
            timeout.saturating_sub(reserve),
            false,
        );
        if !raw_unknown || reserve.is_zero() {
            return first;
        }
        // Retry budget: the leftover of the caller's window (>= the reserve
        // when the first attempt returned early), clamped to the thread SMT
        // deadline like the inc-18 site.
        let remaining = timeout.saturating_sub(attempt_start.elapsed());
        let retry_timeout = match crate::smt::clamp_timeout_to_smt_deadline(Some(remaining)) {
            Ok(Some(t)) => t,
            Ok(None) => remaining,
            Err(()) => return SmtResult::Unknown,
        };
        if retry_timeout < Duration::from_millis(1) {
            return SmtResult::Unknown;
        }
        tracing::debug!("persistent executor dv-off retry start timeout={retry_timeout:?}");
        let (retry, _) = self.check_query_attempt(
            &background,
            &normalized_query,
            propagated_model,
            retry_timeout,
            true,
        );
        // A definitive dv-off rescue flips the session preference (pure
        // attempt-ordering heuristic; no trust change).
        if !matches!(retry, SmtResult::Unknown) {
            self.dv_off_preferred = true;
        }
        retry
    }

    /// One push/assert/check-sat/pop attempt against the persistent session.
    ///
    /// Returns the result plus a `raw_unknown` flag that is true ONLY when
    /// check-sat itself reported "unknown" (the dv-off retry trigger). The
    /// model-rejection and error paths return Unknown with the flag false so
    /// the retry never fires on a failure the pass cannot have caused.
    ///
    /// `disable_eq_diffvar` (inc-21, ported from inc-18): `set-option` is
    /// SESSION-scoped on the persistent executor (not undone by pop), so the
    /// opt-out is written just before this attempt and restored to `true`
    /// right after the pop — later queries on the same session run with the
    /// pass enabled again (asserted by
    /// `test_persistent_dv_off_attempt_isolated_per_query`). Restoring writes
    /// `true` rather than unsetting (SMT-LIB has no unset); the executor's
    /// per-run gate only honors an explicit `false`, and the `AY_EQ_DIFFVAR=0`
    /// master env switch still wins over the option. Every error path resets
    /// the backend (fresh executor, options cleared), so the opt-out cannot
    /// leak there either.
    fn check_query_attempt(
        &mut self,
        background: &ChcExpr,
        normalized_query: &ChcExpr,
        propagated_model: &FxHashMap<String, SmtValue>,
        timeout: Duration,
        disable_eq_diffvar: bool,
    ) -> (SmtResult, bool) {
        if let Err(error) = self.backend.execute_script(&format_timeout_option(timeout)) {
            tracing::debug!("persistent executor timeout update failed: {error}");
            self.reset_backend();
            return (SmtResult::Unknown, false);
        }

        if disable_eq_diffvar {
            if let Err(error) = self
                .backend
                .execute_script("(set-option :ay-eq-diffvar false)\n")
            {
                tracing::debug!("persistent executor dv-off option failed: {error}");
                self.reset_backend();
                return (SmtResult::Unknown, false);
            }
        }

        let mut pushed = false;
        let mut raw_unknown = false;
        let result = (|| -> Result<SmtResult, PersistentExecutorError> {
            self.backend.exec.execute(&Command::Push(1))?;
            pushed = true;

            let mut query_script = String::new();
            append_assertion(&mut query_script, normalized_query);
            self.backend.execute_script(&query_script)?;

            // #cert-accounting item 3: this verdict is consumed only as PDR
            // search guidance; the portfolio's published `Safe` claim is
            // re-derived from scratch by `verify_model_impl` (and, where run,
            // by the checked-replay pass) and reads nothing about how this
            // sub-query was certified. The declaration changes no gate and no
            // verdict today — it attributes this channel's certification cost
            // in `ay_dpll::CertificationAccounting`.
            let status = self
                .backend
                .exec
                .execute(&Command::CheckSat)?
                // ROLE: Published (fail-safe), declaration WITHDRAWN.
                //
                // This called `execute_internal_lemma`, justified by "the
                // portfolio's published Safe claim is re-derived from scratch by
                // verify_model_impl". That justification is CIRCULAR:
                // verify_model_impl's own queries reach the executor through the
                // same SmtContext lane, so the re-derivation cannot vouch for the
                // channel it is itself running on. On that path a false UNSAT
                // becomes a false Safe.
                //
                // The declaration was harmless while the role was read only by
                // accounting. It stopped being harmless when
                // `active_unsat_query_requires_strict_proof` began consulting the
                // role (#cert-item-3): an InternalLemma declaration here now
                // exempts the query from the translated-proof requirement. An
                // exemption may only rest on an audit that establishes this
                // channel's verdict never becomes a published claim — which does
                // not exist. An audit was subsequently completed -- see below.
                //
                // ITEM-2 MEASUREMENT (why the audit passed and the change was still
                // not taken): declaring this channel InternalLemma was tried and
                // measured on dillig12_m. It captured 60 of 1142 decisions and 6 of
                // 1019 mints, worth 0.1ms. The other 1013 mints arrive through
                // SmtContext -- the verifier's OWN lane, which must stay Published.
                // So the "1000 internal lemmas to compose" the plan assumed do not
                // exist: the bulk of certification cost is on the channel that
                // certifies the published claim, and cannot be routed off it. An
                // exemption carries real soundness surface; 0.1ms does not pay for
                // it. Published stands on the measurement, not just on the missing
                // audit -- the audit now exists and passes.
                .ok_or(PersistentExecutorError::MissingResult)?;

            match status.as_str() {
                "sat" => {
                    let model_output = self
                        .backend
                        .exec
                        .execute(&Command::GetModel)?
                        .unwrap_or_default();
                    let mut model = propagated_model.clone();
                    parse_model_into(&mut model, &model_output, &FxHashSet::default());
                    let validation_exprs = [background, normalized_query];
                    Ok(
                        if let Some(model) = accept_reparsed_sat_model(
                            &validation_exprs,
                            model,
                            "persistent executor",
                        ) {
                            SmtResult::Sat(model)
                        } else {
                            SmtResult::Unknown
                        },
                    )
                }
                "unsat" => Ok(SmtResult::Unsat),
                "unknown" => {
                    raw_unknown = true;
                    Ok(SmtResult::Unknown)
                }
                other => {
                    tracing::warn!(
                        "persistent executor: unexpected result string {other:?}; treating as Unknown"
                    );
                    Ok(SmtResult::Unknown)
                }
            }
        })();

        if pushed {
            match self.backend.exec.execute(&Command::Pop(1)) {
                Ok(None) => {}
                Ok(Some(_)) => {
                    tracing::debug!("persistent executor pop produced unexpected output");
                    self.reset_backend();
                    return (SmtResult::Unknown, false);
                }
                Err(error) => {
                    tracing::debug!("persistent executor pop failed: {error}");
                    self.reset_backend();
                    return (SmtResult::Unknown, false);
                }
            }
        }

        // Restore the session default after a dv-off attempt (isolation:
        // later queries on this session must run with the pass enabled).
        if disable_eq_diffvar {
            if let Err(error) = self
                .backend
                .execute_script("(set-option :ay-eq-diffvar true)\n")
            {
                tracing::debug!("persistent executor dv-off restore failed: {error}");
                self.reset_backend();
                return (SmtResult::Unknown, false);
            }
        }

        match result {
            Ok(result) => {
                self.backend.query_count += 1;
                (result, raw_unknown)
            }
            Err(error) => {
                tracing::debug!("persistent executor query failed: {error}");
                self.reset_backend();
                (SmtResult::Unknown, false)
            }
        }
    }

    pub(crate) fn reset_backend(&mut self) {
        self.scratch.reset();
        self.backend.reset();
    }

    #[cfg(test)]
    pub(crate) fn query_count(&self) -> usize {
        self.backend.query_count
    }
}

fn expr_hash(expr: &ChcExpr) -> u64 {
    let mut hasher = DefaultHasher::new();
    expr.hash(&mut hasher);
    hasher.finish()
}

fn collect_unique_vars(exprs: &[ChcExpr]) -> Vec<ChcVar> {
    let mut seen = FxHashSet::default();
    let mut vars = Vec::new();

    for expr in exprs {
        for var in expr.vars() {
            if seen.insert(var.clone()) {
                vars.push(var);
            }
        }
    }

    vars
}

fn format_timeout_option(timeout: Duration) -> String {
    if timeout.is_zero() {
        return String::new();
    }
    let timeout_ms = timeout.as_millis().min(u128::from(u64::MAX));
    format!("(set-option :timeout {timeout_ms})\n")
}

fn append_var_declarations(script: &mut String, vars: &[ChcVar]) {
    for var in vars {
        let sort_str = sort_to_smtlib(&var.sort);
        let name = quote_symbol(&var.name);
        script.push_str(&format!("(declare-const {name} {sort_str})\n"));
    }
}

fn append_assertion(script: &mut String, expr: &ChcExpr) {
    // Assert top-level conjuncts individually for better theory axiom
    // generation (same pattern as `PdrExecutorBackend::check_sat`; #7984).
    for conjunct in expr.conjuncts() {
        let expr_str = InvariantModel::expr_to_smtlib(conjunct);
        script.push_str(&format!("(assert {expr_str})\n"));
    }
}

#[cfg(test)]
#[path = "persistent_tests.rs"]
mod tests;
