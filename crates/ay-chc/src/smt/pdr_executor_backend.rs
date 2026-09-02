// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Persistent executor backend for PDR queries (#7984).
//!
//! PDR makes hundreds of SMT queries per solve, each currently recreating
//! the LIA solver from scratch via `SmtContext::check_sat()`. This module
//! wraps `ay-dpll::Executor` with push/pop to maintain persistent theory
//! solver state across queries, eliminating redundant solver construction.
//!
//! Design follows the `PersistentExecutorSmtContext` pattern from
//! `persistent.rs` but simplified for PDR's query pattern: no separate
//! background/query split — each `check_sat` call pushes, asserts, solves,
//! and pops in one atomic scope.

use super::executor_adapter::{
    accept_reparsed_sat_model, build_uf_application_aliases_avoiding,
    collect_dt_declarations_for_expr, collect_uninterpreted_function_declarations, detect_logic,
    emit_declare_datatypes, emit_declare_uninterpreted_function, emit_uf_application_aliases,
    install_uf_application_alias_values, parse_model_into, quote_symbol, sort_to_smtlib,
    UfApplicationAliasEmissionError,
};
use super::types::SmtResult;
use crate::pdr::model::InvariantModel;
use crate::{ChcExpr, ChcSort, ChcVar};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};
use ay_dpll::Executor;
use ay_frontend::Command;
use std::panic::AssertUnwindSafe;
use std::time::Duration;

/// Error type for persistent executor operations.
#[derive(Debug, thiserror::Error)]
enum PdrBackendError {
    #[error("parse error: {0}")]
    Parse(#[from] ay_frontend::ParseError),
    #[error("executor error: {0}")]
    Execute(#[from] ay_dpll::ExecutorError),
    #[error("invalid uninterpreted-function declaration: {0}")]
    InvalidFunctionSignature(String),
    #[error("invalid datatype declaration: {0}")]
    InvalidDatatypeDeclaration(String),
    #[error("UF application alias emission failed: {0}")]
    UfAliasEmission(#[from] UfApplicationAliasEmissionError),
    #[error("check-sat produced no result")]
    MissingResult,
}

/// Persistent executor backend for PDR SMT queries.
///
/// Maintains a single `Executor` instance across queries, using push/pop
/// for query-scoped assertions. Declared variables persist across queries
/// (the executor keeps them in scope after pop). The logic is set once on
/// first use and upgraded if a query requires a richer logic.
///
/// Reference: Z3 Spacer uses persistent SMT solvers per predicate
/// (`reference/z3/src/muz/spacer/spacer_prop_solver.h`).
pub(crate) struct PdrExecutorBackend {
    exec: Executor,
    logic: Option<String>,
    declared_vars: FxHashMap<String, ChcSort>,
    /// Ordinary UF signatures already declared in the persistent session.
    declared_functions: FxHashMap<String, (ChcSort, Vec<ChcSort>)>,
    /// Monotonic source-name freshness for finite UF-application observations.
    uf_application_alias_counter: usize,
    query_count: usize,
    initialized: bool,
    /// Canonical signatures of datatypes already declared in the persistent
    /// session.  Remembering only names would silently accept a later
    /// same-name/different-definition typed query under the old definition.
    declared_datatypes: FxHashMap<String, String>,
    /// Constructor surface names used while decoding datatype model values.
    declared_datatype_constructors: FxHashSet<String>,
}

impl Default for PdrExecutorBackend {
    fn default() -> Self {
        Self::new()
    }
}

impl PdrExecutorBackend {
    /// Create a new, uninitialized backend.
    pub(crate) fn new() -> Self {
        Self {
            exec: Executor::new(),
            logic: None,
            declared_vars: FxHashMap::default(),
            declared_functions: FxHashMap::default(),
            uf_application_alias_counter: 0,
            query_count: 0,
            initialized: false,
            declared_datatypes: FxHashMap::default(),
            declared_datatype_constructors: FxHashSet::default(),
        }
    }

    /// Run a satisfiability check using the persistent executor.
    ///
    /// Collects free variables, initializes the executor if needed, declares
    /// new variables, then uses push/assert/check-sat/get-model/pop to scope
    /// the query. On any error, resets the backend and returns `SmtResult::Unknown`.
    pub(crate) fn check_sat(&mut self, expr: &ChcExpr, timeout: Duration) -> SmtResult {
        self.check_sat_with_dv_hint(expr, timeout, false)
    }

    /// `check_sat` with the inc-21 EqDiffVar retry and a first-attempt hint.
    ///
    /// Port of the inc-18 dv-off retry (see
    /// `SmtContext::executor_fallback_with_dv_retry` and
    /// `PersistentExecutorSmtContext::check_query`): the inc-14 EqDiffVar
    /// pass fires unconditionally inside the executor and can defeat the
    /// search in either direction (attribution: the car_all houdini
    /// final-validation query is z3-trivially UNSAT, dv-off proves it in
    /// ~2s, dv-on is unknown at 30s).
    ///
    /// Two regimes (mirroring the persistent context):
    /// - `dv_off_first == false` (default): the inc-18 pattern — reserve
    ///   `min(timeout/3, 1.5s)`, run the pass-ON attempt on the rest, and on
    ///   a RAW executor unknown for an Int-mentioning query retry ONCE with
    ///   `:ay-eq-diffvar false` on the remaining budget.
    /// - `dv_off_first == true`: a SINGLE full-budget pass-OFF attempt —
    ///   callers that already learned the workload is dv-poisoned (a
    ///   houdini session whose dv-off retry rescued a raw unknown, or the
    ///   seeded houdini route) forward that knowledge; shaving a reserve off
    ///   the known-good mode only starves tight budgets.
    ///
    /// Kill switches: `AY_EXEC_DV_RETRY=0`, `AY_EQ_DIFFVAR=0` (single plain
    /// attempt). Soundness: every attempt runs the IDENTICAL pipeline below
    /// — UNSAT carries the trust every backend verdict already carries, and
    /// SAT models pass the same strict `accept_reparsed_sat_model`
    /// validation against the ORIGINAL expression. No new answer
    /// construction.
    pub(crate) fn check_sat_with_dv_hint(
        &mut self,
        expr: &ChcExpr,
        timeout: Duration,
        dv_off_first: bool,
    ) -> SmtResult {
        // This admission must precede retry feature scans and every recursive
        // div/mod or variable preprocessing helper.  It is iterative and
        // aggregate-capped; an oversized typed term is not allowed to reach a
        // stack-growing or allocation-producing path.
        if let Err(reason) = collect_dt_declarations_for_expr(&[], expr) {
            tracing::debug!(
                "pdr_executor_backend: {reason}; returning Unknown before recursive preprocessing"
            );
            return SmtResult::Unknown;
        }
        // Use catch_unwind for panic safety. The error closure resets state.
        let result = std::panic::catch_unwind(AssertUnwindSafe(|| {
            self.check_sat_with_retry(expr, timeout, dv_off_first)
        }));
        match result {
            Ok(r) => r,
            Err(_) => {
                tracing::debug!("pdr_executor_backend: ay panic caught; resetting");
                self.reset();
                SmtResult::Unknown
            }
        }
    }

    /// Retry orchestration for `check_sat_with_dv_hint` (inc-21).
    fn check_sat_with_retry(
        &mut self,
        expr: &ChcExpr,
        timeout: Duration,
        dv_off_first: bool,
    ) -> SmtResult {
        let dv_retry = super::executor_adapter::dv_unknown_retry_enabled()
            && super::check_sat::expr_mentions_int_var(expr)
            && timeout >= Duration::from_millis(3);
        if dv_retry && dv_off_first {
            let (result, _) = self.check_sat_inner(expr, timeout, true);
            return result;
        }
        let reserve = if dv_retry {
            (timeout / 3).min(Duration::from_millis(1500))
        } else {
            Duration::ZERO
        };
        let attempt_start = ay_core::time::Instant::now();
        let (first, raw_unknown) =
            self.check_sat_inner(expr, timeout.saturating_sub(reserve), false);
        if !raw_unknown || reserve.is_zero() {
            return first;
        }
        let remaining = timeout.saturating_sub(attempt_start.elapsed());
        let retry_timeout = match crate::smt::clamp_timeout_to_smt_deadline(Some(remaining)) {
            Ok(Some(t)) => t,
            Ok(None) => remaining,
            Err(()) => return SmtResult::Unknown,
        };
        if retry_timeout < Duration::from_millis(1) {
            return SmtResult::Unknown;
        }
        tracing::debug!("pdr_executor_backend dv-off retry start timeout={retry_timeout:?}");
        let (retry, _) = self.check_sat_inner(expr, retry_timeout, true);
        retry
    }

    /// Reset the backend to a fresh state. Called on errors.
    pub(crate) fn reset(&mut self) {
        *self = Self::new();
    }

    /// Number of queries successfully processed.
    #[cfg(test)]
    pub(crate) fn query_count(&self) -> usize {
        self.query_count
    }

    /// Inner implementation of check_sat: one full attempt.
    ///
    /// Returns the result plus a `raw_unknown` flag that is true ONLY when
    /// check-sat itself reported "unknown" (the dv retry trigger); the
    /// model-rejection and error paths return Unknown with the flag false.
    ///
    /// `disable_eq_diffvar` (inc-21): `set-option` is SESSION-scoped (not
    /// undone by pop), so the opt-out is written before the attempt and
    /// restored to `true` right after the pop — later queries on a reused
    /// backend run with the pass enabled again. Error paths reset the
    /// backend (fresh executor, options cleared), so no leak there either.
    fn check_sat_inner(
        &mut self,
        expr: &ChcExpr,
        timeout: Duration,
        disable_eq_diffvar: bool,
    ) -> (SmtResult, bool) {
        // Step 0 (#A3): Axiomatize div/mod with constant divisors before
        // serialization — ay-dpll's AUFLIA/ALIA fragments reject raw integer
        // div/mod with "(unsupported arithmetic)". Equisatisfiable rewrite;
        // SAT models are still validated against the ORIGINAL expression.
        let mod_div_axiomatized = super::executor_adapter::axiomatize_mod_div_for_executor(expr);
        let solve_expr = mod_div_axiomatized.as_ref().unwrap_or(expr);

        let dt_decls = match collect_dt_declarations_for_expr(&[], solve_expr) {
            Ok(declarations) => declarations,
            Err(reason) => {
                tracing::debug!(
                    "pdr_executor_backend: {reason}; returning Unknown after bounded preprocessing"
                );
                return (SmtResult::Unknown, false);
            }
        };

        // Step 1: Collect free variables.
        let vars = solve_expr.vars();
        if vars.is_empty() {
            return (SmtResult::Unknown, false);
        }

        // Step 1b (refutation-oracle fix): a persistent session declares each
        // variable NAME exactly once and `declare_missing_vars` skips any name
        // already cached. CHC clauses independently scope their forall vars and
        // REUSE short names (A, B, ..., R1/S1/T1) with DIFFERENT sorts across
        // clauses — e.g. the s3_srvr transition rule types R1/S1/T1 as Real
        // while the fact/query clauses type them Bool. A name first declared as
        // Bool was therefore never re-declared as Real, so a later
        // real-arithmetic query ran against Bool-typed variables and the theory
        // solver returned `unknown (:reason-unknown incomplete)` — the exact
        // `body ∧ trans ∧ ¬I` refutation Unknown that stalls the DT-LRA learner
        // (and any push/pop caller mixing such clauses). When a name reappears
        // with a CONFLICTING sort the cached session is stale for this query:
        // reset so every variable is re-declared with its current sort. Sound —
        // reset only clears solver state; the query is then solved from scratch.
        let conflict = self.initialized
            && vars.iter().any(|v| {
                self.declared_vars
                    .get(&v.name)
                    .is_some_and(|s| *s != v.sort)
            });
        // Kill switch (default ON): AY_BACKEND_SORT_RESET=0 disables the reset,
        // restoring the pre-fix behavior for controlled before/after measurement.
        let reset_enabled = true; // B24: kill-switch env retired; reset stays on.
        if conflict && reset_enabled {
            tracing::debug!(
                "pdr_executor_backend: variable sort conflict across queries \
                 (persistent name/sort cache is stale); resetting session"
            );
            self.reset();
        }

        // Step 2: Detect required logic.
        let required_logic = detect_logic(&vars, solve_expr).to_string();

        // Step 3: Initialize or upgrade logic if needed.
        if !self.initialized {
            if let Err(e) = self.initialize(&required_logic, timeout) {
                tracing::debug!("pdr_executor_backend: init failed: {e}");
                self.reset();
                return (SmtResult::Unknown, false);
            }
        } else if self.logic.as_deref() != Some(&required_logic) {
            // Logic upgrade needed — reset and reinitialize.
            tracing::debug!(
                "pdr_executor_backend: logic upgrade {} -> {required_logic}",
                self.logic.as_deref().unwrap_or("none")
            );
            self.reset();
            if let Err(e) = self.initialize(&required_logic, timeout) {
                tracing::debug!("pdr_executor_backend: reinit failed: {e}");
                self.reset();
                return (SmtResult::Unknown, false);
            }
        }

        // Step 4: Declare datatype sorts, ordinary UFs, and new variables.
        if let Err(e) = self.declare_datatypes(&dt_decls) {
            tracing::debug!("pdr_executor_backend: dt declaration failed: {e}");
            self.reset();
            return (SmtResult::Unknown, false);
        }
        if let Err(e) = self.declare_missing_uninterpreted_functions(solve_expr) {
            tracing::debug!("pdr_executor_backend: UF declaration failed: {e}");
            self.reset();
            return (SmtResult::Unknown, false);
        }
        if let Err(e) = self.declare_missing_vars(&vars) {
            tracing::debug!("pdr_executor_backend: var declaration failed: {e}");
            self.reset();
            return (SmtResult::Unknown, false);
        }

        // Step 5: Update timeout and the per-attempt EqDiffVar opt-out.
        if let Err(e) = self.update_timeout(timeout) {
            tracing::debug!("pdr_executor_backend: timeout update failed: {e}");
            self.reset();
            return (SmtResult::Unknown, false);
        }
        if disable_eq_diffvar {
            if let Err(e) = self.set_eq_diffvar_option(false) {
                tracing::debug!("pdr_executor_backend: dv-off option failed: {e}");
                self.reset();
                return (SmtResult::Unknown, false);
            }
        }

        // Diagnostic (spike, #ite-lift): dump each query as a self-contained
        // SMT2 file BEFORE check-sat, so even a query that hangs is captured.
        // Gated behind --chc-pdr-dump=<dir>; no effect when unset. The directory is
        // read once and cached, so an unset switch costs nothing on the PDR hot
        // path (hundreds of queries per solve).
        static PDR_DUMP_DIR: std::sync::OnceLock<Option<String>> = std::sync::OnceLock::new();
        if let Some(dir) =
            PDR_DUMP_DIR.get_or_init(|| ay_core::misc_cli_flags().chc_pdr_dump.clone())
        {
            use std::sync::atomic::{AtomicUsize, Ordering};
            static PDR_DUMP_SEQ: AtomicUsize = AtomicUsize::new(0);
            let n = PDR_DUMP_SEQ.fetch_add(1, Ordering::Relaxed);
            let mut s = String::with_capacity(2048);
            s.push_str(&format!("(set-logic {required_logic})\n"));
            s.push_str("(set-option :produce-models true)\n");
            if let Ok(declarations) = emit_declare_datatypes(&dt_decls) {
                s.push_str(&declarations);
            }
            if let Ok(declarations) = collect_uninterpreted_function_declarations(solve_expr) {
                for declaration in &declarations {
                    s.push_str(&emit_declare_uninterpreted_function(declaration));
                }
            }
            for v in &vars {
                s.push_str(&format!(
                    "(declare-const {} {})\n",
                    quote_symbol(&v.name),
                    sort_to_smtlib(&v.sort)
                ));
            }
            let mut n_ite = 0usize;
            let mut n_block = 0usize;
            for c in solve_expr.conjuncts() {
                let cs = InvariantModel::expr_to_smtlib(c);
                if cs.contains("ite") {
                    n_ite += 1;
                }
                if cs.starts_with("(or") {
                    n_block += 1;
                }
                s.push_str(&format!("(assert {cs})\n"));
            }
            s.push_str("(check-sat)\n");
            let path = format!(
                "{dir}/pdr_{n:04}_c{}_ite{n_ite}_or{n_block}.smt2",
                solve_expr.conjuncts().len()
            );
            let _ = std::fs::write(&path, &s);
        }

        let declared_vars = &self.declared_vars;
        let declared_functions = &self.declared_functions;
        let alias_counter = &mut self.uf_application_alias_counter;
        let uf_application_aliases = match build_uf_application_aliases_avoiding(
            std::iter::once(solve_expr),
            alias_counter,
            declared_vars
                .keys()
                .chain(declared_functions.keys())
                .map(String::as_str),
        ) {
            Ok(aliases) => aliases,
            Err(error) => {
                tracing::debug!("pdr_executor_backend: UF application alias failed: {error}");
                return (SmtResult::Unknown, false);
            }
        };

        // Step 6: Push, alias finite UF applications, assert, check-sat,
        // get-model, pop.
        let mut pushed = false;
        let mut raw_unknown = false;
        let result = (|| -> Result<SmtResult, PdrBackendError> {
            self.exec.execute(&Command::Push(1))?;
            pushed = true;

            let alias_script = emit_uf_application_aliases(
                &uf_application_aliases,
                crate::smt::current_thread_solve_deadline(),
            )?;
            if !alias_script.is_empty() {
                let commands = ay_frontend::parse(&alias_script)?;
                self.exec.execute_all(&commands)?;
            }

            // Assert conjuncts individually for better theory axiom generation.
            let conjuncts = solve_expr.conjuncts();
            for c in &conjuncts {
                let c_str = InvariantModel::expr_to_smtlib(c);
                let assert_script = format!("(assert {c_str})\n");
                let cmds = ay_frontend::parse(&assert_script)?;
                self.exec.execute_all(&cmds)?;
            }

            // Check satisfiability.
            // #cert-accounting item 3: this verdict is consumed only as PDR
            // search guidance; the portfolio's published `Safe` claim is
            // re-derived from scratch by `verify_model_impl` (and, where run,
            // by the checked-replay pass) and reads nothing about how this
            // sub-query was certified. The declaration changes no gate and no
            // verdict today — it attributes this channel's certification cost
            // in `ay_dpll::CertificationAccounting`.
            let status = self
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
                .ok_or(PdrBackendError::MissingResult)?;

            match status.as_str() {
                "sat" => {
                    let model_output = self.exec.execute(&Command::GetModel)?.unwrap_or_default();
                    let mut model = FxHashMap::default();
                    parse_model_into(
                        &mut model,
                        &model_output,
                        &self.declared_datatype_constructors,
                    );
                    if !install_uf_application_alias_values(&mut model, &uf_application_aliases) {
                        return Ok(SmtResult::Unknown);
                    }
                    let validation_exprs = [expr];
                    Ok(
                        if let Some(model) = accept_reparsed_sat_model(
                            &validation_exprs,
                            model,
                            "pdr_executor_backend",
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
                        "pdr_executor_backend: unexpected result {other:?}; treating as Unknown"
                    );
                    Ok(SmtResult::Unknown)
                }
            }
        })();

        // Always pop, even on error.
        if pushed {
            match self.exec.execute(&Command::Pop(1)) {
                Ok(None) => {}
                Ok(Some(_)) => {
                    tracing::debug!("pdr_executor_backend: pop produced unexpected output");
                    self.reset();
                    return (SmtResult::Unknown, false);
                }
                Err(e) => {
                    tracing::debug!("pdr_executor_backend: pop failed: {e}");
                    self.reset();
                    return (SmtResult::Unknown, false);
                }
            }
        }

        // Restore the session default after a dv-off attempt (isolation:
        // later queries on a reused backend must run with the pass enabled).
        if disable_eq_diffvar {
            if let Err(e) = self.set_eq_diffvar_option(true) {
                tracing::debug!("pdr_executor_backend: dv-off restore failed: {e}");
                self.reset();
                return (SmtResult::Unknown, false);
            }
        }

        match result {
            Ok(r) => {
                self.query_count += 1;
                (r, raw_unknown)
            }
            Err(e) => {
                tracing::debug!("pdr_executor_backend: query failed: {e}");
                self.reset();
                (SmtResult::Unknown, false)
            }
        }
    }

    /// Write the per-run `:ay-eq-diffvar` option onto the session (inc-21).
    fn set_eq_diffvar_option(&mut self, enabled: bool) -> Result<(), PdrBackendError> {
        let script = format!("(set-option :ay-eq-diffvar {enabled})\n");
        let cmds = ay_frontend::parse(&script)?;
        self.exec.execute_all(&cmds)?;
        Ok(())
    }

    /// Initialize the executor with logic and options.
    fn initialize(&mut self, logic: &str, timeout: Duration) -> Result<(), PdrBackendError> {
        let mut script = String::with_capacity(128);
        script.push_str(&format!("(set-logic {logic})\n"));
        script.push_str("(set-option :produce-models true)\n");
        let timeout_ms = timeout.as_millis();
        if timeout_ms > 0 && timeout_ms < u128::from(u64::MAX) {
            script.push_str(&format!("(set-option :timeout {timeout_ms})\n"));
        }
        let cmds = ay_frontend::parse(&script)?;
        self.exec.execute_all(&cmds)?;
        self.logic = Some(logic.to_string());
        self.initialized = true;
        Ok(())
    }

    /// Declare datatype sorts that haven't been declared yet.
    fn declare_datatypes(
        &mut self,
        dt_decls: &[(&str, &[crate::ChcDtConstructor])],
    ) -> Result<(), PdrBackendError> {
        let mut pending = Vec::new();
        let mut pending_signatures = Vec::new();
        for &(name, constructors) in dt_decls {
            let signature = emit_declare_datatypes(&[(name, constructors)])
                .map_err(|error| PdrBackendError::InvalidDatatypeDeclaration(error.to_string()))?;
            if let Some(previous) = self.declared_datatypes.get(name) {
                if previous != &signature {
                    return Err(PdrBackendError::InvalidDatatypeDeclaration(format!(
                        "datatype sort '{name}' conflicts with its persistent-session definition"
                    )));
                }
                continue;
            }
            pending.push((name, constructors));
            pending_signatures.push((name.to_string(), signature));
        }
        if pending.is_empty() {
            return Ok(());
        }
        let dt_script = emit_declare_datatypes(&pending)
            .map_err(|error| PdrBackendError::InvalidDatatypeDeclaration(error.to_string()))?;
        let cmds = ay_frontend::parse(&dt_script)?;
        self.exec.execute_all(&cmds)?;
        for (_, constructors) in &pending {
            self.declared_datatype_constructors.extend(
                constructors
                    .iter()
                    .map(|constructor| constructor.name.clone()),
            );
        }
        for (name, signature) in pending_signatures {
            self.declared_datatypes.insert(name, signature);
        }
        Ok(())
    }

    /// Declare ordinary UFs that have not appeared in an earlier query.
    ///
    /// SMT-LIB functions are session-global and non-overloadable.  A new use
    /// of an existing name with a different signature therefore invalidates
    /// the query rather than being silently interpreted under the first
    /// declaration retained by the persistent executor.
    fn declare_missing_uninterpreted_functions(
        &mut self,
        expr: &ChcExpr,
    ) -> Result<(), PdrBackendError> {
        let declarations = collect_uninterpreted_function_declarations(expr)
            .map_err(|error| PdrBackendError::InvalidFunctionSignature(error.to_string()))?;
        let mut missing = Vec::new();
        for declaration in declarations {
            let signature = (
                declaration.return_sort.clone(),
                declaration.argument_sorts.clone(),
            );
            if let Some(existing) = self.declared_functions.get(&declaration.name) {
                if existing != &signature {
                    return Err(PdrBackendError::InvalidFunctionSignature(format!(
                        "function '{}' changed signature across persistent queries",
                        declaration.name
                    )));
                }
                continue;
            }
            missing.push((declaration, signature));
        }

        if missing.is_empty() {
            return Ok(());
        }
        let mut script = String::new();
        for (declaration, _) in &missing {
            script.push_str(&emit_declare_uninterpreted_function(declaration));
        }
        let commands = ay_frontend::parse(&script)?;
        self.exec.execute_all(&commands)?;
        for (declaration, signature) in missing {
            self.declared_functions.insert(declaration.name, signature);
        }
        Ok(())
    }

    /// Declare variables that haven't been declared yet.
    fn declare_missing_vars(&mut self, vars: &[ChcVar]) -> Result<(), PdrBackendError> {
        let mut script = String::new();
        for var in vars {
            if self.declared_vars.contains_key(&var.name) {
                continue;
            }
            let sort_str = sort_to_smtlib(&var.sort);
            let name = quote_symbol(&var.name);
            script.push_str(&format!("(declare-const {name} {sort_str})\n"));
            self.declared_vars
                .insert(var.name.clone(), var.sort.clone());
        }
        if script.is_empty() {
            return Ok(());
        }
        let cmds = ay_frontend::parse(&script)?;
        self.exec.execute_all(&cmds)?;
        Ok(())
    }

    /// Update the per-query timeout.
    fn update_timeout(&mut self, timeout: Duration) -> Result<(), PdrBackendError> {
        let timeout_ms = timeout.as_millis();
        if timeout_ms == 0 || timeout_ms >= u128::from(u64::MAX) {
            return Ok(());
        }
        let script = format!("(set-option :timeout {timeout_ms})\n");
        let cmds = ay_frontend::parse(&script)?;
        self.exec.execute_all(&cmds)?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ChcDtConstructor, ChcExpr, ChcOp, ChcSort, ChcVar};
    use std::sync::Arc;

    fn mk_var(name: &str) -> ChcExpr {
        ChcExpr::Var(ChcVar {
            name: name.to_string(),
            sort: ChcSort::Int,
        })
    }

    fn mk_int(v: i128) -> ChcExpr {
        ChcExpr::Int(v)
    }

    #[test]
    fn test_pdr_backend_sat_query() {
        // x >= 0 AND x <= 10 should be SAT
        let x = mk_var("x");
        let expr = ChcExpr::Op(
            ChcOp::And,
            vec![
                Arc::new(ChcExpr::Op(
                    ChcOp::Ge,
                    vec![Arc::new(x.clone()), Arc::new(mk_int(0))],
                )),
                Arc::new(ChcExpr::Op(
                    ChcOp::Le,
                    vec![Arc::new(x), Arc::new(mk_int(10))],
                )),
            ],
        );
        let mut backend = PdrExecutorBackend::new();
        let result = backend.check_sat(&expr, Duration::from_secs(5));
        assert!(result.is_sat(), "expected SAT, got: {result:?}");
        assert_eq!(backend.query_count(), 1);
    }

    /// Regression (task #29, `body ∧ trans ∧ ¬I` refutation-oracle Unknown):
    /// CHC clauses independently scope their forall vars and REUSE the same
    /// NAME with DIFFERENT sorts across clauses (e.g. `R1` typed Bool in the
    /// fact/query clause, Real in the transition rule). The persistent backend
    /// declares each name ONCE and `declare_missing_vars` skips any name already
    /// cached. Before the fix a name first seen as Bool was therefore NEVER
    /// re-declared as Real: the executor session kept a stale Bool declaration
    /// and a later real-arithmetic query built on top of it returned `unknown
    /// (:reason-unknown incomplete)` at scale — exactly the Unknown that aborted
    /// the DT-LRA learner on s3_srvr_4 at refinement iteration 1. This white-box
    /// test pins the FIX's mechanism: after a query that reuses `R1` with a
    /// conflicting sort, the persistent session is reset and `R1` is re-declared
    /// with its CURRENT sort (Real). Without the sort-conflict reset the cached
    /// sort would remain the stale Bool.
    #[test]
    fn test_pdr_backend_var_sort_collision_reset() {
        let mut backend = PdrExecutorBackend::new();
        // Query 1: R1 : Bool -> declares R1 as Bool on the persistent session.
        let r1_bool = ChcExpr::Var(ChcVar {
            name: "R1".to_string(),
            sort: ChcSort::Bool,
        });
        let res1 = backend.check_sat(&r1_bool, Duration::from_secs(5));
        assert!(res1.is_sat(), "bool query expected SAT, got: {res1:?}");
        assert_eq!(
            backend.declared_vars.get("R1"),
            Some(&ChcSort::Bool),
            "R1 should be cached as Bool after the first query"
        );
        // Query 2: R1 : Real reused on the SAME backend. The sort conflict must
        // reset the session so R1 is re-declared with its current sort (Real).
        let r1_real = ChcExpr::Var(ChcVar {
            name: "R1".to_string(),
            sort: ChcSort::Real,
        });
        let real_query = ChcExpr::Op(
            ChcOp::Ge,
            vec![Arc::new(r1_real), Arc::new(ChcExpr::Real(1, 1))],
        );
        let res2 = backend.check_sat(&real_query, Duration::from_secs(5));
        assert!(res2.is_sat(), "real query expected SAT, got: {res2:?}");
        assert_eq!(
            backend.declared_vars.get("R1"),
            Some(&ChcSort::Real),
            "sort-conflict reset must re-declare R1 with its CURRENT sort (Real); \
             a stale Bool here is the persistent name/sort collision that produced \
             the DT-LRA refutation Unknown"
        );
    }

    #[test]
    fn test_pdr_backend_unsat_query() {
        // x >= 10 AND x <= 5 should be UNSAT
        let x = mk_var("x");
        let expr = ChcExpr::Op(
            ChcOp::And,
            vec![
                Arc::new(ChcExpr::Op(
                    ChcOp::Ge,
                    vec![Arc::new(x.clone()), Arc::new(mk_int(10))],
                )),
                Arc::new(ChcExpr::Op(
                    ChcOp::Le,
                    vec![Arc::new(x), Arc::new(mk_int(5))],
                )),
            ],
        );
        let mut backend = PdrExecutorBackend::new();
        let result = backend.check_sat(&expr, Duration::from_secs(5));
        assert!(result.is_unsat(), "expected UNSAT, got: {result:?}");
    }

    #[test]
    fn test_pdr_backend_declares_scalar_uf_before_query() {
        let x = mk_var("x");
        let y = mk_var("y");
        let f_x = ChcExpr::FuncApp("f".to_string(), ChcSort::Int, vec![Arc::new(x.clone())]);
        let f_y = ChcExpr::FuncApp("f".to_string(), ChcSort::Int, vec![Arc::new(y.clone())]);
        let expr = ChcExpr::and_all([ChcExpr::eq(x, y), ChcExpr::not(ChcExpr::eq(f_x, f_y))]);

        let mut backend = PdrExecutorBackend::new();
        let result = backend.check_sat(&expr, Duration::from_secs(5));
        assert!(
            result.is_unsat(),
            "persistent PDR backend must declare f and enforce congruence: {result:?}"
        );
        assert_eq!(
            backend.declared_functions.get("f"),
            Some(&(ChcSort::Int, vec![ChcSort::Int]))
        );
    }

    #[test]
    fn test_pdr_backend_declares_ground_expression_local_datatype() {
        // The datatype occurs only as the result sort of ground constructor
        // applications. It is absent from the sole free variable, so a
        // vars-only declaration pass leaves Red/Blue undeclared while the UF
        // classifier correctly suppresses them as datatype constructors.
        let color = ChcSort::Datatype {
            name: "PdrGroundColor".to_string(),
            constructors: Arc::new(vec![
                ChcDtConstructor {
                    name: "PdrGroundRed".to_string(),
                    selectors: vec![],
                },
                ChcDtConstructor {
                    name: "PdrGroundBlue".to_string(),
                    selectors: vec![],
                },
            ]),
        };
        let enabled = ChcExpr::var(ChcVar::new("ground_dt_enabled", ChcSort::Bool));
        let red = ChcExpr::FuncApp("PdrGroundRed".to_string(), color.clone(), vec![]);
        let blue = ChcExpr::FuncApp("PdrGroundBlue".to_string(), color, vec![]);
        let expr = ChcExpr::and(enabled, ChcExpr::not(ChcExpr::eq(red, blue)));

        let mut backend = PdrExecutorBackend::new();
        let result = backend.check_sat(&expr, Duration::from_secs(5));
        assert!(
            result.is_sat(),
            "ground expression-local datatype query must be executable: {result:?}"
        );
        assert!(
            backend.declared_datatypes.contains_key("PdrGroundColor"),
            "persistent session must declare datatype metadata discovered in the expression"
        );
    }

    #[test]
    fn test_pdr_backend_extracts_exact_scalar_uf_application_value() {
        let x = mk_var("x_uf_sat");
        let f_x = ChcExpr::FuncApp(
            "f_uf_sat".to_string(),
            ChcSort::Int,
            vec![Arc::new(x.clone())],
        );
        let expr = ChcExpr::and_all([ChcExpr::eq(x, mk_int(3)), ChcExpr::eq(f_x, mk_int(9))]);

        let mut backend = PdrExecutorBackend::new();
        let result = backend.check_sat(&expr, Duration::from_secs(5));
        let SmtResult::Sat(model) = result else {
            panic!("persistent PDR UF witness should be strictly checkable: {result:?}");
        };
        assert_eq!(
            crate::expr::evaluate::evaluate_expr(&expr, &model),
            Some(crate::smt::SmtValue::Bool(true))
        );
    }

    #[test]
    fn test_pdr_backend_uf_alias_avoids_symbol_from_prior_query() {
        let x = ChcVar::new("x_prior_alias", ChcSort::Int);
        let x_expr = ChcExpr::var(x.clone());
        let f_x = ChcExpr::FuncApp(
            "f_prior_alias".to_string(),
            ChcSort::Int,
            vec![Arc::new(x_expr.clone())],
        );
        let prior = ChcVar::new("ay!uf!value!2", ChcSort::Int);
        let first = ChcExpr::and_all([
            ChcExpr::eq(f_x, mk_int(9)),
            ChcExpr::eq(ChcExpr::var(prior), mk_int(7)),
        ]);
        let mut backend = PdrExecutorBackend::new();
        let first_result = backend.check_sat(&first, Duration::from_secs(5));
        assert!(
            first_result.is_sat(),
            "setup query must be SAT: {first_result:?}"
        );

        let f_x_again = ChcExpr::FuncApp(
            "f_prior_alias".to_string(),
            ChcSort::Int,
            vec![Arc::new(x_expr.clone())],
        );
        let g_x = ChcExpr::FuncApp(
            "g_prior_alias".to_string(),
            ChcSort::Int,
            vec![Arc::new(x_expr)],
        );
        let second = ChcExpr::and_all([
            ChcExpr::eq(f_x_again, mk_int(9)),
            ChcExpr::eq(g_x, mk_int(10)),
        ]);
        let second_result = backend.check_sat(&second, Duration::from_secs(5));
        assert!(
            second_result.is_sat(),
            "a retained user declaration must not collide with a later UF alias: {second_result:?}"
        );
    }

    /// Inc-21: a dv-off-first attempt sets `:ay-eq-diffvar false` on the
    /// PERSISTENT session (set-option is not undone by pop), so it must be
    /// restored before returning — later queries on a reused backend run
    /// with the EqDiffVar pass enabled again.
    #[test]
    fn test_pdr_backend_dv_off_attempt_isolated_per_query() {
        let x = mk_var("x");
        let sat_expr = ChcExpr::Op(ChcOp::Ge, vec![Arc::new(x.clone()), Arc::new(mk_int(0))]);
        let mut backend = PdrExecutorBackend::new();
        let result = backend.check_sat_with_dv_hint(&sat_expr, Duration::from_secs(5), true);
        assert!(result.is_sat(), "expected SAT, got: {result:?}");

        let opt = backend
            .exec
            .execute(&ay_frontend::Command::GetOption(
                "ay-eq-diffvar".to_string(),
            ))
            .expect("get-option execution")
            .expect("get-option output");
        assert_eq!(
            opt, "(:ay-eq-diffvar true)",
            "dv-off option must be restored on the backend session"
        );

        // The reused backend still answers correctly afterwards.
        let unsat_expr = ChcExpr::Op(
            ChcOp::And,
            vec![
                Arc::new(ChcExpr::Op(
                    ChcOp::Ge,
                    vec![Arc::new(x.clone()), Arc::new(mk_int(10))],
                )),
                Arc::new(ChcExpr::Op(
                    ChcOp::Le,
                    vec![Arc::new(x), Arc::new(mk_int(5))],
                )),
            ],
        );
        let r2 = backend.check_sat(&unsat_expr, Duration::from_secs(5));
        assert!(
            r2.is_unsat(),
            "expected UNSAT after dv-off attempt, got: {r2:?}"
        );
    }

    #[test]
    fn test_pdr_backend_multiple_queries() {
        // Verify state persists across queries (vars remain declared)
        let x = mk_var("x");
        let sat_expr = ChcExpr::Op(ChcOp::Ge, vec![Arc::new(x.clone()), Arc::new(mk_int(0))]);
        let unsat_expr = ChcExpr::Op(
            ChcOp::And,
            vec![
                Arc::new(ChcExpr::Op(
                    ChcOp::Ge,
                    vec![Arc::new(x.clone()), Arc::new(mk_int(10))],
                )),
                Arc::new(ChcExpr::Op(
                    ChcOp::Le,
                    vec![Arc::new(x), Arc::new(mk_int(5))],
                )),
            ],
        );
        let mut backend = PdrExecutorBackend::new();
        let timeout = Duration::from_secs(5);

        let r1 = backend.check_sat(&sat_expr, timeout);
        assert!(r1.is_sat(), "query 1 expected SAT");

        let r2 = backend.check_sat(&unsat_expr, timeout);
        assert!(r2.is_unsat(), "query 2 expected UNSAT");

        assert_eq!(backend.query_count(), 2);
    }
}
