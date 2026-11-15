// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Proof production controls and access.

use crate::api::types::SolverError;
use crate::api::Solver;

impl Solver {
    /// Enable or disable proof production.
    ///
    /// When enabled, the solver collects proof steps during solving.
    /// After an UNSAT result, call [`last_proof`] to retrieve the proof.
    ///
    /// [`last_proof`]: Solver::last_proof
    pub fn set_produce_proofs(&mut self, enabled: bool) {
        self.executor.set_produce_proofs(enabled);
    }

    /// Select the Carcara dialect this solver's Alethe documents are spelled
    /// for (`Executor::set_alethe_dialect`). The default,
    /// [`AletheDialect::Clean`](crate::api::AletheDialect::Clean), prints the
    /// spellings Clean's vendored Carcara checks, and an artifact that keeps
    /// one discloses
    /// [`CarcaraSurface::CleanDialect`](crate::api::CarcaraSurface::CleanDialect).
    /// [`AletheDialect::PinnedCarcara`](crate::api::AletheDialect::PinnedCarcara)
    /// prints the spelling pinned Carcara 9a352ee accepts wherever one exists
    /// and is true.
    pub fn set_alethe_dialect(&mut self, dialect: crate::api::AletheDialect) {
        self.executor.set_alethe_dialect(dialect);
    }

    /// The dialect selected by [`Self::set_alethe_dialect`].
    #[must_use]
    pub fn alethe_dialect(&self) -> crate::api::AletheDialect {
        self.executor.alethe_dialect()
    }

    /// Collect a diagnostic proof surface without making successful proof
    /// translation a prerequisite for publishing an independently certified
    /// verdict.
    ///
    /// This is intentionally distinct from [`Self::set_produce_proofs`]. An
    /// explicit proof request is an authority demand: if strict validation of
    /// the requested artifact fails, an otherwise computed UNSAT must remain
    /// `unknown`. Best-effort collection retains a bounded proof when one can
    /// be reconstructed, so callers can inspect its non-strict and strict
    /// quality, while the verdict continues to depend on AY's mandatory
    /// independent UNSAT-certification funnel.
    ///
    /// `step_budget` is a deterministic bound on reconstruction work. Exhausting
    /// it omits the diagnostic artifact; it never authorizes an uncertified
    /// `unsat` result.
    pub fn set_best_effort_produce_proofs(&mut self, step_budget: u64) {
        self.executor.set_best_effort_produce_proofs(step_budget);
    }

    /// [`Solver::set_best_effort_produce_proofs`], and also keep the
    /// solver's own refutation for Explicit-mode interpolation
    /// ([`Solver::get_interpolants_for_masks`]).
    ///
    /// The artifact proof and every verdict are exactly those of best-effort
    /// production. The extra refutation is taken before any presentation pass
    /// re-spells, demotes or poisons it for an external checker, and its
    /// preprocessed `assume` leaves are attributed to the caller's groups
    /// through the sources the preprocessing recorded. It is not an
    /// exportable artifact; callers validate what they extract.
    pub fn set_interpolation_proofs(&mut self, step_budget: u64) {
        self.executor.set_interpolation_proofs(step_budget);
    }

    /// Enable or disable unsat core production.
    ///
    /// When enabled, the solver tracks named assertions during solving.
    /// After an UNSAT result, call [`try_get_unsat_core`] to retrieve the core.
    /// Enable this before the `check_sat` / `check_sat_assuming` call whose
    /// UNSAT core you want to inspect.
    ///
    /// [`try_get_unsat_core`]: Solver::try_get_unsat_core
    pub fn set_produce_unsat_cores(&mut self, enabled: bool) {
        self.set_option(
            ":produce-unsat-cores",
            if enabled { "true" } else { "false" },
        );
    }

    /// Convert an option value string to the corresponding SExpr.
    fn option_value_to_sexpr(value: &str) -> ay_frontend::sexp::SExpr {
        use ay_frontend::sexp::SExpr;
        match value {
            "true" => SExpr::True,
            "false" => SExpr::False,
            s if !s.is_empty() && s.bytes().all(|b| b.is_ascii_digit()) => {
                SExpr::Numeral(s.to_string())
            }
            _ => SExpr::String(value.to_string()),
        }
    }

    /// Fallible SMT-LIB option setter (#3543).
    ///
    /// Returns `Err` for executor-level failures while issuing the
    /// `set-option` command. This does not perform semantic validation of the
    /// option name or value beyond what the elaboration/executor layer already
    /// checks. In particular, unknown keywords are currently stored as generic
    /// options instead of being rejected.
    ///
    /// Use this instead of [`set_option`] when the caller needs to handle
    /// executor failures without panicking.
    ///
    /// [`set_option`]: Solver::set_option
    #[must_use = "try_* methods return a Result that must be used"]
    pub fn try_set_option(&mut self, keyword: &str, value: &str) -> Result<(), SolverError> {
        let sexpr_value = Self::option_value_to_sexpr(value);
        self.executor
            .execute(&ay_frontend::Command::SetOption(
                keyword.to_string(),
                sexpr_value,
            ))
            .map_err(SolverError::from)?;
        Ok(())
    }

    /// Set an SMT-LIB option by keyword and string value (#5505).
    ///
    /// Forwards to the executor's `Command::SetOption` handler, which stores
    /// the option in the elaboration context. Known options like
    /// `:produce-proofs`, `:produce-unsat-cores`, `:produce-models` affect
    /// solver behavior during `check_sat`.
    ///
    /// The keyword should include the leading `:` (e.g., `:produce-proofs`).
    /// Boolean values should be `"true"` or `"false"`.
    ///
    /// # Panics
    ///
    /// Panics if the executor returns an error while issuing the option.
    /// Use [`try_set_option`] for fallible handling.
    ///
    /// [`try_set_option`]: Solver::try_set_option
    pub fn set_option(&mut self, keyword: &str, value: &str) {
        self.try_set_option(keyword, value)
            .expect("set_option failed; use try_set_option for fallible handling");
    }

    /// Returns true if proof production is enabled.
    #[must_use]
    pub fn is_producing_proofs(&self) -> bool {
        self.executor.is_producing_proofs()
    }

    /// Proof from the last `check_sat` call.
    ///
    /// Returns `None` unless the last result was UNSAT and proof output was requested
    /// when that solve began; later setting changes cannot relabel the artifact.
    #[must_use]
    pub fn last_proof(&self) -> Option<&ay_core::Proof> {
        self.executor.last_proof()
    }
}
