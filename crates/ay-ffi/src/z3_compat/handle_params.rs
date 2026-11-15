// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Solver parameters per handle (T5 P0.2 Q10).
//!
//! Every Solver and Optimize handle of a context shares the context's engine.
//! `Z3_solver_set_params` used to write the engine directly, so one solver's
//! `timeout` governed every later check of every handle (measured: after
//! `s1.set("timeout", 1)`, a fresh `s2` answered a pigeonhole `unknown`;
//! libz3 5.1.0 answers `unsat`). The interrupt flag was sticky as well
//! (`Z3_interrupt` and then a check answered `unknown`; libz3 5.1.0 answers
//! `sat`).
//!
//! Each handle now keeps its own [`ParamSet`]; the context keeps the defaults
//! of `Z3_mk_context`'s configuration and `Z3_update_param_value`. A check
//! applies the full effective set (handle over context) to the engine, clears
//! the interrupt, and restores the engine's previous settings when it ends.

use std::panic::{catch_unwind, AssertUnwindSafe};
use std::time::Duration;

use ay_dpll::api::Solver;

use super::Z3_context;

/// The parameters AY honours, as one handle or the context set them; an
/// unset field falls back to the context default.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct ParamSet {
    /// `timeout` in milliseconds; `0` means no limit (z3's convention).
    timeout_ms: Option<u64>,
    /// `proof` / `produce_proofs`.
    proofs: Option<bool>,
    clause_proof: Option<bool>,
}

impl ParamSet {
    /// Record the honoured keys of `params` (the keys `apply_supported_params`
    /// reads); later values override earlier ones, unknown keys are ignored.
    pub(crate) fn record(&mut self, params: &[(String, String)]) {
        for (key, value) in params {
            match key.as_str() {
                "timeout" => {
                    if let Ok(ms) = value.parse::<u64>() {
                        self.timeout_ms = Some(ms);
                    }
                }
                "clause_proof" => self.clause_proof = Some(matches!(value.as_str(), "true" | "1")),
                "proof" | "produce_proofs" | "produce-proofs" => {
                    self.proofs = Some(matches!(value.as_str(), "true" | "1"));
                }
                _ => {}
            }
        }
    }

    /// Set proof production (`Z3_solver_set_proof_production`).
    pub(crate) fn set_proofs(&mut self, enabled: bool) {
        self.proofs = Some(enabled);
    }

    /// This set with every unset field taken from `defaults`.
    #[must_use]
    pub(crate) fn over(self, defaults: ParamSet) -> ParamSet {
        ParamSet {
            timeout_ms: self.timeout_ms.or(defaults.timeout_ms),
            proofs: self.proofs.or(defaults.proofs),
            clause_proof: self.clause_proof.or(defaults.clause_proof),
        }
    }

    /// Whether proofs are produced under this set, with an engine that
    /// produces them exactly when `engine_default` holds.
    pub(crate) fn proofs_enabled(self, engine_default: bool) -> bool {
        self.proofs.unwrap_or(engine_default)
    }

    pub(crate) fn clause_proof_enabled(self) -> bool {
        self.clause_proof.unwrap_or(false)
    }

    fn timeout(self) -> Option<Duration> {
        self.timeout_ms
            .filter(|&ms| ms != 0)
            .map(Duration::from_millis)
    }
}

/// The engine's settings before a check applied its handle's parameters.
pub(crate) struct EngineSettings {
    timeout: Option<Duration>,
    clause_capture: ay_dpll::api::ClauseEventCapture,
    /// The proof setting to restore, when the check changed it. Proof
    /// production is switched only when the effective set names it and it
    /// differs: the switch also resets proof and interpolation state.
    proofs: Option<bool>,
}

impl EngineSettings {
    /// Apply `effective` in full to the engine and clear its interrupt flag
    /// (libz3 5.1.0 answers `sat` on a check after `Z3_interrupt`), returning
    /// the settings to restore when the check ends.
    pub(crate) fn apply(solver: &mut Solver, effective: ParamSet) -> EngineSettings {
        let current_proofs = solver.is_producing_proofs();
        let saved = EngineSettings {
            timeout: solver.timeout(),
            clause_capture: solver.clause_event_capture(),
            proofs: (effective.proofs_enabled(current_proofs) != current_proofs)
                .then_some(current_proofs),
        };
        solver.set_clause_event_capture(if effective.clause_proof_enabled() {
            ay_dpll::api::ClauseEventCapture::Lifecycle
        } else {
            ay_dpll::api::ClauseEventCapture::Additions
        });
        solver.set_timeout(effective.timeout());
        if saved.proofs.is_some() {
            solver.set_produce_proofs(!current_proofs);
        }
        solver.clear_interrupt();
        saved
    }

    /// Restore the settings [`Self::apply`] replaced.
    pub(crate) fn restore(self, solver: &mut Solver) {
        solver.set_clause_event_capture(self.clause_capture);
        solver.set_timeout(self.timeout);
        if let Some(proofs) = self.proofs {
            solver.set_produce_proofs(proofs);
        }
    }
}

/// Begin an auxiliary query of a handle with parameters `params`
/// (`Z3_solver_get_consequences`, `Z3_get_implied_equalities`): apply them
/// over the context defaults and clear the interrupt. `None` for a null
/// context. Pair it with [`finish_handle_query`].
///
/// # Safety
/// `c` must be null or a live context that no other reference borrows for
/// the duration of the call.
pub(crate) unsafe fn begin_handle_query(c: Z3_context, params: ParamSet) -> Option<EngineSettings> {
    // SAFETY: per this function's contract; the borrow ends with the call.
    let ctx = unsafe { c.as_mut() }?;
    catch_unwind(AssertUnwindSafe(|| {
        EngineSettings::apply(&mut ctx.solver, params.over(ctx.default_params))
    }))
    .ok()
}

/// End a query begun by [`begin_handle_query`]: remove any definition the
/// engine adopted during it (see `solver::release_adopted_definitions`) and
/// restore the engine settings. The context's error state is kept.
///
/// # Safety
/// As for [`begin_handle_query`].
pub(crate) unsafe fn finish_handle_query(
    c: Z3_context,
    settings: Option<EngineSettings>,
    operation: &str,
) {
    // SAFETY: per this function's contract; the borrow ends with the call.
    let Some(ctx) = (unsafe { c.as_mut() }) else {
        return;
    };
    let finished = catch_unwind(AssertUnwindSafe(|| {
        super::solver::release_adopted_definitions(ctx, operation);
        if let Some(settings) = settings {
            settings.restore(&mut ctx.solver);
        }
    }));
    if finished.is_err() {
        // A panic while releasing leaves the engine state unknown.
        ctx.poison_decision_engine(format!(
            "{operation}: the engine could not be restored after the query"
        ));
    }
}
