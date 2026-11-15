// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A route `sat` the SAT emission refused (#qsat-refused-sat).
//!
//! The route's `sat` installs a witness model; the ordinary SAT emission's
//! quantified model gate then decides it (`qsat_publish_sat`). A refusal
//! there used to end the query: the route had already returned its verdict,
//! so the pass's legacy lanes never ran, and the memo told every later pass
//! that the route had published, which kept the nested-CEGQI lane and the
//! deep-QE retry stood down. Measured on the closed `∀q:Int. ∃r:Int. r > q`
//! under `:produce-proofs` (ay 9f51cc9556): the game decides `sat`, the
//! gate's strategy route cannot confirm the alternation (the probe's
//! refutation of `¬(q < q + 1)` carries no strict proof, so its `unsat` is
//! refused) and no other gate route confirms it either, and the query
//! answered `unknown`; under `--no-qsat` the same gate confirms the legacy
//! path's model and the answer is `sat`.
//!
//! A refused route `sat` is now what the route's docs say a refused
//! publication is: the route published nothing, it no longer stands the
//! legacy lanes down, and the query is solved once more without it (the memo
//! keeps the game from running again). The re-solve's verdict passes the
//! same emission gates as any other.

use super::Executor;
use crate::executor_types::{Result, SolveResult, UnknownReason};

impl Executor {
    /// When `result` is the `unknown` the emission made of the route's
    /// handed-off `sat`, withdraw the route and re-solve the query once;
    /// any other result is returned unchanged. No re-solve after a stop.
    pub(in crate::executor) fn qsat_refused_sat_resolve(
        &mut self,
        result: SolveResult,
    ) -> Result<SolveResult> {
        if result != SolveResult::Unknown || !std::mem::take(&mut self.qsat_route.sat_handed_off) {
            return Ok(result);
        }
        self.qsat_route.applied = false;
        self.qsat_route.strategy = None;
        self.qsat_note("qsat.publish", "sat-gate-refused");
        let stopped = matches!(
            self.last_unknown_reason,
            Some(
                UnknownReason::Timeout
                    | UnknownReason::ResourceLimit
                    | UnknownReason::MemoryLimit
                    | UnknownReason::Interrupted
            )
        ) || self.external_stop_reason().is_some()
            || ay_core::resource::check_stop_requested();
        if !stopped {
            self.last_statistics.set_int("qsat.refused_sat_resolves", 1);
        }
        // The re-solve resets the statistics and restores the memo's.
        let stats = self.qsat_statistics();
        if let Some(memo) = self.qsat_route.memo.as_mut() {
            memo.published = false;
            memo.stats = stats;
        }
        if stopped {
            return Ok(result);
        }
        self.reset_public_query_solve_state();
        self.array_ext_shadow.clear();
        self.cegqi_ce_free_stash = None;
        self.last_unknown_reason = None;
        self.last_result = None;
        self.last_model = None;
        self.solve_and_emit_primary()
    }
}

#[cfg(test)]
mod tests;
