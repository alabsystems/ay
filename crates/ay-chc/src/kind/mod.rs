// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! K-Induction solver for CHC problems
//!
//! K-Induction is a bounded model checking algorithm that combines:
//! - Base case: Check if error states are reachable in up to k steps
//! - Induction step: Check if k-step induction proves safety
//!
//! This is a port of Golem's Kind engine (200 lines C++).
//!
//! ## Algorithm
//!
//! For each k from 0 to max_k:
//!
//! 1. **Base case**: Init(x₀) ∧ Tr(x₀,x₁) ∧ ... ∧ Tr(xₖ₋₁,xₖ) ∧ Query(xₖ)
//!    - If SAT: found counterexample of length k → UNSAFE
//!
//! 2. **Forward induction**: ¬Query(x₀) ∧ Tr(x₀,x₁) ∧ ¬Query(x₁) ∧ ... ∧ ¬Query(xₖ) ⟹ ¬Query(xₖ₊₁)
//!    - If valid (negation is UNSAT): found k-inductive invariant → SAFE
//!
//! 3. **Backward induction**: Tr(x₀,x₁) ∧ ¬Init(x₁) ∧ ... ∧ Tr(xₖ,xₖ₊₁) ∧ ¬Init(xₖ₊₁) ⟹ ¬Init(x₀)
//!    - If valid (negation is UNSAT): found k-inductive invariant → SAFE
//!
//! ## Applicability
//!
//! K-Induction works best on linear CHC problems (single predicate transition systems).
//! For non-linear problems, we fall back to PDR.

use std::cell::Cell;

use crate::cancellation::CancellationToken;
use crate::engine_config::ChcEngineConfig;
use ay_core::kani_compat::DetHashMap as FxHashMap;

use crate::engine_result::build_single_pred_model;
use crate::smt::SmtValue;
use crate::smt::{IncrementalCheckResult, IncrementalQueryContext};
use crate::transition_system::TransitionSystem;
use crate::{ChcExpr, ChcProblem, Counterexample, CounterexampleStep, InvariantModel, PredicateId};
use ay_sat::{TlaTraceWriter, TlaTraceable};

mod solve;
mod trace;
mod verify;

#[cfg(test)]
mod tests;

/// Outcome of a fresh induction cross-check (#7739).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum FreshCheckOutcome {
    /// Fresh solver confirmed UNSAT — induction step is valid.
    ConfirmedUnsat,
    /// Fresh solver found SAT — incremental result was a false-UNSAT.
    CounterexampleSat,
    /// Fresh solver returned UNKNOWN after consuming the allotted timeout.
    BudgetUnknown { timeout: std::time::Duration },
}

impl FreshCheckOutcome {
    fn from_smt_result(result: &crate::smt::SmtResult, timeout: std::time::Duration) -> Self {
        if result.is_unsat() {
            Self::ConfirmedUnsat
        } else if result.is_unknown() {
            Self::BudgetUnknown { timeout }
        } else {
            Self::CounterexampleSat
        }
    }

    fn as_str(&self) -> &'static str {
        match self {
            Self::ConfirmedUnsat => "UNSAT",
            Self::CounterexampleSat => "SAT",
            Self::BudgetUnknown { .. } => "UNKNOWN",
        }
    }
}

/// K-Induction solver result (type alias for unified ChcEngineResult).
pub type KindResult = crate::engine_result::ChcEngineResult;

/// K-Induction solver configuration
#[derive(Debug, Clone)]
pub struct KindConfig {
    /// Common engine config (verbose, cancellation)
    pub(crate) base: ChcEngineConfig,
    /// Maximum k to try
    pub(crate) max_k: usize,
    /// Timeout per SMT query
    pub(crate) query_timeout: std::time::Duration,
    /// Total time budget for the entire K-Induction run
    /// If exceeded, returns Unknown and lets PDR take over
    pub(crate) total_timeout: std::time::Duration,

    /// Extra wall-clock allowance, beyond `total_timeout`, that may be spent
    /// ONLY on validating a proof that induction already found (fresh
    /// cross-check, init/query verification, k-to-1 strengthening).
    ///
    /// Rationale (lustre-class): short Kind probes routinely PROVE forward
    /// induction at low k right at the budget edge, then drop the proof
    /// because the mandatory #6789 cross-check runs with a zero timeout.
    /// Search remains bounded by `total_timeout`; the grace only prevents a
    /// found proof from being discarded for lack of validation budget.
    pub(crate) validation_grace: std::time::Duration,

    /// BMC-only mode: skip forward/backward induction checks.
    pub(crate) bmc_only: bool,
}

impl KindConfig {
    /// Create a KindConfig from individual fields, wrapping verbose and
    /// cancellation_token into the embedded `ChcEngineConfig`.
    pub fn with_engine_config(
        max_k: usize,
        query_timeout: std::time::Duration,
        total_timeout: std::time::Duration,
        verbose: bool,
        cancellation_token: Option<CancellationToken>,
    ) -> Self {
        Self {
            base: ChcEngineConfig {
                verbose,
                cancellation_token,
            },
            max_k,
            query_timeout,
            total_timeout,
            validation_grace: std::time::Duration::ZERO,
            bmc_only: false,
        }
    }

    /// Builder: allow proof validation to spend up to `grace` beyond
    /// `total_timeout` (see `validation_grace`).
    pub fn with_validation_grace(mut self, grace: std::time::Duration) -> Self {
        self.validation_grace = grace;
        self
    }
}

impl Default for KindConfig {
    fn default() -> Self {
        Self {
            base: ChcEngineConfig::default(),
            max_k: 50,
            query_timeout: std::time::Duration::from_secs(5),
            total_timeout: std::time::Duration::from_secs(30),
            validation_grace: std::time::Duration::ZERO,
            bmc_only: false,
        }
    }
}

/// K-Induction solver
pub struct KindSolver {
    problem: ChcProblem,
    config: KindConfig,
    tla_trace: Option<TlaTraceWriter>,
    /// Current check phase for TLA trace (idle/base/forward/backward).
    /// Uses `Cell` for interior mutability (TLA trace methods take `&self`).
    trace_phase: Cell<&'static str>,
    /// Whether base case has been checked at the current k value.
    /// Mirrors `baseCaseChecked` in `specs/kind_test.tla` (#3022).
    trace_base_case_checked: Cell<bool>,
}

impl Drop for KindSolver {
    fn drop(&mut self) {
        // Release the TLA trace file claim if we claimed it during
        // enable_tla_trace(). Without this, subsequent solvers in the
        // same process (e.g., PDR after Kind in the adaptive portfolio)
        // cannot trace because claim_trace_file() is still held (#8673).
        if self.tla_trace.is_some() {
            ay_core::release_trace_file();
        }
        std::mem::take(&mut self.problem).iterative_drop();
    }
}

const KIND_TRACE_MODULE: &str = "kind_test";
const KIND_TRACE_VARIABLES: [&str; 4] = ["k", "result", "phase", "baseCaseChecked"];

impl TlaTraceable for KindSolver {
    fn tla_module() -> &'static str {
        KIND_TRACE_MODULE
    }

    fn tla_variables() -> &'static [&'static str] {
        &KIND_TRACE_VARIABLES
    }

    /// Enable TLA2 JSONL trace emission for this solver instance.
    fn enable_tla_trace(&mut self, path: &str, module: &str, variables: &[&str]) {
        ay_core::claim_trace_file();
        self.tla_trace = Some(TlaTraceWriter::new(path, module, variables));
        self.kind_trace_step_at(0, "Running", None);
    }
}

impl KindSolver {
    /// Create a new K-Induction solver
    pub(crate) fn new(problem: ChcProblem, config: KindConfig) -> Self {
        Self {
            problem,
            config,
            tla_trace: None,
            trace_phase: Cell::new("idle"),
            trace_base_case_checked: Cell::new(false),
        }
    }
}
