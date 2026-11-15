// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SMT backend for CHC solving
//!
//! This module provides SMT query support for the PDR solver by converting
//! CHC expressions to ay-core terms and using the ay-dpll solver.

mod array_lambda;
mod array_model;
mod assumptions;
mod bounds;
mod bounds_inference;
mod bv_cache;
mod check_sat;
mod conflict_clause;
mod context;
mod convert;
mod convert_dag;
/// Workstream D (CHC-COMP 2026) DAG-linear printer/counter; owner WP-D1-P.
pub(crate) mod dag_smtlib;
pub(crate) mod deadline;
pub(crate) mod executor_adapter;
pub(crate) mod executor_sort_guard;
pub(crate) mod executor_unknown_memo;
pub(crate) mod executor_work;
mod incremental;
mod incremental_pdr;
// #horn-smt-session (Rung 1): `lane` is contract C6 (verification pins, the
// session mode flag, the process-wide board counters) over Rung 0's
// `SmtLane`; `session` is the module tree (see `session/mod.rs` for ownership).
mod interpolating;
mod interpolation_api;
pub(crate) mod lane;
mod model_extract;
pub(crate) mod model_verify;
pub(crate) mod pdr_executor_backend;
mod persistent;
pub(crate) mod replay_control;
pub(crate) mod resource_observation;
pub(crate) mod session;
pub(crate) mod solve_eqs;
pub(crate) mod sort_unique;
mod split_hints;
mod theory_classify;
pub(crate) mod types;
mod value_parse;

#[allow(clippy::panic)]
#[cfg(test)]
mod tests;
#[allow(clippy::panic)]
#[cfg(test)]
mod tests_accumulator_bug;
#[allow(clippy::panic)]
#[cfg(test)]
mod tests_advanced;
#[allow(clippy::panic)]
#[cfg(test)]
mod tests_assumptions;
#[allow(clippy::panic)]
#[cfg(test)]
mod tests_check_sat;
#[allow(clippy::panic)]
#[cfg(test)]
mod tests_executor_routed_fallback;
#[allow(clippy::panic)]
#[cfg(test)]
mod tests_model_verify;
#[allow(clippy::panic)]
#[cfg(test)]
mod tests_phase_seed;
#[allow(clippy::panic)]
#[cfg(test)]
mod tests_rung0_bridge_hygiene;

// Re-export public API (preserves all existing `use crate::smt::X` paths)
// SmtContext, SmtResult, SmtValue are re-exported as pub by lib.rs
#[cfg(test)]
pub(crate) use check_sat::ill_typed_engine_queries;
pub(crate) use context::{current_thread_solve_deadline, ScopedSolveDeadline};
pub(crate) use context::{
    no_progress_breaker_tripped, note_bv_cache_thrash_clear, note_solve_progress,
    note_unassignable_free_var_no_progress, ScopedNoProgressBreaker,
};
pub use context::{SmtContext, SmtLane};
pub use interpolation_api::InterpolationResult;
pub use types::UnsatCoreDiagnostics;
pub(crate) use types::{FarkasConflict, Partition};
pub use types::{SmtResult, SmtValue};

// Crate-internal re-exports
pub(crate) use deadline::{
    clamp_timeout_to_smt_deadline, smt_deadline_expired, ScopedLaneCancellation, ScopedSmtDeadline,
};
pub(crate) use incremental::{IncrementalCheckResult, IncrementalQueryContext};
pub(crate) use incremental_pdr::IncrementalPdrContext;
pub(crate) use interpolating::{InterpolatingResult, InterpolatingSmtContext};
pub(crate) use model_verify::is_theory_atom;
pub(crate) use pdr_executor_backend::PdrExecutorBackend;
pub(crate) use persistent::PersistentExecutorSmtContext;

pub(crate) fn parse_model_value_for_testing(input: &str, sort: &ay_core::Sort) -> Option<SmtValue> {
    value_parse::parse_smt_value_str(input, sort)
}
