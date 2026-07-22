// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! SMT backend for CHC solving
//!
//! This module provides SMT query support for the PDR solver by converting
//! CHC expressions to ay-core terms and using the ay-dpll solver.

mod array_model;
mod assumptions;
mod bounds;
mod bounds_inference;
mod bv_cache;
mod check_sat;
mod conflict_clause;
mod context;
mod convert;
pub(crate) mod deadline;
pub(crate) mod executor_adapter;
pub(crate) mod executor_sort_guard;
pub(crate) mod executor_unknown_memo;
mod incremental;
mod incremental_pdr;
mod interpolating;
mod interpolation_api;
mod model_extract;
pub(crate) mod model_verify;
pub(crate) mod pdr_executor_backend;
mod persistent;
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
mod tests_model_verify;
#[allow(clippy::panic)]
#[cfg(test)]
mod tests_phase_seed;

// Re-export public API (preserves all existing `use crate::smt::X` paths)
// SmtContext, SmtResult, SmtValue are re-exported as pub by lib.rs
pub use context::SmtContext;
pub(crate) use context::{current_thread_solve_deadline, ScopedSolveDeadline};
pub(crate) use context::{
    no_progress_breaker_tripped, note_bv_cache_thrash_clear, note_solve_progress,
    note_unassignable_free_var_no_progress, ScopedNoProgressBreaker,
};
pub use interpolation_api::InterpolationResult;
pub use types::UnsatCoreDiagnostics;
pub(crate) use types::{FarkasConflict, Partition};
pub use types::{SmtResult, SmtValue};

// Crate-internal re-exports
pub(crate) use deadline::{clamp_timeout_to_smt_deadline, smt_deadline_expired, ScopedSmtDeadline};
pub(crate) use incremental::{IncrementalCheckResult, IncrementalQueryContext};
pub(crate) use incremental_pdr::IncrementalPdrContext;
pub(crate) use interpolating::{InterpolatingResult, InterpolatingSmtContext};
pub(crate) use model_verify::is_theory_atom;
pub(crate) use pdr_executor_backend::PdrExecutorBackend;
pub(crate) use persistent::PersistentExecutorSmtContext;

pub(crate) fn parse_model_value_for_testing(input: &str, sort: &ay_core::Sort) -> Option<SmtValue> {
    value_parse::parse_smt_value_str(input, sort)
}
