// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//! Canonical FlatZinc-to-SMT-LIB2 translator for AY.
//!
//! This crate owns `translate`, `TranslationResult`, SMT variable naming,
//! SMT-side output metadata, and the SMT solver driver helpers. The
//! `ay-fzn2smt` crate consumes these public types for `ay flatzinc solve` and
//! separately owns the direct CP backend; it should not duplicate this SMT
//! translator.

#![forbid(unsafe_code)]

pub mod branching;
mod builtins;
mod builtins_arithmetic;
mod builtins_extra;
pub mod error;
mod globals;
mod globals_count;
mod globals_extra;
mod globals_regular;
mod logic;
pub mod output;
mod resolve;
pub mod search;
mod set_constraints;
mod set_constraints_reif;
pub mod solver;
pub(crate) mod translate;

pub use branching::solve_branching;
pub use error::TranslateError;
pub use output::format_dzn_solution;
pub use search::{
    flatten_search_vars, parse_search_annotations, SearchAnnotation, SearchStrategy, ValChoice,
    VarChoice,
};
pub use solver::{solve, SolverConfig, SolverError};
pub use translate::{translate, ObjectiveInfo, OutputVarInfo, TranslationResult, VarDomain};

#[cfg(test)]
mod ay_library_bench;
#[cfg(test)]
mod tests;
#[cfg(test)]
mod tests_error;
#[cfg(test)]
mod tests_extended;
#[cfg(test)]
mod tests_globals;
#[cfg(test)]
mod tests_globals_extra;
#[cfg(test)]
mod tests_set_constraints;
