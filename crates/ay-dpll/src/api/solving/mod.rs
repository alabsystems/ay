// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Assertion, solving, and model extraction for AY Solver API.
//!
//! This module is split by solver lifecycle stage:
//!
//! - [`assertions`]: Assert, push, pop, scopes, reset
//! - [`controls`]: Verification level, counterexample style, timeout/memory/clause limits,
//!   interrupt, unknown reason, statistics
//! - [`check`]: `check_sat`, `check_sat_assuming`, shared preflight/epilogue helpers
//! - [`panic_safe`]: `try_check_sat`, `try_check_sat_assuming`
//! - [`cross_check`]: script-first replay API for logic/seed differential checks
//! - [`model`]: Unsat assumptions, model/value extraction, declared variables
//! - [`proofs`]: Proof production controls and access
//! - [`parse`]: SMT-LIB2 parsing bridge
//! - [`scope`]: RAII `SolverScope` helper for balanced push/pop lifetimes

mod abduction;
mod annotated_core;
mod assertions;
mod check;
mod controls;
mod core_evolution;
mod cross_check;
mod explanation;
mod field_sat;
mod field_simplify;
mod field_solve;
mod field_to_bv;
mod field_unique;
mod interpolant;
pub(crate) mod interpolant_farkas;
mod maxsmt;
mod model;
mod model_blocking;
mod model_minimize;
mod model_provenance;
mod named_values;
mod native_assertion_source;
mod native_replay;
mod optimize;
mod panic_safe;
mod parse;
mod polynomial_parameters;
mod proofs;
mod scalar_functions;
mod scope;
mod tactic_bool_rewrite;
mod tactic_model;
mod tactic_parameters;
mod tactic_polynomial;
pub use polynomial_parameters::PolynomialParameters;
mod tactic_prepare;
mod tactic_propagate_values;
mod tactic_sequence_rewrite;
mod tactic_solve_eqs;
mod term_simplifier;
pub use term_simplifier::SimplifyParameters;
mod tactics;

pub use abduction::{PatchStrength, PatchSuggestion};
pub use parse::{
    ParsedPublicFormulaMetadata, ParsedPublicTermMetadata, ParsedSmtlib2Batch, ParsedSmtlib2Formula,
};
pub use scope::SolverScope;
pub use tactic_model::TacticModelConverter;
pub use tactic_parameters::{TacticInstance, TacticParameterValue, TacticParameters};
pub(crate) use tactic_prepare::PreparedTactic;
pub use tactics::{
    ApplyResult, Goal, Tactic, TacticDecision, TacticExecutionKind, TacticFailure, TacticOperation,
    TacticSolver, TacticSubgoal,
};
