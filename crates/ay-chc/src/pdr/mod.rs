// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! PDR (Property-Directed Reachability) / IC3 solver for CHC
//!
//! This implements the PDR algorithm for solving Constrained Horn Clause problems.
//! The algorithm maintains frames (over-approximations of reachable states) and
//! refines them by blocking counterexample states using SMT queries.
//!
//! ## Module Structure
//!
//! - `config`: Solver configuration types
//! - `model`: Predicate interpretation and model types
//! - `counterexample`: Counterexample trace types
//! - `frame`: Frame and lemma management
//! - `obligation`: Proof obligation types
//! - `scc`: Strongly connected component analysis
//! - `invariant_parser`: SMT-LIB invariant parsing
//! - `interpolation_failure`: Structured diagnostics for interpolation failures
//! - `solver`: Main PDR solver implementation

mod anti_unify;
mod case_split;
mod config;
pub(crate) mod counterexample;
pub(crate) mod cube;
mod derivation;
mod expr_utils;
mod frame;
mod generalization;
mod generalize_adapter;
mod global_generalizer;
pub(crate) mod implication_cache;
mod init_analysis;
mod interpolation_failure;
mod invariant_parser;
pub(crate) use invariant_parser::validate_qf_expression;
mod lemma_cluster;
mod lemma_sanitize;
pub(crate) mod model;
mod obligation;
mod pob_concretize;
mod reach_fact;
mod reach_solver;
pub(crate) mod scc;
mod semantic_match;
mod solver;
mod types;
mod verification;

// Re-export public types
pub use config::PdrConfig;
pub use counterexample::{Counterexample, CounterexampleStep};
pub use frame::PdrResult;
pub use model::{
    ChcReplayObligation, ChcReplayObligationKind, InvariantModel, PredicateInterpretation,
};
pub use solver::PdrSolver;
pub use verification::CexVerificationResult;
