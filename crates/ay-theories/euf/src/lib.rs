// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![forbid(unsafe_code)]

//! AY EUF - Equality and Uninterpreted Functions theory solver
//!
//! Implements congruence closure for equality reasoning.
//!
//! ## Architecture
//!
//! The solver uses an incremental E-graph structure inspired by Z3's egraph:
//! - `ENode`: Tracks term identity, equivalence class membership, and parent pointers
//! - `CongruenceTable`: Persistent hash table mapping signatures to canonical representatives
//! - Worklist-based merge propagation for O(n log n) amortized complexity
//!
//! Reference: Z3 egraph (Nikolaj Bjorner, MIT License)
//! `reference/z3/src/ast/euf/euf_egraph.{h,cpp}`

#![warn(missing_docs)]
#![warn(clippy::all)]
// Complex types for congruence closure lookup maps
#![allow(clippy::type_complexity)]

// Import safe_eprintln! from ay-core (non-panicking eprintln replacement)
#[macro_use]
extern crate ay_core;

mod bool_atoms;
mod closure;
mod egraph;
mod explain;
mod merge;
mod model_extraction;
mod solver;
mod solver_query;
mod theory_check;
mod theory_impl;
mod theory_propagate;
mod types;
mod verification;

#[allow(clippy::panic)]
#[cfg(test)]
mod tests;

// Re-export public API
pub use bool_atoms::{clear_bool_arg_repair_candidates, take_bool_arg_repair_candidates};
pub use solver::EufSolver;
pub use solver_query::DiscoveredDisequality;
pub use theory_propagate::{EUF_LAZY_MAGIC, EUF_LAZY_MAGIC_MASK};
pub use types::{EufModel, FunctionTable, SortModel};

pub mod theories_ledger;
