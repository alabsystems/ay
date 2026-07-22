// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// WIP engine (#8211). Not yet wired into the portfolio — all items in this
// module are currently dead from the public API perspective but are kept as
// in-progress infrastructure. Remove these allows when the engine is wired up.
#![allow(dead_code, unused_variables)]

//! Clause-level IC3/PDR engine for bit-level hardware model checking (#8211).
//!
//! This module implements IC3 (Bradley 2011) / PDR (Een et al. 2011) operating
//! directly on propositional clauses using ay-sat as the SAT solver backend. Unlike
//! the word-level PDR in `crate::pdr` which uses SMT queries over LIA/BV
//! expressions, this engine works at the clause level:
//!
//! - Frames are sets of clauses (negated blocked cubes)
//! - Generalization uses clause-level MIC (drop literals, check inductiveness)
//! - All queries go through ay-sat assumption-based solving
//! - No SMT overhead for pure Boolean problems
//!
//! This is the correct abstraction level for AIGER/HWMCC benchmarks where
//! each latch is a single bit.
//!
//! # References
//!
//! - Bradley, "SAT-Based Model Checking without Unrolling" (VMCAI 2011)
//! - Een, Mishchenko, Brayton, "Efficient Implementation of PDR" (FMCAD 2011)
//! - Z3 Spacer: `reference/z3/src/muz/spacer/`
//! - rIC3: clause-level IC3 reference implementation

mod cube;
mod definition_library;
mod generalize;
mod propagate;
// Exposed crate-wide (#8211 wiring) so the additive `crate::ic3_lane` portfolio
// lane can construct a transition system and drive the solver.
pub(crate) mod solver;
mod stats;
pub(crate) mod transition_system;

#[cfg(test)]
mod tests;
