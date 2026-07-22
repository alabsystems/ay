#![forbid(unsafe_code)]
#![warn(missing_docs)]
// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! AY QBF - Quantified Boolean Formula Solver
//!
//! A QCDCL (Quantified Conflict-Driven Clause Learning) solver for QBF.
//!
//! ## Features
//! - QDIMACS parser for standard QBF benchmarks
//! - Budgeted exact QDPLL verdict authority with partial-matrix pruning
//! - Fail-closed `Unknown` on node-budget exhaustion
//! - Experimental QCDCL machinery retained internally for continued work
//!
//! Strategy-certificate extraction is not yet part of the authoritative path;
//! definite results currently carry [`Certificate::None`].
//!
//! ## Algorithm Overview
//!
//! QCDCL extends CDCL to handle quantified formulas:
//! - Variables are partitioned into existential (∃) and universal (∀) quantifier blocks
//! - Universal reduction removes universal literals that cannot affect satisfiability
//! - Conflict analysis respects quantifier dependencies
//! - Learned clauses must be "dependency-valid"
//!
//! ## Example
//!
//! ```
//! use ay_qbf::{QbfSolver, QbfFormula, QbfResult, QuantifierBlock};
//! use ay_sat::Literal;
//!
//! // ∃x. (x) — trivially SAT
//! let formula = QbfFormula::new(
//!     1,
//!     vec![QuantifierBlock::exists(vec![1])],
//!     vec![vec![Literal::positive(ay_sat::Variable::new(1))]],
//! );
//! let mut solver = QbfSolver::new(formula);
//! let result = solver.solve();
//! assert!(matches!(result, QbfResult::Sat(_)));
//! ```
//!
//! ## References
//! - Lonsing & Biere, "DepQBF: A Dependency-Aware QBF Solver"
//! - Zhang & Malik, "Conflict Driven Learning in a Quantified Boolean Satisfiability Solver"

#![warn(clippy::all)]

pub(crate) mod formula;
pub(crate) mod parser;
pub(crate) mod solver;

pub use formula::{QbfFormula, Quantifier, QuantifierBlock};
pub use parser::{parse_qdimacs, QdimacsError};
pub use solver::{Certificate, HerbrandFunction, QbfResult, QbfSolver, QbfStats, SkolemFunction};
