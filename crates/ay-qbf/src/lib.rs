#![forbid(unsafe_code)]
#![warn(missing_docs)]
// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! AY QBF - Quantified Boolean Formula Solver
//!
//! A QBF solver for prenex CNF.
//!
//! ## Features
//! - QDIMACS parser for standard QBF benchmarks, and a prenex QCIR-G14
//!   reader that translates the circuit to prenex CNF in the crate
//! - [`QbfSolver::solve_until`]: clausal-abstraction search (CAQE / QESTO
//!   style, one incremental CDCL solver per quantifier level) that runs to a
//!   verdict or a deadline; this is what `ay qbf solve` uses
//! - [`QbfSolver::solve`] / [`QbfSolver::solve_with_limit`]: budgeted exact
//!   QDPLL with partial-matrix pruning, fail-closed `Unknown` on budget
//!   exhaustion (the tests' independent reference)
//! - Experimental QCDCL machinery retained internally, not used for verdicts
//!
//! Strategy-certificate extraction is not yet part of either path; definite
//! results carry [`Certificate::None`].
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
//! assert_eq!(formula.num_vars(), 1);
//! assert_eq!(formula.prefix().len(), 1);
//! assert_eq!(formula.clauses().len(), 1);
//! let mut solver = QbfSolver::new(formula);
//! let result = solver.solve();
//! assert!(matches!(result, QbfResult::Sat(_)));
//! ```
//!
//! ## References
//! - Lonsing & Biere, "DepQBF: A Dependency-Aware QBF Solver"
//! - Zhang & Malik, "Conflict Driven Learning in a Quantified Boolean Satisfiability Solver"
//! - Rabe & Tentrup, "CAQE: A Certifying QBF Solver", FMCAD 2015
//! - Janota & Marques-Silva, "Solving QBF by Clause Selection", IJCAI 2015

#![warn(clippy::all)]

pub(crate) mod formula;
pub(crate) mod parser;
pub(crate) mod qcir;
pub(crate) mod solver;

pub use formula::{QbfFormula, Quantifier, QuantifierBlock};
pub use parser::{parse_qdimacs, QdimacsError};
pub use qcir::{is_qcir, parse_qcir, QcirError};
pub use solver::{Certificate, HerbrandFunction, QbfResult, QbfSolver, QbfStats, SkolemFunction};
