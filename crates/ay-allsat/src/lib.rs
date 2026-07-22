#![forbid(unsafe_code)]
#![warn(missing_docs)]
// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Solution Enumeration (ALL-SAT) Solver
//!
//! ALL-SAT finds all satisfying assignments for a Boolean formula. This is useful
//! for complete analysis, model counting (when count is small), and configuration
//! enumeration.
//!
//! ## Problem Variants
//!
//! - **Full enumeration**: Find all complete assignments
//! - **Projected enumeration**: Find all assignments to a subset of "important" variables
//! - **Bounded enumeration**: Find up to k solutions
//!
//! ## Example
//!
//! ```
//! use ay_allsat::{AllSatSolver, AllSatConfig};
//!
//! let mut solver = AllSatSolver::new();
//!
//! // (x1 OR x2) AND (NOT x1 OR NOT x2)
//! // Solutions: x1=T,x2=F and x1=F,x2=T
//! solver.add_clause(vec![1, 2]);
//! solver.add_clause(vec![-1, -2]);
//!
//! let solutions: Vec<_> = solver.iter().collect();
//! assert_eq!(solutions.len(), 2);
//! ```
//!
//! ## Projected Enumeration
//!
//! ```
//! use ay_allsat::{AllSatSolver, AllSatConfig};
//!
//! let mut solver = AllSatSolver::new();
//!
//! // x1 AND (x2 OR x3)
//! solver.add_clause(vec![1]);
//! solver.add_clause(vec![2, 3]);
//!
//! // Only care about assignments to x1
//! let config = AllSatConfig {
//!     projection: Some(vec![1]),
//!     ..Default::default()
//! };
//! let solutions = solver.enumerate_with_config(config);
//! // Only one projected solution: x1=T
//! assert_eq!(solutions.len(), 1);
//! ```
//!
//! ## Algorithm
//!
//! Uses iterative SAT solving with blocking clauses:
//!
//! 1. Solve the formula
//! 2. If SAT, record the solution
//! 3. Add a blocking clause that excludes this solution
//! 4. Repeat until UNSAT
//!
//! For projected enumeration, blocking clauses only reference projected variables.
//!
//! ## Performance Notes
//!
//! - ALL-SAT can be exponentially expensive (2^n solutions in worst case)
//! - Use bounded enumeration or projection to limit work
//! - Early termination via iterator lets you process solutions incrementally
//!
//! ## References
//!
//! - McMillan, "Applying SAT Methods in Unbounded Symbolic Model Checking"
//! - Grumberg et al., "Memory Efficient All-Solutions SAT Solver"

mod solver;

pub use solver::{
    AllSatConfig, AllSatIterator, AllSatOutcome, AllSatSolver, AllSatStats, Solution,
};
