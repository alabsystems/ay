#![forbid(unsafe_code)]
#![warn(missing_docs)]
// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Maximum Satisfiability (MAX-SAT) solver
//!
//! MAX-SAT finds an assignment that maximizes the number (or weight) of
//! satisfied clauses in a CNF formula.
//!
//! ## Problem Variants
//!
//! - **Unweighted MAX-SAT**: Maximize the count of satisfied clauses
//! - **Weighted MAX-SAT**: Maximize the sum of weights of satisfied clauses
//! - **Partial MAX-SAT**: Some clauses are "hard" (must be satisfied), others are "soft"
//! - **Weighted Partial MAX-SAT**: Combination of weighted and partial
//!
//! ## Example
//!
//! ```
//! use ay_maxsat::{MaxSatSolver, MaxSatResult};
//!
//! let mut solver = MaxSatSolver::new();
//!
//! // Add soft clauses (can be violated at a cost)
//! solver.add_soft_clause(vec![1], 1);   // prefer x1 = true
//! solver.add_soft_clause(vec![-1], 1);  // prefer x1 = false (conflicts!)
//! solver.add_soft_clause(vec![2], 1);   // prefer x2 = true
//!
//! let result = solver.solve();
//! match result {
//!     MaxSatResult::Optimal { model, cost } => {
//!         // Cost = 1 (one soft clause violated)
//!         assert_eq!(cost, 1);
//!     }
//!     _ => panic!("Expected optimal solution"),
//! }
//! ```
//!
//! ## Algorithm
//!
//! The engine (see [`crate::oll`] internals) is a core-guided OLL solver in
//! the style of the top exact solvers of recent MaxSAT Evaluations, running
//! on one persistent incremental [`ay_sat`] solver:
//!
//! 1. Selector literals per soft clause, assumed true in each SAT call;
//!    UNSAT cores raise a certified lower bound.
//! 2. Lazily extended totalizers count violations per core; weight
//!    splitting handles weighted instances; totalizer construction is
//!    delayed while disjoint cores accumulate; fresh totalizers are
//!    "exhausted" under a small budget to lift the bound further.
//! 3. Stratification (Boolean lexicographic optimization) activates
//!    high-weight selectors first; hardening turns softs that can no longer
//!    be violated into hard units.
//! 4. Preprocessing folds duplicate/tautological/complementary softs and
//!    intrinsic at-most-one groups (cliques over binary hard clauses).
//! 5. When the remainder is uniform-weight and the bound gap is large, a
//!    solution-improving descent (LSU) over one shared totalizer replaces
//!    core enumeration.
//!
//! ## References
//!
//! - Morgado et al., "Core-Guided MaxSAT with Soft Cardinality Constraints" (OLL)
//! - Ignatiev et al., "RC2: an Efficient MaxSAT Solver"
//! - Martins et al., "Incremental Cardinality Constraints for MaxSAT"
//! - Ansótegui et al., "SAT-based MaxSAT algorithms" (stratification, hardening)

mod dpw;
mod oll;
mod solver;

pub use ay_sat::SignedClause;
pub use oll::{PaidMinedCore, PaidSatCore};
pub use solver::{MaxSatResult, MaxSatSolver, MaxSatStats};
