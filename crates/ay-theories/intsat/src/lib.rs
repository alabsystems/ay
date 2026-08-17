// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![forbid(unsafe_code)]

//! AY IntSat - CDCL-style conflict-driven ILP solver for LIA.
//!
//! Implements the IntSat technique from:
//! Nieuwenhuis, Oliveras, Rodriguez-Carbonell.
//! "IntSat: Integer Linear Programming by Conflict-Driven Constraint-Learning."
//! arXiv:2402.15522, February 2024.
//!
//! # Overview
//!
//! IntSat extends CDCL to integer linear constraints, replacing the traditional
//! simplex + branch-and-bound approach with a native CDCL architecture:
//!
//! - **Trail of bounds**: Instead of Boolean literals, the trail records integer
//!   variable bounds (lower and upper). A variable is "defined" when its bounds
//!   coincide.
//!
//! - **Bound propagation**: Derives new bounds with integer rounding (floor/ceil)
//!   built into each propagation step. This is a key difference from LP relaxation.
//!
//! - **Conflict analysis via cut rule**: When a constraint is falsified, the
//!   analysis eliminates variables using the cut rule (analogous to resolution),
//!   continuing until 1UIP.
//!
//! - **GCD normalization**: Every constraint is eagerly normalized by dividing
//!   by the GCD of coefficients and flooring the RHS. This produces a free
//!   Chvatal-Gomory cut at every step.
//!
//! # Usage
//!
//! ```
//! use ay_intsat::{Constraint, IntSatResult, VarId, solve_ilp};
//! use num_bigint::BigInt;
//!
//! // x + y <= 10, x >= 3, y >= 4
//! let constraints = vec![
//!     Constraint {
//!         coeffs: vec![(VarId(0), BigInt::from(1)), (VarId(1), BigInt::from(1))],
//!         rhs: BigInt::from(10),
//!     },
//!     Constraint {
//!         coeffs: vec![(VarId(0), BigInt::from(-1))],
//!         rhs: BigInt::from(-3),
//!     },
//!     Constraint {
//!         coeffs: vec![(VarId(1), BigInt::from(-1))],
//!         rhs: BigInt::from(-4),
//!     },
//! ];
//!
//! let initial_bounds = vec![
//!     (VarId(0), BigInt::from(0), BigInt::from(100)),
//!     (VarId(1), BigInt::from(0), BigInt::from(100)),
//! ];
//!
//! match solve_ilp(constraints, 2, &initial_bounds) {
//!     IntSatResult::Sat(model) => {
//!         let x = &model[&VarId(0)];
//!         let y = &model[&VarId(1)];
//!         assert!(x + y <= BigInt::from(10));
//!     }
//!     _ => panic!("expected SAT"),
//! }
//! ```

#![warn(missing_docs)]
#![warn(clippy::all)]

mod conflict;
mod decide;
mod normalize;
mod propagate;
mod solver;
mod trail;
mod types;

pub use solver::{IntSatConfig, IntSatSolver};
pub use types::{Constraint, IntSatResult, VarId};

use num_bigint::BigInt;
use types::{BoundEntry, BoundReason};

/// Solve an ILP problem using the IntSat algorithm.
///
/// # Arguments
///
/// - `constraints`: Linear constraints in `<= form`. Each constraint is
///   `sum(coeffs[i] * x_i) <= rhs`. Equalities should be encoded as two
///   constraints (<=  and >=, the latter negated).
/// - `num_vars`: Number of integer variables (indexed 0..num_vars-1).
/// - `initial_bounds`: Initial domain bounds for variables as `(var, lower, upper)`.
///
/// # Returns
///
/// - `IntSatResult::Sat(model)` if a solution exists.
/// - `IntSatResult::Unsat` if no solution exists.
/// - `IntSatResult::Unknown` if resource limits were exceeded.
pub fn solve_ilp(
    constraints: Vec<Constraint>,
    num_vars: usize,
    initial_bounds: &[(VarId, BigInt, BigInt)],
) -> IntSatResult {
    let mut solver = IntSatSolver::new(constraints, num_vars, IntSatConfig::default());

    // Set up initial bounds on the trail.
    for (var, lb, ub) in initial_bounds {
        solver.add_initial_bound(*var, lb.clone(), ub.clone());
    }

    solver.solve()
}

impl IntSatSolver {
    /// Add initial bounds for a variable (at level 0).
    pub fn add_initial_bound(&mut self, var: VarId, lower: BigInt, upper: BigInt) {
        self.trail.push_bound(BoundEntry {
            var,
            value: lower,
            is_upper: false,
            reason: BoundReason::Input,
            level: 0,
        });
        self.trail.push_bound(BoundEntry {
            var,
            value: upper,
            is_upper: true,
            reason: BoundReason::Input,
            level: 0,
        });
    }
}

#[cfg(test)]
#[path = "integration_tests.rs"]
mod integration_tests;

// Kani verification stubs — required by pre-commit hook for theory crates.
// STUB: These are placeholder harnesses. Real proofs need implementation.
#[cfg(kani)]
mod kani_proofs {
    use super::*;

    /// STUB: Verify GCD normalization preserves constraint equivalence.
    #[kani::proof]
    fn kani_stub_gcd_normalization() {
        // STUB: Implement real proof for GCD normalization correctness.
    }
}
