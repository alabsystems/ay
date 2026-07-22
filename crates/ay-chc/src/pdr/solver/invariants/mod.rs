// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Invariant discovery module for PDR solver.
//!
//! This module contains the invariant discovery algorithms used by the PDR solver
//! to proactively find invariants before the main solving loop. These invariants
//! help PDR converge faster by providing initial lemmas.
//!
//! ## Module Structure
//!
//! Extracted invariant discovery modules:
//!
//! - `conditional_affine.rs` - Conditional affine invariants (parity-split kernels)
//! - `divisibility.rs` - Divisibility invariants (var mod k = c)
//! - `equality.rs` - Equality invariants (var_i = var_j)
//! - `parity.rs` - Parity helpers (var mod 2 constraints)
//! - `relational.rs` - Relational invariants (var_i <= var_j)
//!
//! Remaining in sibling solver modules (not yet extracted):
//!
//! - `invariant_discovery.rs` - Parity, conditional, counting, step-bounded
//! - `expr.rs` - Sum, affine, difference, scaled invariants
//! - `algebraic.rs` - Preservation helpers
//!
//! ## Discovery Algorithm Overview
//!
//! Invariant discovery is orchestrated within `PdrSolver::solve()` which runs:
//!
//! 1. **Startup Fixpoint Loop** (iterates until convergence):
//!    - Bound invariants
//!    - Fact clause conjunct invariants
//!    - Joint init shifted lower bounds
//!    - Multi-linear invariants
//!    - Equality invariants
//!    - Error-implied invariants
//!
//! 2. **Post-Fixpoint Discovery** (runs once):
//!    - Sum invariants
//!    - Affine invariants
//!    - Triple sum invariants
//!    - Difference invariants
//!    - Scaled difference/sum invariants
//!    - Parity invariants
//!    - Conditional parity invariants
//!    - Conditional invariants
//!    - Relational invariants
//!    - Step-bounded difference invariants
//!    - Counting invariants
//!
//! ## References
//!
//! - Golem's Spacer implementation uses similar proactive discovery
//! - Z3 Spacer uses "underApprox" for related functionality

mod conditional_affine;
mod divisibility;
mod equality;
mod parity;
mod propagation;
mod relational;

/// Maximum number of canonical variables per predicate for O(V^2+) discovery.
/// Predicates with more variables than this skip pairwise/triple enumeration
/// to prevent quadratic/cubic blowup on wide predicates (e.g., BvToBool-expanded).
pub(super) const MAX_PAIRWISE_DISCOVERY_VARS: usize = 30;

pub(super) use conditional_affine::discover_conditional_affine_invariants;
pub(super) use divisibility::{discover_divisibility_patterns, extract_variable_values};
#[cfg(test)]
pub(super) use parity::parity_mod2_opposite_blocking;
pub(super) use parity::{extract_negated_parity_constraint, extract_parity_constraint};
