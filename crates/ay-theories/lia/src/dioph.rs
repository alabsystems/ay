// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Diophantine equation solver with variable elimination.
//!
//! Implements Griggio's algorithm from Z3 for directly solving systems of
//! linear integer equations. This is much more efficient than iterative
//! cutting planes for equality-dense problems.
//!
//! Reference:
//! - Z3: `src/math/lp/dioph_eq.cpp`
//! - Paper: "A Practical Approach to SMT Linear Integer Arithmetic" (Griggio)

mod bound_analysis;
mod elimination;
mod equation;
mod solver;

pub(crate) use equation::IntEquation;
pub(crate) use solver::{DiophResult, DiophSolver};

#[allow(clippy::panic)]
#[cfg(test)]
mod tests;
