// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Transition Power Abstraction (TPA) engine for CHC solving.
//!
//! TPA computes an over-approximation of the transition relation's transitive closure.
//! Instead of unrolling transitions step-by-step (like BMC), it abstracts multiple
//! transitions at once using power-of-two step bounds.
//!
//! # Algorithm Overview
//!
//! Given transition relation T, compute abstractions:
//! - T^{=n}: exactly 2^n steps
//! - T^{<n}: less than 2^n steps
//!
//! The algorithm checks reachability at increasing powers until:
//! - A counterexample is found (UNSAFE)
//! - A fixed point is detected (SAFE)
//!
//! When reachability queries return UNSAT, interpolation strengthens the abstractions.
//! When SAT, the path is recursively verified by splitting at midpoints.
//!
//! # References
//!
//! - "Transition Power Abstraction for Deep Counterexample Detection" (TACAS 2023)
//!   <https://arxiv.org/abs/2208.08100>
//! - Golem CHC solver: reference/golem/src/engine/TPA.cc
//!
//! Part of #958

mod freshen;
mod model;
mod power;
mod reachability;
mod solver;

pub(crate) use solver::TpaConfig;
pub(crate) use solver::{TpaResult, TpaSolver};
