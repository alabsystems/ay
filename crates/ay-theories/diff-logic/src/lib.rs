//! `ay-diff-logic` — an incremental difference-logic (QF_IDL / QF_RDL) decision
//! procedure.
//!
//! This crate is a **standalone, self-certifying** difference-logic engine. It
//! is deliberately *not* wired into the AY dispatcher, logic detection, or
//! `check_sat_assuming` (Phase 5 increment 1 is the engine only; integration is
//! a later increment). Soundness is the priority: a wrong sat/unsat is the worst
//! outcome, so every verdict is self-certified with always-on `debug_assert!`s
//! and the test suite cross-checks random systems against the `z3` oracle.
//!
//! # What is difference logic?
//!
//! Atoms have the shape `x − y ⋈ c` (a difference of two variables vs a
//! constant), with `⋈ ∈ {<=, <, =, >=, >}`. QF_IDL uses integer constants,
//! QF_RDL rationals. The decision procedure encodes each `x − y <= c` as a
//! graph edge `y → x : c`; the system is **unsatisfiable iff the graph has a
//! negative-weight cycle**, and otherwise the shortest-path *potentials* form a
//! satisfying model.
//!
//! # Layout
//!
//! - [`weight`] — the [`Weight`]/[`IntWeight`] traits and `i64`/`BigInt`/
//!   `BigRational` instances.
//! - [`rstar`] — `ℚ[ε]`, the rational+infinitesimal group used to make strict
//!   RDL constraints exact.
//! - [`atom`] — the [`DiffAtom`] struct and the *fail-closed* atom→edge
//!   translation (see the table in that module).
//! - [`graph`] — [`DiffGraph`], `add_constraint`, and the Bellman-Ford check
//!   with negative-cycle extraction and self-certification.
//! - [`builder`] — `from_atoms`-style entry points returning a verdict + model.
//!
//! # Soundness guarantees
//!
//! - **SAT self-cert:** before returning a model the engine substitutes it into
//!   *every* stored constraint and `debug_assert!`s each holds.
//! - **UNSAT self-cert:** before returning a cycle the engine re-walks it,
//!   checks contiguity/closure, and `debug_assert!`s its summed weight `< 0`.
//! - **Fail-closed parsing:** any atom that is not a pure two-variable (or
//!   var-vs-const) difference constraint causes the whole system to be rejected
//!   rather than mis-modeled.

// This crate contains no `unsafe`; make that a compiler-enforced invariant
// (matches the sibling theory crates that already forbid it).
#![forbid(unsafe_code)]

pub mod atom;
pub mod builder;
pub mod graph;
pub mod rstar;
pub mod weight;

pub use atom::{DiffAtom, Negate, Op};
pub use builder::{solve_int_atoms, solve_rational_atoms, BuildResult};
pub use graph::{DiffGraph, DiffResult, GraphEdge};
pub use rstar::RStar;
pub use weight::{IntWeight, Weight};
