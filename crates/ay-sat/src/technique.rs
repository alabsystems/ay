// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Canonical enum of independently-disablable SAT techniques.
//!
//! Compile-time contract:
//! - Adding a variant auto-adds it to `ay solve --disable <TECHNIQUE>` CLI help.
//! - [`crate::Solver::disable_technique`] uses exhaustive match — omitting a
//!   handler is a compile error.
//! - Removing a variant breaks both CLI and solver — intentional.

/// Every independently-disablable SAT preprocessing/inprocessing technique.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "cli", derive(clap::ValueEnum))]
#[cfg_attr(feature = "cli", clap(rename_all = "kebab-case"))]
pub enum SatTechnique {
    /// All preprocessing passes.
    Preprocess,
    /// Bounded variable elimination.
    Bve,
    /// Failed literal probing.
    Probe,
    /// Congruence closure (gate-based).
    Congruence,
    /// SCC-based formula decomposition.
    Decompose,
    /// Equivalence sweeping (SAT sweeping).
    Sweep,
    /// Clause conditioning.
    Condition,
    /// Clause vivification.
    Vivify,
    /// Subsumption elimination.
    Subsume,
    /// Blocked clause elimination.
    Bce,
    /// Covered clause elimination.
    Cce,
    /// Transitive reduction.
    Transred,
    /// Hyper ternary resolution.
    Htr,
    /// Gate extraction.
    Gate,
    /// Clause factoring.
    Factor,
    /// Structured BVA.
    Sbva,
    /// Clause shrinking.
    Shrink,
    /// Fast elimination (lightweight BVE).
    Elimfast,
    /// All inprocessing (master switch).
    Inprocess,
    /// Flip-based local search.
    Flip,
    /// SAT native-code helper compilation.
    Jit,
    /// external code generation compilation backend.
    ExternalCodegenBackend,
    /// Random walk / local search.
    Walk,
    /// Search warmup phase.
    Warmup,
    /// Signed (literal-level) symmetry search (B2: CLI opt-out replacing the
    /// retired env gate; the route itself remains opt-in pending its default
    /// decision).
    SymmetrySigned,
    /// Aux-free pigeonhole SR refutation route (default ON; this is its
    /// opt-out).
    SymmetryAuxfree,
    /// Orbitope symmetry route (default ON; this is its opt-out).
    SymmetryOrbitope,
}
