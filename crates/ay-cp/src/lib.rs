// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![forbid(unsafe_code)]

//! AY-CP: Lazy Clause Generation CP-SAT solver
//!
//! A constraint programming solver built on ay's CDCL SAT engine using
//! Lazy Clause Generation (LCG). Integer variables are encoded as SAT
//! literals (order encoding), and constraint propagators explain their
//! inferences via clauses, enabling full CDCL conflict analysis.
//!
//! # Architecture
//!
//! ```text
//!                  ┌────────────────────────────┐
//!                  │     Constraint Model        │
//!                  │  (FlatZinc / direct API)    │
//!                  └──────────┬─────────────────┘
//!                             │
//!                  ┌──────────▼─────────────────┐
//!                  │     ay-cp Engine            │
//!                  │  ┌─────────────────────┐   │
//!                  │  │  IntegerTrail        │   │
//!                  │  │  (bound changes +    │   │
//!                  │  │   explanations)      │   │
//!                  │  └─────────────────────┘   │
//!                  │  ┌─────────────────────┐   │
//!                  │  │  IntegerEncoder      │   │
//!                  │  │  (int var ↔ SAT lit  │   │
//!                  │  │   lazy mapping)      │   │
//!                  │  └─────────────────────┘   │
//!                  │  ┌─────────────────────┐   │
//!                  │  │  Propagators         │   │
//!                  │  │  (alldiff, linear,   │   │
//!                  │  │   table, cumul, ...) │   │
//!                  │  └─────────────────────┘   │
//!                  └──────────┬─────────────────┘
//!                             │ Extension trait
//!                  ┌──────────▼─────────────────┐
//!                  │     ay-sat CDCL Engine      │
//!                  │  (conflict analysis,        │
//!                  │   clause learning,           │
//!                  │   restarts, VSIDS)           │
//!                  └────────────────────────────┘
//! ```
//!
//! # Key Design Decisions
//!
//! - **Order encoding**: Integer variable `x ∈ [lb..ub]` is represented by
//!   Boolean literals `[x >= lb+1], [x >= lb+2], ..., [x >= ub]`.
//!   The value of x is determined by the highest true `[x >= v]` literal.
//!   This encoding enables efficient bounds propagation via unit propagation.
//!
//! - **Lazy literal creation**: Literals are created on demand. A variable
//!   `x ∈ [0..1_000_000]` doesn't need 1M SAT variables upfront — only
//!   the bounds actually referenced by propagators get SAT variables.
//!
//! - **Explainable propagation**: Every domain reduction must produce an
//!   explanation (a clause). This enables ay-sat's conflict analysis to
//!   learn nogoods that generalize beyond the current search branch.
//!
//! # References
//!
//! - Ohrimenko, Stuckey, Codish. "Propagation = Lazy Clause Generation" (CP 2007)
//! - Feydy, Stuckey. "Lazy Clause Generation Reengineered" (CP 2009)
//! - Stuckey. "Lazy Clause Generation: Combining the Power of SAT and CP" (CPAIOR 2010)
//! - OR-Tools CP-SAT: github.com/google/or-tools (ortools/sat/integer.h)
//! - Chuffed: github.com/chuffed/chuffed (MIT, reference LCG implementation)
//! - Pumpkin: github.com/ConSol-Lab/Pumpkin (MIT, Rust LCG solver)

pub mod domain;
pub mod encoder;
pub mod engine;
pub(crate) mod heap;
pub mod propagator;
pub mod search;
pub mod trail;
pub mod variable;

// Propagator implementations
pub mod propagators;

// Re-exports
pub use domain::{Domain, DomainCreationError, DomainEnumerationError};
pub use encoder::IntegerEncoder;
pub use engine::CpSatEngine;
pub use propagator::{Explanation, PropagationResult, Propagator};
pub use search::{SearchStrategy, ValueChoice};
pub use trail::IntegerTrail;
pub use variable::{IntVarId, IntVariable};
