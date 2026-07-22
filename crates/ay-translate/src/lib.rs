// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![forbid(unsafe_code)]

//! # ay-translate: Unified term translation for ay consumers
//!
//! This crate provides a common translation layer for consumers of ay (private downstream consumers).
//! It reduces code duplication by extracting shared patterns:
//!
//! - `TranslationSession<V>`: Borrowed session combining solver ref + state (preferred)
//! - `TranslationState<V>`: Reusable variable/function caches (no solver dependency)
//! - `TranslationContext<V>`: Owning compatibility wrapper (deprecated — use Session + State)
//! - `TranslationHost<V>`: Shared host trait for owning and borrowed translation
//! - `SortTranslator` trait: Map consumer sort types to ay sorts
//! - `TermTranslator` trait: Recursive term translation
//! - `ops` module: Pre-built operator builders (arith, bv, array, etc.)

mod context;
pub mod ops;
mod sort;
mod term;

pub use context::{
    TranslationContext, TranslationHost, TranslationSession, TranslationState, TranslationTermHost,
};
pub use sort::SortTranslator;
pub use term::TermTranslator;

// Re-export ay-dpll Solver API types for consumer convenience.
// Consumers should depend only on ay-translate; these re-exports provide
// the full Solver-level type surface without a direct ay-dpll dependency.
pub use ay_dpll::api::{
    ArraySort, BitVecSort, DatatypeConstructor, DatatypeField, DatatypeSort, FpSpecialKind,
    FuncDecl, Logic, Model, ModelValue, SolveDetails, SolveResult, Solver, SolverError, Sort, Term,
    TermKind, VerificationLevel, VerificationSummary, VerifiedModel, VerifiedSolveResult,
};

// Re-export executor-level types needed by SMT-LIB text consumers
pub use ay_dpll::{CounterexampleStyle, Executor, ExecutorError, Statistics, UnknownReason};

// Re-export explainability and incremental types (#8153, #8154)
pub use ay_dpll::api::{
    AnnotatedCoreLiteral, AnnotatedUnsatCore, AssignmentReason, CongruenceReason, CongruenceStep,
    IncrementalCoreEvolution, ModelProvenance, SmtProofCertificate, TheoryAttribution,
    VariableProvenance,
};
