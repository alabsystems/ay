// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Andrew Yates <andrewyates.name@gmail.com>
// Dedicated executable-memory/ABI boundary; unsafe sites are locally audited.
#![allow(unsafe_code)]
#![deny(unsafe_op_in_unsafe_fn)]

//! # ay-jit: JIT compilation infrastructure for the ay SMT solver
//!
//! This crate provides native machine code generation for performance-critical
//! solver hot paths: SAT inprocessing (conflict analysis, minimization,
//! subsumption), theory bound propagation, simplex pivot updates, and CHC
//! expression evaluation.
//!
//! ## Module map
//!
//! ### SAT inprocessing JIT (production, used by ay-sat)
//!
//! - [`conflict_jit`] -- JIT-compiled 1UIP conflict literal processing.
//! - [`minimize_jit`] -- JIT-compiled conflict clause minimization.
//! - [`simd_inprocess`] -- SIMD batch literal scanning for subsumption/BCE.
//! - [`batch`] -- BV bit-blasting batch clause compilation.
//! - [`learned_clause_emit`] -- Profile-only learned-clause descriptor contract;
//!   native SAT dispatch is disabled.
//! - [`batch_recompile`] -- Scheduler for selecting hot learned clauses for
//!   profile extraction.
//! - [`deletion_hook`] -- Inert deletion/mutation scaffold for any future
//!   gated learned-clause runtime experiment.
//!
//! ### Theory JIT (production, used by ay-theories and ay-dpll)
//!
//! - [`theory_prop`] -- Interpreted fast-path for LRA/LIA bound propagation.
//! - [`theory_prop_native`] -- Native machine code for bound propagation.
//! - [`theory_dispatch`] -- O(1) theory atom dispatch table for DPLL(T).
//! - [`simplex_jit`] -- JIT-compiled simplex pivot row updates and sparse substitutes.
//! - [`lra_region`] -- Metadata-only basis-local LRA compiled-region foundation.
//! - [`expr_eval`] -- JIT-compiled CHC expression evaluation (used by ay-chc).
//!
//! ### Platform assemblers (`pub(crate)`)
//!
//! - `aarch64` -- Apple Silicon native assembler.
//! - `x86_64` -- x86-64 native assembler.
//!
//! ### Infrastructure
//!
//! - `compiler_service` -- Asynchronous solver-program scheduling service.
//! - `executable` -- Executable memory allocation via mmap/MAP_JIT.
//! - `solver_program_runtime` -- Metadata-only install/apply guard contract for compiled regions.
//!
//! ## Integration with the solver
//!
//! **ay-dpll** uses [`TheoryDispatchTable`] for O(1) theory atom dispatch
//! during BCP, replacing HashMap lookups.
//!
//! **ay-theories** (LRA) uses [`TheoryPropJit`] and [`NativeVarPropagator`]
//! for fast bound propagation, and [`PivotRowCache`] for compiled simplex pivots.
//!
//! **ay-chc** uses [`expr_eval::compile_expr`] for JIT-compiled expression
//! evaluation in the implication cache.

pub mod batch;
pub mod batch_recompile;
pub mod code_cache;
#[allow(dead_code)] // #8875 foundation: integration wiring lands in follow-up lanes
pub(crate) mod compiler_service;
pub mod conflict_jit;
pub mod context;
pub mod deletion_hook;
pub mod expr_eval;
pub mod guards;
pub mod learned_clause_emit;
#[allow(dead_code)] // #8876 foundation: production wiring lands in follow-up lanes
pub mod lra_region;
pub mod minimize_jit;
pub mod theory_dispatch;
pub mod theory_prop;
pub mod theory_prop_native;
// SIMD batch literal scanning for inprocessing (subsumption, BCE, vivification).
#[cfg(target_arch = "aarch64")]
#[allow(dead_code)]
#[allow(unreachable_pub)]
pub(crate) mod aarch64;
pub(crate) mod executable;
pub mod simd_inprocess;
pub mod simplex_jit;
#[allow(dead_code)] // #8874 foundation: consumed by the upcoming #8875 async tier
pub(crate) mod solver_program;
#[allow(dead_code)] // #8877 foundation: production solver integration lands in follow-up lanes
pub(crate) mod solver_program_runtime;
#[allow(dead_code)] // #8526 foundation: verifier integration lands in later slices
pub mod superopt;
pub mod tier_controller;
// Kept with zero lib.rs-side consumers (the BCP-emitter chain that used it was
// deleted per #8517): tests/x86_64_encoder_regression.rs includes the source
// directly via #[path], so the module must keep compiling.
#[cfg(target_arch = "x86_64")]
#[allow(dead_code)]
#[allow(unreachable_pub)]
pub(crate) mod x86_64;

// Retired SAT propagation compiler integration tests (tests.rs) removed in #8517.

pub mod pgo;
pub use batch::{BvBatchStats, BvClauseBatch, BvGateCompiler, BvGateDesc, BvGateType};
pub use batch_recompile::{
    BatchRecompileBudget, ClauseId, LearnedClauseMeta, RecompileBatchOutcome, RecompileScheduler,
};
pub use code_cache::{CacheSlot, CodeCacheManager, CodeCacheStats, DEFAULT_CODE_CACHE_BUDGET};
pub use context::PropagationContext;
pub use guards::ClauseGuards;
pub use learned_clause_emit::{
    emit_learned_clause, CodegenContext as LearnedClauseCodegenContext, LearnedClausePropagator,
    LitValue as LearnedLitValue, Literal as LearnedLiteral, PropagatorResult,
    Trail as LearnedTrail,
};
pub use lra_region::{
    LraBasisRegionProfileKey, LraBasisRegionRequest, LraBasisRegionRuntimeEvidence,
    LraBasisRegionRuntimePayload, LraBasisRegionRuntimeRow, LraRegionCompileTiming,
    LraRegionEligibilityRejection, LraRegionEpochs, LraRegionGuardMetadata,
    LraRegionInvalidationKey, LraRegionNeighborhood, LraRegionNeighborhoodKind, LraRegionRowShape,
    LRA_BASIS_REGION_SEMANTIC_VERSION, LRA_BASIS_REGION_STATS_PREFIX,
};
pub use pgo::{HeatClass, PgoProfile, DEFAULT_PGO_CONFLICT_THRESHOLD};
pub use simplex_jit::{
    batch_pivot_update_i64, compile_batch_pivot_update, CompiledBatchPivotUpdate, CompiledPivotRow,
    PivotRowCache, COMPILE_THRESHOLD,
};
pub use solver_program::{
    SolverProgramLraBasisRegionStats, SolverProgramLraSparseSubstituteStats,
    SolverProgramProfileToggles, SolverProgramStableStats,
    SOLVER_PROGRAM_STABLE_STATS_SCHEMA_VERSION,
};
pub use theory_dispatch::{TheoryAtomEntry, TheoryDispatchResult, TheoryDispatchTable};
pub use theory_prop::{
    BoundAtom, PropagationResult, SmallBound, TheoryPropFingerprint, TheoryPropJit, VarPropagator,
    NATIVE_COMPILE_THRESHOLD,
};
pub use theory_prop_native::{compile_native_propagators, NativeVarPropagator};
pub use tier_controller::{
    CompilationTier, FormulaProfile, TierController, TierPromotion, TierThresholds,
};

/// Compatibility gate for an unavailable development backend.
///
/// Public snapshots always return `true`, keeping every dependent solver
/// path on its supported fallback implementation.
#[doc(hidden)]
#[inline]
pub fn no_external_codegen_backend_cached() -> bool {
    true
}

/// Error type for JIT compilation failures.
#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
pub enum JitError {
    #[error("No native ISA available for this platform")]
    NoNativeIsa,

    #[error("mmap failed: could not allocate executable memory")]
    MmapFailed,

    #[error("JIT backend error: {0}")]
    BackendError(String),

    /// An external compiler call panicked. Baseline code continues to run
    /// correctly; this only means an optimistic native-code compile was lost.
    /// We surface it as a typed error so tier controllers and tests can
    /// observe the failure.
    #[error("JIT backend compilation panicked: {0}")]
    BackendPanic(String),
}
