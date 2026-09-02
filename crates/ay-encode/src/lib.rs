// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

#![forbid(unsafe_code)]

//! `ay-encode` — the single shared AY-interface crate.
//!
//! This is the *one* crate that both **model-checker-consumer** (Rust MIR model checker) and
//! **ty** (TLA+ model checker) consume to talk to the AY solver. It exists so
//! the two projects share exactly one copy of:
//!
//! 1. the **sort/term builder** surface over [`ay_bindings`] (Bool/Int/BV/
//!    Array/Datatype) *plus* first-class wrappers for AY's native
//!    `Seq` / `Set` / `Map` / `String` theories — the encoders ty currently
//!    hand-rolls (`sequence_encoder`, `finite_set`, `function_encoder`, string
//!    interning) and that model-checker-consumer lowers ad-hoc;
//! 2. one **invocation config** ([`invoke::EncodeConfig`]) + a runner that
//!    drives [`ay_chc::AdaptivePortfolio`] / [`ay_chc::engines::solve_pdr_proof`];
//! 3. a **frontend-neutral verdict** ([`verdict::AyVerdict`]) that normalizes
//!    AY's `Safe` / `Unsafe` / `Unknown` into one type both projects map from;
//! 4. a **proof hook** ([`proof::Certificate`]) to obtain AY's re-checkable
//!    evidence (CHC proof transcript, and optionally a SAT-level Alethe cert).
//!
//! ## What stays per-project
//!
//! Everything *above* the obligation boundary stays in each frontend:
//!
//! - **model-checker-consumer** keeps `MIR -> BmcVc / ChcVc` lowering (`codegen_ay`), its
//!   `ay_violation_<label>_<N>` BMC naming convention, and its result→`kani`
//!   reporting. It calls into this crate to build the [`ay_bindings::AYProgram`]
//!   / [`ay_chc::ChcProblem`] and to invoke + normalize.
//! - **ty** keeps `TLA+ -> TlaSort / TlaExpr` translation, its BMC/k-induction
//!   driver state, and its record/powerset encoders (genuinely TLA-specific).
//!   It calls into this crate's term builders to replace the four hand-rolled
//!   theory encoders, and into [`invoke`]/[`verdict`] for the portfolio + PDR.
//!
//! In short: **frontend IR → obligations is per-project; obligations → AY is
//! shared here.** This crate intentionally has *no* knowledge of MIR or TLA+.
//!
//! ## Status
//!
//! This is the foundation skeleton. Public types and signatures are real and
//! compile; capabilities that depend on the full port return typed
//! [`EncodeError::Unimplemented`] errors and are flagged in their doc comments.
//! No frontend code is migrated here yet.

pub mod invoke;
pub mod proof;
pub mod sorts;
pub mod terms;
pub mod verdict;

#[cfg(test)]
mod tests;

// ---------------------------------------------------------------------------
// Re-exports: the canonical AY types, surfaced once so neither frontend has to
// depend on `ay-bindings` / `ay-chc` directly for the common path.
// ---------------------------------------------------------------------------

/// The typed builder surface from [`ay_bindings`].
///
/// Both frontends build their obligations out of these. Re-exported here so a
/// consumer can depend on `ay-encode` alone for the common encoding path.
pub use ay_bindings::{
    AYProgram, Constraint, DatatypeConstructor, DatatypeField, DatatypeSort, Expr, ExprValue,
    ProgramBuilder, Sort, SortError, SortInner,
};

/// Structure-preserving expression rebuild from [`ay_bindings`].
///
/// model-checker-consumer-core's CHC simplification passes (`chc_const_prop_subst`,
/// `chc_normalize_free_arrays`) rewrite an [`Expr`] tree bottom-up and call this
/// to re-form a node from its (possibly rewritten) children while keeping the
/// node's operator/metadata. Re-exported (G7) so model-checker-consumer-core can depend on
/// `ay-encode` alone instead of `ay-bindings` for the common encoding path.
pub use ay_bindings::rebuild_with_children;

/// The CHC problem model + portfolio surface from [`ay_chc`].
///
/// Re-exported for consumers that hand-build a [`ay_chc::ChcProblem`] (model-checker-consumer's
/// typed lowering, the model-checker consumer's `ChcTranslator`) rather than going through SMT-LIB text.
pub use ay_chc::{
    AdaptiveConfig, AdaptiveExecutionMode, AdaptivePortfolio, AdaptiveSolveReport,
    AdaptiveSolveTrace, AdaptiveStrategyObservation, AdaptiveStrategyOutcome, BudgetPolicy,
    CancellationToken, ChcError, ChcExpr, ChcOp, ChcParser, ChcProblem, ChcQueryObligation,
    ChcQueryObligationId, ChcSort, ChcVar, EngineType, HornClause, PredicateId, SmtValue,
    VerifiedChcResult, MAX_BITVECTOR_WIDTH,
};

/// The content-addressed CHC normalization helpers from [`ay_chc`].
///
/// model-checker-consumer's typed CHC/PDR path uses `normalized_chc_input(&problem)` for its
/// content-addressed cache key and obligation-hash cross-check, and the sha256
/// variant for the proof-run manifest binding (G6). Re-exported so the typed
/// lowering can stay on `ay-encode` alone.
pub use ay_chc::{normalized_chc_input, normalized_chc_input_sha256};

/// Proof-run transcript/artifact types from [`ay_chc`] (G5/G6).
///
/// [`crate::proof::Certificate`] wraps [`ChcProofRunArtifacts`] (the model +
/// replay-transcript artifact bundle) and [`ChcProofTranscriptConsumerEvidence`].
/// These are re-exported so a consumer can use immutable artifact
/// `schema`/`role`/`digest`/`bytes` accessors (G5) and read the proof-run
/// metadata JSON + `normalized_input_sha256` + `proof_status` accessors (G6)
/// without depending on `ay-chc` directly.
pub use ay_chc::{
    ChcPdrProofRun, ChcProofArtifactDigest, ChcProofRunArtifact, ChcProofRunArtifacts,
    ChcProofRunStopReason, ChcProofRunWithBudgetReport, ChcProofTranscriptConsumerEvidence,
    ChcProofTranscriptMetadata,
};

/// Portfolio observability types from [`ay_chc`] (G8, optional).
///
/// Re-exported so consumers can read authoritative whole-run timing and, when
/// driving a concrete `PortfolioSolver` directly, compare per-engine
/// [`EngineStopReason`] values structurally instead of via Debug strings. These
/// feed diagnostics only (not verdicts); adaptive proof reports intentionally
/// leave per-engine entries empty because specialized routes are represented
/// by [`AdaptiveSolveTrace`] instead of inaccurate concrete-engine identities.
pub use ay_chc::{BudgetReport, EngineStopReason};

/// Convenience alias: every public fallible op in this crate returns this.
pub type Result<T> = std::result::Result<T, EncodeError>;

/// Errors raised while encoding or invoking through this crate.
///
/// Frontends collapse these into their own diagnostics. We keep the variants
/// coarse on purpose — fine-grained AY errors live in [`ay_chc::error`] and
/// [`ay_bindings::SortError`] and are wrapped here rather than re-modeled.
#[derive(Debug)]
#[non_exhaustive]
pub enum EncodeError {
    /// A term/sort builder produced an ill-sorted expression.
    Sort(SortError),
    /// The AY CHC layer (parse / portfolio / PDR) failed.
    Chc(ChcError),
    /// The AY solver panicked with an AY-classified internal panic (G3).
    ///
    /// Carries AY's panic reason string. Programmer-error panics (non-AY) are
    /// *not* captured here — they re-propagate so they surface as real bugs.
    SolverPanicked(String),
    /// The caller cancelled an obligation before its solve was started.
    Cancelled,
    /// A feature was requested that this skeleton has not implemented yet.
    Unimplemented(&'static str),
}

impl std::fmt::Display for EncodeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Sort(e) => write!(f, "ay-encode sort error: {e}"),
            Self::Chc(e) => write!(f, "ay-encode chc error: {e}"),
            Self::SolverPanicked(reason) => write!(f, "ay-encode: solver panicked: {reason}"),
            Self::Cancelled => write!(f, "ay-encode: solve cancelled by caller"),
            Self::Unimplemented(what) => write!(f, "ay-encode: not yet implemented: {what}"),
        }
    }
}

impl std::error::Error for EncodeError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        match self {
            Self::Sort(e) => Some(e),
            Self::Chc(e) => Some(e),
            Self::SolverPanicked(_) => None,
            Self::Cancelled => None,
            Self::Unimplemented(_) => None,
        }
    }
}

impl From<SortError> for EncodeError {
    fn from(e: SortError) -> Self {
        Self::Sort(e)
    }
}

impl From<ChcError> for EncodeError {
    fn from(e: ChcError) -> Self {
        Self::Chc(e)
    }
}
