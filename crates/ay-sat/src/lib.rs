// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![deny(unsafe_code)]
// SAT solvers use many domain acronyms (BCE, BVE, VSIDS, HTR, CDCL, etc.).
#![allow(clippy::upper_case_acronyms)]

//! AY SAT - CDCL SAT solver core
//!
//! A Conflict-Driven Clause Learning SAT solver using established techniques
//! from CaDiCaL and Kissat.
//!
//! ## Example
//!
//! ```rust
//! use ay_sat::{Literal, SatResult, Solver};
//!
//! let mut solver = Solver::new(0);
//! let x0 = solver.new_var();
//! let x1 = solver.new_var();
//!
//! assert!(solver.add_clause(vec![Literal::positive(x0)]));
//! assert!(solver.add_clause(vec![Literal::positive(x1)]));
//!
//! match solver.solve().into_inner() {
//!     SatResult::Sat(model) => {
//!         assert!(model[x0.index()]);
//!         assert!(model[x1.index()]);
//!     }
//!     other => panic!("unexpected result: {other:?}"),
//! }
//! ```
//!
//! ## Core CDCL Features
//! - 2-watched literal scheme for efficient unit propagation
//! - VSIDS/VMTF variable selection heuristics with decay
//! - 1UIP conflict analysis with recursive clause minimization
//! - Luby and glucose-style EMA restarts
//! - LBD-based tier clause management (core/mid/local)
//! - Chronological backtracking with lazy reimplication
//! - Phase saving
//!
//! ## Inprocessing Techniques
//! - Vivification (clause strengthening via propagation)
//! - Bounded variable elimination (BVE)
//! - Blocked clause elimination (BCE)
//! - Subsumption and self-subsumption
//! - Failed literal probing
//! - Hyper-ternary resolution (HTR)
//! - Block-level clause shrinking
//!
//! ## Advanced SAT Techniques
//! - Gate extraction (AND/XOR/ITE/EQUIV recognition)
//! - SAT sweeping (equivalent literal detection)
//! - Congruence closure (gate-based equivalence detection)
//! - Walk/ProbSAT local search
//! - Factorization, transitive reduction, SCC decomposition, conditioning
//! - Model reconstruction for equisatisfiable transformations
//!
//! ## Parallel Portfolio Solving
//! - Multiple solver configurations running in parallel
//! - Instance-aware strategy selection via SATzilla-style features
//! - Different restart policies (Luby, Glucose EMA)
//! - Configurable inprocessing strategies per thread
//! - First-result wins, others terminate via cooperative interruption
//! - CLI: `ay --parallel N file.cnf`
//!
//! ## Proof Generation
//! - DRAT proof output (text and binary formats)
//! - LRAT proof output with resolution hints (text and binary formats)
//! - Variable-length binary encoding for compact proofs

#![warn(missing_docs)]
#![warn(clippy::all)]
#![allow(
    clippy::doc_lazy_continuation,
    clippy::enum_variant_names,
    clippy::missing_fields_in_debug,
    clippy::never_loop,
    clippy::too_many_arguments,
    clippy::type_complexity
)]

// Import safe_eprintln! from ay-core (non-panicking eprintln replacement)
#[macro_use]
extern crate ay_core;

pub(crate) mod bce;
pub(crate) mod bve;
// Phase 1 of incremental BVE during search (#8795) lives inside `bve::` as
// `bve::incremental_cost` and `bve::trigger`. The previous standalone
// `bve_incremental` module was removed in #8808 because it was a parallel
// island with no CDCL hooks; the re-landed Phase 1 ships as sibling modules
// of the existing preprocessing BVE so Phase 2 can share clause-database
// accessors without another round of relocation.
pub(crate) mod cce;
// The two circuit_* modules below carry a module-level dead-code allow on
// purpose: they are audit/replay surfaces for the multiplier-equivalence
// pipeline whose entry points are driven by external tooling and env-gated
// paths, so large parts are intentionally retained while unused from the
// solver itself. Audited and kept pending the next dead-code cleanup slice
// (same convention as ay-chc's documented per-module allows).
#[allow(dead_code)]
pub mod circuit_equiv_packet;
#[allow(dead_code)]
pub(crate) mod circuit_scout;
pub(crate) mod clause;
pub(crate) mod clause_arena;
pub(crate) mod clause_provenance;
pub(crate) mod clause_trace;
pub(crate) mod component;
pub(crate) mod condition;
pub(crate) mod conflict;
pub(crate) mod congruence;
pub(crate) mod decision_trace;
pub(crate) mod decompose;
pub mod dense_clique;
pub(crate) mod determinism;
pub(crate) mod diagnostic_trace;
pub(crate) mod dimacs;
/// Shared DIMACS-family parser core for SAT/XOR/QBF format tokenization.
pub mod dimacs_core;
pub(crate) mod elim_heap;
pub mod er_proof;
pub(crate) mod extension;
pub(crate) mod factor;
/// Test-only `.xz` fixture decompression that skips gracefully when the system
/// `xz` tool is absent (see module docs).
#[cfg(test)]
mod test_xz;
/// Compile-time feature flag constants for downstream crate introspection.
///
/// Zero-cost: all values are `const bool` resolved at compile time via `cfg!()`.
pub mod feature_flags {
    /// CaDiCaL-exact raw pointer BCP enabled.
    pub const RAW_POINTER_BCP: bool = cfg!(feature = "raw-pointer-bcp");
    /// JIT-compiled BCP enabled (FC-SAT).
    pub const JIT: bool = cfg!(feature = "jit");
    /// GPU compute infrastructure enabled.
    pub const GPU: bool = cfg!(feature = "gpu");
}

/// Capacity limits of the clause-arena addressing scheme, exposed so callers
/// that build very large CNFs can refuse to import a formula the solver cannot
/// address soundly.
///
/// Clauses live in a single `Vec<u32>` arena and are referenced by their
/// **word offset** stored in a [`u32`] (`ClauseRef`). Watch entries keep the
/// binary-clause flag in a *separate* bit (bit 32 of a `u64` clause word, see
/// `watched::BINARY_FLAG`), so the flag no longer aliases the offset and the
/// whole 32-bit offset space is addressable (#9670). The arena must still stay
/// strictly below [`MAX_ARENA_WORDS`] so that `u32::MAX` remains reserved as the
/// "dead" sentinel used by the clause-relocation remap table.
pub mod arena_limits {
    /// `u32` header words stored before the literals of each clause in the arena.
    /// Mirrors `clause_arena::HEADER_WORDS`.
    pub const HEADER_WORDS: u64 = 3;

    /// Maximum number of `u32` words the clause arena can address soundly.
    ///
    /// The binary flag now lives at bit 32 of the `u64` watch clause word, so any
    /// `u32` word offset is representable without aliasing the flag. The only
    /// remaining reservation is `u32::MAX`, which the arena-compaction remap
    /// table uses as its "dead clause" sentinel (`watched::remap_clause_refs`).
    /// Keeping the arena strictly below this bound guarantees no live clause is
    /// ever allocated at offset `u32::MAX`, so a clause must fit entirely below
    /// it and the whole arena must stay strictly under this value.
    pub const MAX_ARENA_WORDS: u64 = u32::MAX as u64;

    /// Arena words consumed by a single clause with `num_literals` literals.
    #[must_use]
    pub const fn clause_words(num_literals: u64) -> u64 {
        HEADER_WORDS + num_literals
    }
}

pub(crate) mod adaptive;
pub(crate) mod alethe_export;
pub(crate) mod cube_and_conquer;
pub(crate) mod features;
pub(crate) mod flip;
pub mod fmla_guarded_equiv_scout;
pub mod fmla_ledger_preview;
pub mod fmla_runtime_ledger;
pub(crate) mod forward_checker;
pub(crate) mod gates;
#[cfg(feature = "gpu")]
pub(crate) mod gpu;
pub mod guard_cover_sidecar;
pub mod guidance;
pub(crate) mod htr;
/// Structured JSONL progress observer for `--progress-json` output.
pub mod json_observer;
pub(crate) mod kani_compat;
pub(crate) mod kitten;
pub(crate) mod lean_export;
pub(crate) mod lit_marks;
pub(crate) mod literal;
#[cfg(any(debug_assertions, test))]
pub(crate) mod lrat_checker;
pub(crate) mod mab;
/// Programmatic progress callback trait for AI consumers.
pub mod observer;
pub(crate) mod occ_list;
pub(crate) mod portfolio;
pub(crate) mod preprocess_transaction;
pub(crate) mod probe;
pub(crate) mod proof;
pub(crate) mod proof_capability;
pub mod proof_certificate;
pub(crate) mod proof_manager;
pub(crate) mod reconstruct;
pub(crate) mod replay_trace;
pub mod resolution_dag;
mod resolution_validate;
pub mod sat_proof_manager;
pub(crate) mod sbva;
pub(crate) mod solver;
pub(crate) mod solver_log;
pub(crate) mod subsume;
pub(crate) mod sweep;
pub(crate) mod symmetry;
pub mod technique;
#[cfg(any(test, kani))]
pub(crate) mod test_util;
pub(crate) mod tla_trace;
pub(crate) mod tla_traceable;
pub(crate) mod transred;
/// Route-b in-memory UNSAT certificate API (Program CK1 WS1-M1): solve a
/// caller-supplied CNF and surface the solver's own validated LRAT/RUP
/// refutation, in memory, for cross-blaster certificate consumers (external-codegen).
#[cfg(feature = "unsat-cert")]
pub mod unsat_cert;
mod variant;
pub(crate) mod vivify;
pub(crate) mod vsids;
pub(crate) mod walk;
pub(crate) mod warmup;
pub(crate) mod watched;

/// Snapshot of SAT solver feature toggles relevant to inprocessing soundness gates.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[non_exhaustive]
pub struct InprocessingFeatureProfile {
    /// Initial preprocess pipeline toggle.
    pub preprocess: bool,
    /// Walk-based phase initialization toggle.
    pub walk: bool,
    /// Warmup-based phase initialization toggle.
    pub warmup: bool,
    /// Conflict-clause shrink toggle.
    pub shrink: bool,
    /// Hyper-binary resolution within probing toggle.
    pub hbr: bool,
    /// Vivification toggle.
    pub vivify: bool,
    /// Subsumption toggle.
    pub subsume: bool,
    /// Failed-literal probing toggle.
    pub probe: bool,
    /// Bounded variable elimination toggle.
    pub bve: bool,
    /// Blocked clause elimination toggle.
    pub bce: bool,
    /// Conditioning toggle.
    pub condition: bool,
    /// SCC decomposition toggle.
    pub decompose: bool,
    /// Factorization toggle.
    pub factor: bool,
    /// Structured bounded variable addition toggle.
    pub sbva: bool,
    /// Transitive reduction toggle.
    pub transred: bool,
    /// Hyper-ternary resolution toggle.
    pub htr: bool,
    /// Gate extraction toggle.
    pub gate: bool,
    /// Congruence-closure toggle.
    pub congruence: bool,
    /// SAT sweeping toggle.
    pub sweep: bool,
    /// Backbone literal computation toggle.
    pub backbone: bool,
    /// Root-only symmetry preprocessing toggle.
    pub symmetry: bool,
    /// Kissat-style clause-weighted VMTF queue reorder toggle.
    pub reorder: bool,
    /// Covered clause elimination (ACCE) toggle.
    /// CaDiCaL defaults `cover=0` (OFF). CCE strictly subsumes BCE and shares
    /// the same O(clauses * max_occ) overhead per call.
    pub cce: bool,
}

impl Default for InprocessingFeatureProfile {
    fn default() -> Self {
        Self {
            preprocess: true,
            walk: true,
            warmup: true,
            shrink: true,
            hbr: true,
            vivify: true,
            subsume: true,
            probe: true,
            bve: false,
            bce: false,
            condition: false,
            decompose: false,
            factor: true,
            sbva: true,
            transred: true,
            htr: true,
            gate: true,
            congruence: false,
            sweep: true,
            backbone: true,
            symmetry: false,
            reorder: true,
            cce: false,
        }
    }
}

// -- Public API: types used by downstream crates and integration tests --
pub use adaptive::adjust_features_for_instance;
pub use clause_provenance::{ClauseProvenance, CoreProvenanceSummary};
pub use clause_trace::{ClauseTrace, ClauseTraceEntry, HintOmission, HintOmissionStats};
pub use cube_and_conquer::CubeAndConquerSolver;
pub use decision_trace::{
    decision_trace_suppressed_after_public_mismatch, finish_reserved_decision_trace,
    finish_reserved_decision_trace_retained, invalidate_reserved_decision_trace,
    reserve_decision_trace, suppress_decision_trace_after_public_mismatch, write_minimal_trace,
    write_minimal_trace_to, SettledDecisionTrace, TraceOutcome,
};
pub use dimacs::{parse_str as parse_dimacs, DimacsError, DimacsFormula};
pub use er_proof::{ErDefinition, ErObligationKind, ErProducer, ErProofLog};
pub use extension::{
    ExtCheckResult, ExtPropagateResult, Extension, PreparedExtension, SolverContext,
};
pub use features::{InstanceClass, SatFeatureAccumulator, SatFeatures};
pub use guidance::{
    SatGuidanceFingerprint, SatGuidanceImportDecision, SatGuidanceImportLevel,
    SatGuidanceImportReason, SAT_GUIDANCE_V2_FORMAT,
};
pub use literal::{Literal, SignedClause, Variable};
pub use mab::{BranchHeuristic, BranchHeuristicStats, BranchSelectorMode};
pub use portfolio::PortfolioSolver;
pub use preprocess_transaction::PreprocessTransactionStats;
pub use proof::{DratWriter, LratWriter, ProofOutput, MAX_LRAT_ORIGINAL_CLAUSES};
pub use proof_certificate::{ProofCertificate, ProofStep};
pub use resolution_dag::{
    prove_unsat_resolution_dag, prove_unsat_resolution_dag_with_limits,
    solve_resolution_dag_with_limits, ResolutionDag, ResolutionDagError, ResolutionProofError,
    ResolutionProofLimits, ResolutionProofPhase, ResolutionProofResource, ResolutionSolveOutcome,
    RupStep,
};
pub use resolution_validate::{
    ResolutionDagValidateError, ResolutionValidationError, ResolutionValidationLimits,
    ResolutionValidationResource,
};
pub use solver::{
    AssumeResult, BcpLongScanStats, BcpSavedPosStats, DecomposeLratPreflightStats, FactorStats,
    LookaheadStats, LratMaterializationStats, RephaseAttributionStats, RestartAttributionStats,
    SatResult, SatUnknownReason, SetSolutionError, Solver, TheoryPropResult, VarAssignmentKind,
    VerifiedAssumeResult, VerifiedSatResult,
};
pub use symmetry::SymmetryReport;
pub use technique::SatTechnique;
pub use tla_trace::TlaTraceWriter;
pub use tla_traceable::TlaTraceable;
#[cfg(feature = "unsat-cert")]
pub use unsat_cert::{prove_cnf_unsat_dimacs, CnfCertError};
pub use variant::{
    SolverVariant, VariantBranchPolicy, VariantConfig, VariantHotPathConfig, VariantInput,
    VariantProfilePlan, VariantRestartPolicy, VariantRouteProfile, VariantStartupPolicy,
};
pub use watched::ClauseRef;

// Approximate-BCP filter bridge (issue #8789 Phase 2). The enum is part of
// the feature-gated public API so integration tests in the external `tests/`
// crate can assert counter movement and verdict values.
#[cfg(feature = "approx-bcp-filter")]
pub use solver::approx_bcp_bridge::ApproxBcpPrefilterVerdict;

// -- Inprocessing statistics types (consumed by integration tests and ay binary) --
pub use bce::BCEStats;
pub use bve::BVEStats;
pub use cce::CCEStats;
pub use component::ComponentStats;
pub use condition::ConditioningStats;
pub use congruence::CongruenceStats;
pub use decompose::DecomposeStats;
pub use gates::GateStats;
pub use htr::HTRStats;
pub use probe::ProbeStats;
pub use subsume::SubsumeStats;
pub use sweep::SweepStats;
pub use transred::TransRedStats;
pub use vivify::VivifyStats;
