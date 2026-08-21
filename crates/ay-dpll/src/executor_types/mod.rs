// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Type definitions for the SMT executor.
//!
//! This module contains error types, result types, and statistics structures
//! used by the [`Executor`](crate::Executor).

use ay_core::string_literal;
use ay_core::{VerificationBoundary, VerificationFailure};
use ay_frontend::ElaborateError;
use std::collections::BTreeMap;

use crate::DpllError;

/// Typed model validation error replacing the previous `String`-based contract.
///
/// The previous `ExecutorError::ModelValidation(String)` relied on substring
/// matching (`"could not be model-validated"`) to decide whether to degrade
/// SAT to Unknown or to surface a hard error. This enum makes that decision
/// compile-time checkable.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
#[non_exhaustive]
pub enum ModelValidationError {
    /// This layer could not prove the model satisfies the property.
    /// The caller should degrade SAT to Unknown.
    #[error("model validation incomplete: {0}")]
    Incomplete(VerificationFailure),
    /// A concrete contradiction was found — the model definitely violates
    /// the property. This is a hard error.
    #[error("model validation violated: {0}")]
    Violated(VerificationFailure),
}

impl ModelValidationError {
    /// Create an `Incomplete` error for a specific boundary.
    pub fn incomplete(boundary: VerificationBoundary, detail: impl Into<String>) -> Self {
        Self::Incomplete(VerificationFailure {
            boundary,
            detail: detail.into(),
        })
    }

    /// Create a `Violated` error for a specific boundary.
    pub fn violated(boundary: VerificationBoundary, detail: impl Into<String>) -> Self {
        Self::Violated(VerificationFailure {
            boundary,
            detail: detail.into(),
        })
    }

    /// Returns `true` if this is an `Incomplete` error (should degrade to Unknown).
    pub fn is_incomplete(&self) -> bool {
        matches!(self, Self::Incomplete(_))
    }

    /// Returns `true` if this is a `Violated` error (hard failure).
    pub fn is_violated(&self) -> bool {
        matches!(self, Self::Violated(_))
    }

    /// Returns the failure detail for either variant.
    pub fn failure(&self) -> &VerificationFailure {
        match self {
            Self::Incomplete(f) | Self::Violated(f) => f,
        }
    }

    /// Check if the human-readable detail string contains a substring.
    ///
    /// Convenience for test assertions migrating from the old `String`-based
    /// error contract. Prefer `is_incomplete()` / `is_violated()` for new
    /// code.
    pub fn contains(&self, needle: &str) -> bool {
        self.failure().detail.contains(needle)
    }
}

/// Error during SMT execution
#[derive(Debug, Clone, thiserror::Error)]
#[non_exhaustive]
pub enum ExecutorError {
    /// Elaboration error
    #[error("elaboration error: {0}")]
    Elaborate(#[from] ElaborateError),
    /// DPLL(T) solver error (theory-SAT mapping failure or unexpected result)
    #[error("DPLL solver error: {0}")]
    Dpll(#[from] DpllError),
    /// Unsupported logic
    #[error(
        "unsupported logic: {0}. Supported logics: \
        ALL, AUFDT, AUFDTLIA, AUFDTLIRA, AUFLIA, AUFLIRA, AUFLRA, \
        LIA, LIRA, LRA, NIA, NIRA, NRA, \
        QF_ABV, QF_AUFBV, QF_AUFLIA, QF_AUFLIRA, QF_AUFLRA, QF_AX, \
        QF_BV, QF_BVFP, QF_DT, QF_EIA, QF_FP, QF_LIA, QF_LIRA, QF_LRA, \
        QF_NIA, QF_NIRA, QF_NRA, QF_S, QF_SEQ, QF_SLIA, QF_SNIA, \
        QF_UF, QF_UFBV, QF_UFLIA, QF_UFLRA, QF_UFNIA, QF_UFNIRA, QF_UFNRA, \
        UF, UFDT, UFDTLIA, UFDTLIRA, UFDTLRA, UFDTNIA, UFDTNIRA, UFDTNRA, \
        UFLIA, UFLRA, UFNIA, UFNIRA, UFNRA, HORN"
    )]
    UnsupportedLogic(String),
    /// Unsupported optimization feature
    #[error("unsupported optimization: {0}")]
    UnsupportedOptimization(String),
    /// Model validation failed — typed contract replaces previous `String`.
    #[error("model validation failed: {0}")]
    ModelValidation(ModelValidationError),
    /// A requested solver/certificate artifact could not be produced faithfully.
    #[error("artifact export failed: {0}")]
    ArtifactExport(String),
}

/// Result type for executor operations
pub type Result<T> = std::result::Result<T, ExecutorError>;

/// Reason for an Unknown result from check-sat
///
/// When the solver returns Unknown, this enum provides structured information
/// about why satisfiability could not be determined. Modeled after CVC5's
/// `UnknownExplanation` enum.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub enum UnknownReason {
    /// Time limit exceeded
    Timeout,
    /// Resource limit exceeded
    ResourceLimit,
    /// Memory limit exceeded
    MemoryLimit,
    /// User or portfolio interrupted the solver
    Interrupted,
    /// Logic requires unimplemented features
    Incomplete,
    /// **A computed verdict was REFUTED by AY's own fail-closed checker.**
    ///
    /// This is categorically different from every other variant here. The rest
    /// mean "AY never reached an answer". This one means AY *did* reach `sat`
    /// or `unsat`, its own model evaluator or strict refutation checker refused
    /// to certify it, and `--self-check` therefore withheld it. Each occurrence
    /// is a LATENT WRONG ANSWER that default mode would have emitted.
    ///
    /// It exists because these were previously reported as [`Self::Incomplete`],
    /// making a caught soundness bug indistinguishable from an unsupported
    /// logic. A 2026-07-25 corpus run found 13 wrong answers that way — 12 UFBV
    /// wrong-SATs and one AUFLIA wrong-UNSAT — every one of which `--self-check`
    /// had already caught and reported as a bland "incomplete", so nobody
    /// noticed. Never fold this back into `Incomplete`.
    SelfCheckRejected,
    /// **A computed UNSAT was WITHHELD because its proof is not trust-free.**
    ///
    /// The soundness gate of #8759. Under strict proofs, an `unsat` is only
    /// admissible when the terminal derivation chain reaching the empty clause
    /// is independently checkable end to end. This reason means it was not:
    /// a `:rule trust`/`hole` step or trust-kind theory lemma is reachable from
    /// the empty clause, or an `assume` leaf on that path is not backed by the
    /// problem's provenance (a laundered free axiom), or the proof references
    /// sequence-theory content no external checker can parse. AY reached
    /// `unsat` and refused to stand behind it.
    ///
    /// This is NOT [`Self::Incomplete`]. `Incomplete` means a lane could not
    /// decide the problem — nothing was computed and nothing was withheld.
    /// This variant means a verdict WAS computed and a soundness gate took it
    /// away, which is the same class of fact as [`Self::SelfCheckRejected`] and
    /// carries the same warning: **never fold this back into `Incomplete`.**
    /// It was folded in once — ay 0.6 deleted this variant in 66538b006 and
    /// left the gate publishing the generic reason from the CLI driver only —
    /// and the result was that a withheld unsound UNSAT became byte-identical
    /// to an unsupported logic, with the distinction surviving nowhere but a
    /// free-form transcript string.
    ///
    /// It is also distinct from [`Self::SelfCheckRejected`]: that one is the
    /// mandatory certification funnel refuting a verdict it could not certify;
    /// this one is the strict-proof gate refusing a verdict that certified but
    /// whose presentation nobody else can check.
    ProofTrusted,
    /// E-matching round budget or per-round instantiation limit exhausted.
    /// The solver could not explore all possible instantiations within budget.
    QuantifierRoundLimit,
    /// Deferred quantifier instantiations remain that could invalidate the model.
    QuantifierDeferred,
    /// Triggerless quantifiers that neither E-matching nor CEGQI could handle.
    QuantifierUnhandled,
    /// CEGQI-specific incompleteness: mixed forall/exists, failed ground
    /// disambiguation, or incomplete witness/counterexample search.
    QuantifierCegqiIncomplete,
    /// E-matching processed an exists quantifier but added instances as
    /// conjunctive assertions. UNSAT from the conjunction is unreliable
    /// because exists only needs one witness (#3593).
    QuantifierEmatchingExistsIncomplete,
    /// Maximum split limit reached (theory solver)
    SplitLimit,
    /// Expression split needed but not yet implemented (#1915)
    ExpressionSplit,
    /// Unsupported feature encountered
    Unsupported,
    /// Unsupported arithmetic fragment, such as symbolic Int div/mod that was
    /// not eliminated into linear constraints.
    UnsupportedArithmetic,
    /// Unsupported mixed collection/datatype fragment, such as live sequence
    /// constraints combined with algebraic datatypes.
    UnsupportedMixedCollection,
    /// Internal executor error (e.g., model validation failure).
    /// Use `Solver::get_executor_error()` for the detail message.
    InternalError,
    /// No specific reason available
    Unknown,
}

/// Authoritative production origin for a public [`UnknownReason`].
///
/// This is deliberately a one-to-one taxonomy rather than a free-form label.
/// A producer publishes `Unknown` through an origin, and the origin determines
/// the reason.  That prevents a diagnostic or conformance hook from claiming a
/// reason that does not belong to the exercised production boundary.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum UnknownOrigin {
    /// The wall-clock solve deadline expired.
    SolveDeadline,
    /// The deterministic resource budget was exhausted.
    DeterministicResourceBudget,
    /// The configured memory budget was exhausted.
    MemoryBudget,
    /// The caller's interrupt flag was observed.
    InterruptFlag,
    /// A selected solver lane could not decide the input.
    IncompleteSolverLane,
    /// Mandatory verdict certification could not confirm the result.
    VerdictCertification,
    /// The strict-proof gate found the terminal derivation chain of a computed
    /// UNSAT was not trust-free, and withheld the verdict.
    TerminalTrust,
    /// The E-matching round budget was exhausted.
    EmatchingRoundBudget,
    /// Required quantifier instantiation was deferred.
    DeferredInstantiation,
    /// A quantifier shape has no complete handler.
    UnhandledQuantifier,
    /// CEGQI could not complete its refinement.
    CegqiRefinement,
    /// Existential E-matching could not complete.
    ExistentialEmatching,
    /// A theory split exhausted its budget.
    TheorySplitBudget,
    /// An expression could not be split soundly by the selected lane.
    UnsupportedExpressionSplit,
    /// The input uses an unsupported feature.
    UnsupportedFeature,
    /// The input uses an unsupported arithmetic fragment.
    UnsupportedArithmeticFragment,
    /// The input uses an unsupported mixed collection fragment.
    UnsupportedMixedCollection,
    /// The executor encountered an internal failure.
    ExecutorFailure,
    /// A legacy unknown path had no more specific origin.
    UntaggedSolverUnknown,
}

include!("unknown_origin_registry.rs");

impl UnknownReason {
    /// Closed registry of every currently public Unknown reason.
    ///
    /// The order is a stable, append-only evidence contract: downstream
    /// consumers may persist the associated [`code`](Self::code), but must not
    /// infer semantics from an array index. A new enum variant must be appended
    /// here and assigned a new, unique code.
    ///
    /// Every registered reason has the same public-result lifecycle. Installing
    /// an `Unknown` through
    /// [`Executor::replace_last_result_with_unknown`](crate::Executor::replace_last_result_with_unknown)
    /// retains only the `Unknown` decision and its reason:
    ///
    /// | Prior result artifact | After any registered `Unknown` |
    /// | --- | --- |
    /// | SAT model, SAT acceptance certificate, model-validation provenance | Revoked |
    /// | UNSAT proof, proof quality/provenance, LRAT/clause trace | Revoked |
    /// | Unsat assumptions, named core, core-name provenance | Revoked |
    /// | Optimization values, soft-cost witness, objective certificates | Revoked |
    /// | Solver configuration and reusable incremental search state | Retained (not a result artifact) |
    ///
    /// This uniform policy prevents the reason taxonomy from accidentally
    /// granting authority to stale artifacts from an earlier decision.
    pub const ALL: [Self; 19] = [
        Self::Timeout,
        Self::ResourceLimit,
        Self::MemoryLimit,
        Self::Interrupted,
        Self::Incomplete,
        Self::SelfCheckRejected,
        Self::QuantifierRoundLimit,
        Self::QuantifierDeferred,
        Self::QuantifierUnhandled,
        Self::QuantifierCegqiIncomplete,
        Self::QuantifierEmatchingExistsIncomplete,
        Self::SplitLimit,
        Self::ExpressionSplit,
        Self::Unsupported,
        Self::UnsupportedArithmetic,
        Self::UnsupportedMixedCollection,
        Self::InternalError,
        Self::Unknown,
        Self::ProofTrusted,
    ];

    /// The single production origin authorized to publish this reason.
    pub const fn origin(self) -> UnknownOrigin {
        match self {
            Self::Timeout => UnknownOrigin::SolveDeadline,
            Self::ResourceLimit => UnknownOrigin::DeterministicResourceBudget,
            Self::MemoryLimit => UnknownOrigin::MemoryBudget,
            Self::Interrupted => UnknownOrigin::InterruptFlag,
            Self::Incomplete => UnknownOrigin::IncompleteSolverLane,
            Self::SelfCheckRejected => UnknownOrigin::VerdictCertification,
            Self::ProofTrusted => UnknownOrigin::TerminalTrust,
            Self::QuantifierRoundLimit => UnknownOrigin::EmatchingRoundBudget,
            Self::QuantifierDeferred => UnknownOrigin::DeferredInstantiation,
            Self::QuantifierUnhandled => UnknownOrigin::UnhandledQuantifier,
            Self::QuantifierCegqiIncomplete => UnknownOrigin::CegqiRefinement,
            Self::QuantifierEmatchingExistsIncomplete => UnknownOrigin::ExistentialEmatching,
            Self::SplitLimit => UnknownOrigin::TheorySplitBudget,
            Self::ExpressionSplit => UnknownOrigin::UnsupportedExpressionSplit,
            Self::Unsupported => UnknownOrigin::UnsupportedFeature,
            Self::UnsupportedArithmetic => UnknownOrigin::UnsupportedArithmeticFragment,
            Self::UnsupportedMixedCollection => UnknownOrigin::UnsupportedMixedCollection,
            Self::InternalError => UnknownOrigin::ExecutorFailure,
            Self::Unknown => UnknownOrigin::UntaggedSolverUnknown,
        }
    }

    /// Stable snake_case machine code for evidence and routing consumers.
    ///
    /// This is intentionally separate from [`Display`](std::fmt::Display):
    /// `Display` preserves SMT-LIB-style text, while `code()` is the compact
    /// AY-owned value downstream tools should persist.
    pub fn code(&self) -> &'static str {
        match self {
            Self::Timeout => "timeout",
            Self::ResourceLimit => "resource_limit",
            Self::MemoryLimit => "memory_limit",
            Self::Interrupted => "interrupted",
            Self::Incomplete => "incomplete",
            Self::SelfCheckRejected => "self_check_rejected",
            Self::ProofTrusted => "proof_trusted",
            Self::QuantifierRoundLimit => "quantifier_round_limit",
            Self::QuantifierDeferred => "quantifier_deferred",
            Self::QuantifierUnhandled => "quantifier_unhandled",
            Self::QuantifierCegqiIncomplete => "quantifier_cegqi_incomplete",
            Self::QuantifierEmatchingExistsIncomplete => "quantifier_ematching_exists_incomplete",
            Self::SplitLimit => "split_limit",
            Self::ExpressionSplit => "expression_split",
            Self::Unsupported => "unsupported",
            Self::UnsupportedArithmetic => "unsupported_arithmetic",
            Self::UnsupportedMixedCollection => "unsupported_mixed_collection",
            Self::InternalError => "internal_error",
            Self::Unknown => "unknown",
        }
    }

    /// Short human-readable label for the stable machine [`code`](Self::code).
    pub fn name(&self) -> &'static str {
        match self {
            Self::Timeout => "Timeout",
            Self::ResourceLimit => "Resource limit",
            Self::MemoryLimit => "Memory limit",
            Self::Interrupted => "Interrupted",
            Self::Incomplete => "Incomplete",
            Self::SelfCheckRejected => "Self-check REJECTED a computed verdict",
            Self::ProofTrusted => "Strict proofs WITHHELD a trust-bearing UNSAT",
            Self::QuantifierRoundLimit => "Quantifier round limit",
            Self::QuantifierDeferred => "Quantifier deferred",
            Self::QuantifierUnhandled => "Quantifier unhandled",
            Self::QuantifierCegqiIncomplete => "Quantifier CEGQI incomplete",
            Self::QuantifierEmatchingExistsIncomplete => "Quantifier E-matching exists incomplete",
            Self::SplitLimit => "Split limit",
            Self::ExpressionSplit => "Expression split",
            Self::Unsupported => "Unsupported",
            Self::UnsupportedArithmetic => "Unsupported arithmetic",
            Self::UnsupportedMixedCollection => "Unsupported mixed collection",
            Self::InternalError => "Internal error",
            Self::Unknown => "Unknown",
        }
    }

    /// Returns `true` if this reason is any quantifier-related incompleteness.
    pub fn is_quantifier(&self) -> bool {
        matches!(
            self,
            Self::QuantifierRoundLimit
                | Self::QuantifierDeferred
                | Self::QuantifierUnhandled
                | Self::QuantifierCegqiIncomplete
                | Self::QuantifierEmatchingExistsIncomplete
        )
    }
}

impl std::fmt::Display for UnknownReason {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // Use lowercase symbols matching SMT-LIB convention (cvc5/yices2 style)
        match self {
            Self::Timeout => write!(f, "timeout"),
            Self::ResourceLimit => write!(f, "resourceout"),
            Self::MemoryLimit => write!(f, "memout"),
            Self::Interrupted => write!(f, "interrupted"),
            Self::Incomplete => write!(f, "incomplete"),
            // NOT plain "incomplete": this one means a computed verdict was
            // refuted by AY's own checker, i.e. a caught wrong answer. It must
            // be greppable and must never be mistaken for an unsupported logic.
            Self::SelfCheckRejected => write!(f, "(incomplete self-check-rejected)"),
            // NOT plain "incomplete", for the same reason as the line above: a
            // withheld trust-bearing UNSAT is a caught soundness hazard, not an
            // undecided problem. This is the exact text the `ay` CLI has always
            // printed for `--strict-proofs`, so the typed reason and the
            // transcript string now agree by construction rather than by
            // coincidence.
            Self::ProofTrusted => write!(f, "(incomplete proof-trusted)"),
            Self::QuantifierRoundLimit => write!(f, "(incomplete quantifier-round-limit)"),
            Self::QuantifierDeferred => write!(f, "(incomplete quantifier-deferred)"),
            Self::QuantifierUnhandled => write!(f, "(incomplete quantifier-unhandled)"),
            Self::QuantifierCegqiIncomplete => write!(f, "(incomplete quantifier-cegqi)"),
            Self::QuantifierEmatchingExistsIncomplete => {
                write!(f, "(incomplete quantifier-ematching-exists)")
            }
            Self::SplitLimit => write!(f, "incomplete"),
            Self::ExpressionSplit => write!(f, "incomplete"),
            Self::Unsupported => write!(f, "unsupported"),
            Self::UnsupportedArithmetic => write!(f, "(unsupported arithmetic)"),
            Self::UnsupportedMixedCollection => write!(f, "(unsupported mixed-collection)"),
            Self::InternalError => write!(f, "internal-error"),
            Self::Unknown => write!(f, "unknown"),
        }
    }
}

/// Value type for extensible statistics
#[derive(Debug, Clone, PartialEq)]
#[non_exhaustive]
pub enum StatValue {
    /// Integer count
    Int(u64),
    /// Floating point value (e.g., time in seconds)
    Float(f64),
    /// String value (e.g., labels)
    String(String),
}

impl std::fmt::Display for StatValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Int(v) => write!(f, "{v}"),
            Self::Float(v) => write!(f, "{v:.2}"),
            Self::String(v) => write!(f, "{}", string_literal(v)),
        }
    }
}

/// Solver statistics from the last check-sat call
///
/// Provides performance metrics for debugging and analysis.
/// Modeled after Z3's `Z3_solver_get_statistics` and CVC5's `Solver::getStatistics()`.
#[derive(Debug, Clone, Default, PartialEq)]
#[non_exhaustive]
pub struct Statistics {
    // =========================================================================
    // SAT-level statistics
    // =========================================================================
    /// Number of conflicts encountered during solving
    pub conflicts: u64,
    /// Number of decisions made
    pub decisions: u64,
    /// Number of unit propagations
    pub propagations: u64,
    /// Number of restarts
    pub restarts: u64,
    /// Number of learned clauses currently retained
    pub learned_clauses: u64,
    /// Number of clauses deleted during clause management
    pub deleted_clauses: u64,

    // =========================================================================
    // Theory-level statistics
    // =========================================================================
    /// Number of theory conflicts (theory solver detected inconsistency)
    pub theory_conflicts: u64,
    /// Number of theory propagations
    pub theory_propagations: u64,

    // =========================================================================
    // Nelson-Oppen combination statistics (#8165)
    // =========================================================================
    /// Total Nelson-Oppen fixpoint iterations across all check calls
    pub nelson_oppen_rounds: u64,
    /// Maximum N-O fixpoint iterations in a single check call
    pub nelson_oppen_max_rounds: u64,
    /// Number of equalities propagated from arithmetic to EUF
    pub equalities_propagated_to_euf: u64,
    /// Number of equalities propagated from EUF to arithmetic
    pub equalities_propagated_to_arith: u64,

    // =========================================================================
    // Theory Unknown / partial clause statistics (#8165)
    // =========================================================================
    /// Total number of theory Unknown returns
    pub theory_unknown_count: u64,
    /// Total number of partial clause events (terms couldn't map to SAT literals)
    pub partial_clause_count: u64,

    // =========================================================================
    // Conflict quality statistics (#8165)
    // =========================================================================
    /// Maximum number of literals in any single theory conflict clause
    pub conflict_max_literals: u64,
    /// Sum of literals across all theory conflict clauses (for computing average)
    pub conflict_total_literals: u64,
    /// Number of literals removed by theory conflict minimization (#8424)
    pub theory_minimize_lits_removed: u64,

    // =========================================================================
    // Farkas verification statistics (#8165)
    // =========================================================================
    /// Number of Farkas certificate structural/semantic verification failures
    pub farkas_certificate_failures: u64,
    /// Number of Farkas certificate downgrades (conflict kept, certificate dropped)
    pub farkas_certificate_downgrades: u64,
    /// Number of semantic verifications skipped due to large term store budget (#8558).
    pub semantic_verify_budget_skips: u64,

    // =========================================================================
    // Model validation statistics (#8165)
    // =========================================================================
    /// Number of model validation skips (deferred or unsupported theories)
    pub model_validation_skips: u64,
    /// Number of model validation failures (incomplete or violated)
    pub model_validation_failures: u64,

    // =========================================================================
    // Proof / explainability statistics (#8153)
    // =========================================================================
    /// Number of proof clause steps (LRAT) in the last UNSAT proof certificate
    pub proof_clause_count: u64,
    /// Whether the proof certificate is complete (all antecedents resolved)
    pub proof_complete: bool,
    /// Number of entries in the annotated UNSAT core (if requested)
    pub annotated_core_entries: u64,
    /// Number of distinct theories involved in the annotated UNSAT core
    pub annotated_core_theories: u64,

    // =========================================================================
    // E-matching / quantifier instantiation statistics (#8614)
    // =========================================================================
    /// Number of E-matching rounds completed in the last check-sat.
    pub ematching_rounds_completed: u64,
    /// Number of quantifier instances created by E-matching.
    pub ematching_instances_created: u64,

    // =========================================================================
    // Resource consumption
    // =========================================================================
    /// Bytes consumed by the per-instance term store (hash-consed terms).
    pub term_bytes: u64,
    /// Number of interned terms in the term store.
    pub term_count: u64,
    /// Number of CEGQI/theory refinement rounds (quantifier or split loops).
    pub refinement_count: u64,
    /// Elapsed wall-clock time for the last check-sat call, in seconds.
    pub time_seconds: f64,
    /// RSS-derived process memory in MiB at the end of the last check-sat call.
    pub memory_mb: f64,
    /// Peak process memory use in MiB at the end of the last check-sat call.
    pub max_memory_mb: f64,
    /// Deterministic solver-work counter exposed under Z3's rlimit-count key.
    pub rlimit_count: u64,

    // =========================================================================
    // Problem size
    // =========================================================================
    /// Number of variables in the problem
    pub num_vars: u64,
    /// Number of clauses in the problem
    pub num_clauses: u64,
    /// Number of assertions
    pub num_assertions: u64,

    // =========================================================================
    // Extensible statistics
    // =========================================================================
    /// Additional statistics (for theory-specific or future metrics)
    pub extra: BTreeMap<String, StatValue>,
}

impl Statistics {
    /// Create an empty statistics object
    pub fn new() -> Self {
        Self::default()
    }

    /// Assert internal consistency invariants (debug builds only).
    ///
    /// Theory-level counters must be subsets of SAT-level counters:
    /// - theory_conflicts <= conflicts
    /// - theory_propagations <= propagations
    #[inline]
    pub(crate) fn debug_assert_consistency(&self) {
        debug_assert!(
            self.theory_conflicts <= self.conflicts,
            "BUG: theory_conflicts ({}) > conflicts ({})",
            self.theory_conflicts,
            self.conflicts,
        );
        debug_assert!(
            self.theory_propagations <= self.propagations,
            "BUG: theory_propagations ({}) > propagations ({})",
            self.theory_propagations,
            self.propagations,
        );
    }

    /// Get an integer statistic by name
    pub fn get_int(&self, name: &str) -> Option<u64> {
        match name {
            "conflicts" => Some(self.conflicts),
            "decisions" => Some(self.decisions),
            "propagations" => Some(self.propagations),
            "restarts" => Some(self.restarts),
            "learned_clauses" => Some(self.learned_clauses),
            "deleted_clauses" => Some(self.deleted_clauses),
            "theory_conflicts" => Some(self.theory_conflicts),
            "theory_propagations" => Some(self.theory_propagations),
            "nelson_oppen_rounds" => Some(self.nelson_oppen_rounds),
            "nelson_oppen_max_rounds" => Some(self.nelson_oppen_max_rounds),
            "equalities_propagated_to_euf" => Some(self.equalities_propagated_to_euf),
            "equalities_propagated_to_arith" => Some(self.equalities_propagated_to_arith),
            "theory_unknown_count" => Some(self.theory_unknown_count),
            "partial_clause_count" => Some(self.partial_clause_count),
            "conflict_max_literals" => Some(self.conflict_max_literals),
            "conflict_total_literals" => Some(self.conflict_total_literals),
            "theory_minimize_lits_removed" => Some(self.theory_minimize_lits_removed),
            "farkas_certificate_failures" => Some(self.farkas_certificate_failures),
            "farkas_certificate_downgrades" => Some(self.farkas_certificate_downgrades),
            "semantic_verify_budget_skips" => Some(self.semantic_verify_budget_skips),
            "model_validation_skips" => Some(self.model_validation_skips),
            "model_validation_failures" => Some(self.model_validation_failures),
            "proof_clause_count" => Some(self.proof_clause_count),
            "proof_complete" => Some(u64::from(self.proof_complete)),
            "annotated_core_entries" => Some(self.annotated_core_entries),
            "annotated_core_theories" => Some(self.annotated_core_theories),
            "ematching_rounds_completed" => Some(self.ematching_rounds_completed),
            "ematching_instances_created" => Some(self.ematching_instances_created),
            "term_bytes" => Some(self.term_bytes),
            "term_count" => Some(self.term_count),
            "refinement_count" => Some(self.refinement_count),
            "rlimit_count" | "rlimit-count" => Some(self.rlimit_count),
            "num_vars" => Some(self.num_vars),
            "num_clauses" => Some(self.num_clauses),
            "num_assertions" => Some(self.num_assertions),
            _ => self.extra.get(name).and_then(|v| {
                if let StatValue::Int(i) = v {
                    Some(*i)
                } else {
                    None
                }
            }),
        }
    }

    /// Set an extra integer statistic
    pub fn set_int(&mut self, name: &str, value: u64) {
        self.extra.insert(name.to_string(), StatValue::Int(value));
    }

    /// Set an extra float statistic
    pub fn set_float(&mut self, name: &str, value: f64) {
        self.extra.insert(name.to_string(), StatValue::Float(value));
    }

    /// Get an extra float statistic by name (inc-13 per-check phase attribution).
    pub fn get_float(&self, name: &str) -> Option<f64> {
        self.extra.get(name).and_then(|v| {
            if let StatValue::Float(f) = v {
                Some(*f)
            } else {
                None
            }
        })
    }

    /// Get a string statistic by name.
    pub fn get_string(&self, name: &str) -> Option<&str> {
        self.extra.get(name).and_then(|v| {
            if let StatValue::String(s) = v {
                Some(s.as_str())
            } else {
                None
            }
        })
    }

    /// Set an extra string statistic.
    pub fn set_string(&mut self, name: &str, value: impl Into<String>) {
        self.extra
            .insert(name.to_string(), StatValue::String(value.into()));
    }
}

impl std::fmt::Display for Statistics {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "(:statistics")?;
        writeln!(f, "  :conflicts {}", self.conflicts)?;
        writeln!(f, "  :decisions {}", self.decisions)?;
        writeln!(f, "  :propagations {}", self.propagations)?;
        writeln!(f, "  :restarts {}", self.restarts)?;
        writeln!(f, "  :learned-clauses {}", self.learned_clauses)?;
        writeln!(f, "  :deleted-clauses {}", self.deleted_clauses)?;
        writeln!(f, "  :theory-conflicts {}", self.theory_conflicts)?;
        writeln!(f, "  :theory-propagations {}", self.theory_propagations)?;
        writeln!(f, "  :nelson-oppen-rounds {}", self.nelson_oppen_rounds)?;
        writeln!(
            f,
            "  :nelson-oppen-max-rounds {}",
            self.nelson_oppen_max_rounds
        )?;
        writeln!(
            f,
            "  :equalities-propagated-to-euf {}",
            self.equalities_propagated_to_euf
        )?;
        writeln!(
            f,
            "  :equalities-propagated-to-arith {}",
            self.equalities_propagated_to_arith
        )?;
        writeln!(f, "  :theory-unknown-count {}", self.theory_unknown_count)?;
        writeln!(f, "  :partial-clause-count {}", self.partial_clause_count)?;
        writeln!(f, "  :conflict-max-literals {}", self.conflict_max_literals)?;
        writeln!(
            f,
            "  :conflict-total-literals {}",
            self.conflict_total_literals
        )?;
        writeln!(
            f,
            "  :theory-minimize-lits-removed {}",
            self.theory_minimize_lits_removed
        )?;
        writeln!(
            f,
            "  :farkas-certificate-failures {}",
            self.farkas_certificate_failures
        )?;
        writeln!(
            f,
            "  :farkas-certificate-downgrades {}",
            self.farkas_certificate_downgrades
        )?;
        if self.semantic_verify_budget_skips > 0 {
            writeln!(
                f,
                "  :semantic-verify-budget-skips {}",
                self.semantic_verify_budget_skips
            )?;
        }
        writeln!(
            f,
            "  :model-validation-skips {}",
            self.model_validation_skips
        )?;
        writeln!(
            f,
            "  :model-validation-failures {}",
            self.model_validation_failures
        )?;
        if self.proof_clause_count > 0 {
            writeln!(f, "  :proof-clause-count {}", self.proof_clause_count)?;
            writeln!(f, "  :proof-complete {}", self.proof_complete)?;
        }
        if self.annotated_core_entries > 0 {
            writeln!(
                f,
                "  :annotated-core-entries {}",
                self.annotated_core_entries
            )?;
            writeln!(
                f,
                "  :annotated-core-theories {}",
                self.annotated_core_theories
            )?;
        }
        if self.ematching_rounds_completed > 0 {
            writeln!(
                f,
                "  :ematching-rounds-completed {}",
                self.ematching_rounds_completed
            )?;
            writeln!(
                f,
                "  :ematching-instances-created {}",
                self.ematching_instances_created
            )?;
        }
        if self.term_bytes > 0 {
            writeln!(f, "  :term-bytes {}", self.term_bytes)?;
            writeln!(f, "  :term-count {}", self.term_count)?;
        }
        if self.refinement_count > 0 {
            writeln!(f, "  :refinement-count {}", self.refinement_count)?;
        }
        writeln!(f, "  :max-memory {:.2}", self.max_memory_mb)?;
        writeln!(f, "  :memory {:.2}", self.memory_mb)?;
        writeln!(f, "  :rlimit-count {}", self.rlimit_count)?;
        writeln!(f, "  :time {:.2}", self.time_seconds)?;
        writeln!(f, "  :num-vars {}", self.num_vars)?;
        writeln!(f, "  :num-clauses {}", self.num_clauses)?;
        writeln!(f, "  :num-assertions {}", self.num_assertions)?;
        for (name, value) in &self.extra {
            writeln!(f, "  :{name} {value}")?;
        }
        write!(f, ")")
    }
}

// Re-export SolveResult and SmtProofCertificate from the API types for backward compatibility.
// Previously this module defined its own `CheckSatResult` with identical variants.
pub(crate) use crate::api::types::SolveResult;

#[cfg(test)]
mod tests;
